(**************************************************************************)
(*                                                                        *)
(*  This file is part of the Frama-C's E-ACSL plug-in.                    *)
(*                                                                        *)
(*  Copyright (C) 2012-2016                                               *)
(*    CEA (Commissariat à l'énergie atomique et aux énergies              *)
(*         alternatives)                                                  *)
(*                                                                        *)
(*  you can redistribute it and/or modify it under the terms of the GNU   *)
(*  Lesser General Public License as published by the Free Software       *)
(*  Foundation, version 2.1.                                              *)
(*                                                                        *)
(*  It is distributed in the hope that it will be useful,                 *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(*  GNU Lesser General Public License for more details.                   *)
(*                                                                        *)
(*  See the GNU Lesser General Public License version 2.1                 *)
(*  for more details (enclosed in the file license/LGPLv2.1).             *)
(*                                                                        *)
(**************************************************************************)

open Cil_types
open Cil_datatype

(* ************************************************************************** *)
(** {2 Handling the E-ACSL's C-libraries, part I} *)
(* ************************************************************************** *)

let library_files () =
  List.map
    (fun d -> Options.Share.file ~error:true d)
    [ "e_acsl.h";
      "e_acsl_gmp_types.h";
      "e_acsl_gmp.h";
      "memory_model/e_acsl_mmodel_api.h";
      "memory_model/e_acsl_bittree.h";
      "memory_model/e_acsl_mmodel.h" ]

let normalized_library_files = 
  lazy (List.map Filepath.normalize (library_files ()))

let is_library_loc (loc, _) = 
  List.mem loc.Lexing.pos_fname (Lazy.force normalized_library_files)

let library_functions = Datatype.String.Hashtbl.create 17
let register_library_function vi = 
  Datatype.String.Hashtbl.add library_functions vi.vname vi

let reset () = Datatype.String.Hashtbl.clear library_functions

(* ************************************************************************** *)
(** {2 Builders} *)
(* ************************************************************************** *)

exception Unregistered_library_function of string
let mk_call ~loc ?result fname args =
  let vi =  
    try Datatype.String.Hashtbl.find library_functions fname
    with Not_found ->
      (* could not happen in normal mode, but coud be raised when E-ACSL is used
         as a library *)
      raise (Unregistered_library_function fname)
  in
  let f = Cil.evar ~loc vi in
  vi.vreferenced <- true;
  let ty_params = match vi.vtype with
    | TFun(_, Some l, _, _) -> l
    | _ -> assert false
  in
  let args =
    List.map2
      (fun (_, ty, _) arg -> 
	let e =
	  match ty, Cil.unrollType (Cil.typeOf arg), arg.enode with
	  | TPtr _, TArray _, Lval lv -> Cil.new_exp ~loc (StartOf lv)
	  | TPtr _, TArray _, _ -> assert false
	  | _, _, _ -> arg
	in
	Cil.mkCast ~force:false ~newt:ty ~e)
      ty_params
      args
  in
  Cil.mkStmtOneInstr ~valid_sid:true (Call(result, f, args, loc))

type annotation_kind = 
  | Assertion
  | Precondition
  | Postcondition
  | Invariant
  | RTE

let kind_to_string loc k = 
  Cil.mkString 
    ~loc
    (match k with
    | Assertion -> "Assertion"
    | Precondition -> "Precondition"
    | Postcondition -> "Postcondition"
    | Invariant -> "Invariant"
    | RTE -> "RTE")

let is_generated_varinfo vi =
  let name = vi.vname in
     name.[0] = '_'
     && name.[1] = '_'
     && name.[2] = 'e'
     && name.[3] = '_'
     && name.[4] = 'a'
     && name.[5] = 'c'
     && name.[6] = 's'
     && name.[7] = 'l'
     && name.[8] = '_'

let is_generated_kf kf =
  let name = Kernel_function.get_vi kf in
  is_generated_varinfo name

let get_orig_name kf =
  let name = Kernel_function.get_name kf in
  let str = Str.regexp "__e_acsl_\\(.*\\)" in
  if Str.string_match str name 0 then
    try Str.matched_group 1 name with Not_found -> assert false
  else
    name

let e_acsl_guard_name = "e_acsl_assert"

(* Build a C conditional doing a runtime assertion check. *)
let mk_e_acsl_guard ?(reverse=false) kind kf e p =
  let loc = p.loc in
  let msg = 
    Kernel.Unicode.without_unicode
      (Pretty_utils.sfprintf "%a@?" Printer.pp_predicate_named) p 
  in
  let line = (fst loc).Lexing.pos_lnum in
  let e = 
    if reverse then e else Cil.new_exp ~loc:e.eloc (UnOp(LNot, e, Cil.intType)) 
  in
  mk_call 
    ~loc 
    e_acsl_guard_name
    [ e; 
      kind_to_string loc kind; 
      Cil.mkString ~loc (get_orig_name kf); 
      Cil.mkString ~loc msg; 
      Cil.integer loc line ] 

let mk_block prj stmt b = 
  let mk b = match b.bstmts with
    | [] -> 
      (match stmt.skind with
      | Instr(Skip _) -> stmt
      | _ -> assert false)
    | [ s ] -> 
      if Stmt.equal stmt s then s 
      else 
	(* [JS 2012/10/19] this case exactly corresponds to
	   e_acsl_assert(...) when the annotation is associated to a
	   statement <skip>. Creating a block prevents the printer to add
	   a stupid unintuitive block *)
	Cil.mkStmt ~valid_sid:true (Block b)
    |  _ :: _ -> Cil.mkStmt ~valid_sid:true (Block b)
  in	    
  Project.on prj mk b

(* ************************************************************************** *)
(** {2 Handling \result} *)
(* ************************************************************************** *)

let result_lhost kf =
  let stmt = 
    try Kernel_function.find_return kf 
    with Kernel_function.No_Statement -> assert false
  in
  match stmt.skind with
  | Return(Some { enode = Lval (lhost, NoOffset) }, _) -> lhost
  | _ -> assert false

let result_vi kf = match result_lhost kf with
  | Var vi -> vi
  | Mem _ -> assert false

(* ************************************************************************** *)
(** {2 Handling the E-ACSL's C-libraries, part II} *)
(* ************************************************************************** *)

let mk_debug_mmodel_stmt stmt =
  if Options.debug_atleast 1
    && Options.is_debug_key_enabled Options.dkey_analysis 
  then
    let debug = mk_call ~loc:(Stmt.loc stmt) "__e_acsl_memory_debug" [] in
    Cil.mkStmt ~valid_sid:true (Block (Cil.mkBlock [ stmt; debug]))
  else 
    stmt

let mk_full_init_stmt ?(addr=true) vi =
  let loc = vi.vdecl in
  let stmt = match addr, Cil.unrollType vi.vtype with
    | _, TArray(_,Some _, _, _) | false, _ ->
      mk_call ~loc "__full_init" [ Cil.evar ~loc vi ]
    | _ -> mk_call ~loc "__full_init" [ Cil.mkAddrOfVi vi ]
  in
  mk_debug_mmodel_stmt stmt

let mk_initialize ~loc (host, offset as lv) = match host, offset with
  | Var _, NoOffset -> mk_call ~loc "__full_init" [ Cil.mkAddrOf ~loc lv ]
  | _ -> 
    let typ = Cil.typeOfLval lv in
    mk_call ~loc 
      "__initialize" 
      [ Cil.mkAddrOf ~loc lv; Cil.new_exp loc (SizeOf typ) ]

let mk_store_stmt ?str_size vi =
  let ty = Cil.unrollType vi.vtype in
  let loc = vi.vdecl in
  let store = mk_call ~loc "__store_block" in
  let stmt = match ty, str_size with
    | TArray(_, Some _,_,_), None -> 
      store [ Cil.evar ~loc vi ; Cil.sizeOf ~loc ty ]
    | TPtr(TInt(IChar, _), _), Some size -> store [ Cil.evar ~loc vi ; size ]
    | _, None -> store [ Cil.mkAddrOfVi vi ; Cil.sizeOf ~loc ty ]
    | _, Some _ -> assert false
  in
  mk_debug_mmodel_stmt stmt

let mk_delete_stmt vi =
  let loc = vi.vdecl in
  let stmt = match Cil.unrollType vi.vtype with
    | TArray(_, Some _, _, _) ->
      mk_call ~loc "__delete_block" [ Cil.evar ~loc vi ]
      (*      | Tarray(_, None, _, _)*)
    | _ -> mk_call ~loc "__delete_block" [ Cil.mkAddrOfVi vi ] 
  in
  mk_debug_mmodel_stmt stmt

let mk_literal_string vi =
  let loc = vi.vdecl in
  let stmt = mk_call ~loc "__literal_string" [ Cil.evar ~loc vi ] in
  mk_debug_mmodel_stmt stmt

(* ************************************************************************** *)
(** {2 Other stuff} *)
(* ************************************************************************** *)

let term_addr_of ~loc tlv ty =
  Logic_const.taddrof ~loc tlv (Ctype (TPtr(ty, [])))

(*
Local Variables:
compile-command: "make"
End:
*)
