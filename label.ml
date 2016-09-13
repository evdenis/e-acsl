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

(* The keys are the stmts which were previously labeled, whereas the associated
   values are the new stmts containing the same labels. *)
module Labeled_stmts =
  Cil_state_builder.Stmt_hashtbl
    (Cil_datatype.Stmt)
    (struct
      let size = 7
      let dependencies = [] (* delayed *)
      let name = "E-ACSL.Labels"
     end)

let self = Labeled_stmts.self

let new_labeled_stmt stmt = try Labeled_stmts.find stmt with Not_found -> stmt

let move (vis:Visitor.generic_frama_c_visitor) ~old new_stmt =
  let labels = old.labels in
  match labels with
  | [] -> ()
  | _ :: _ ->
    old.labels <- [];
    new_stmt.labels <- labels @ new_stmt.labels;
    Labeled_stmts.add old new_stmt;
    (* update the gotos of the function jumping to one of the labels *)
    let o = object
      inherit Visitor.frama_c_inplace
      method !vstmt_aux s = match s.skind with
      | Goto(s_ref, _) ->
        if Cil_datatype.Stmt.equal !s_ref old then s_ref := new_stmt;
        Cil.SkipChildren
      | _ -> Cil.DoChildren
      (* improve efficiency: skip childrens which cannot contain any label *)
      method !vinst _ = Cil.SkipChildren
      method !vexpr _ = Cil.SkipChildren
      method !vlval _ = Cil.SkipChildren
    end in
    let f = Extlib.the vis#current_func in
    let mv_labels s =
      ignore (Visitor.visitFramacStmt o (Cil.memo_stmt vis#behavior s))
    in
    List.iter mv_labels f.sallstmts

let get_stmt vis = function
  | StmtLabel { contents = stmt } -> stmt
  | LogicLabel(_, label) when label = "Here" ->
    (match vis#current_stmt with
    | None -> Error.not_yet "label \"Here\" in function contract"
    | Some s -> s)
  | LogicLabel(_, label) when label = "Old" || label = "Pre" ->
    (try Kernel_function.find_first_stmt (Extlib.the vis#current_kf)
     with Kernel_function.No_Statement -> assert false)
  | LogicLabel(_, label) when label = "Post" ->
    (try Kernel_function.find_return (Extlib.the vis#current_kf)
     with Kernel_function.No_Statement -> assert false)
  | LogicLabel(_, _label) -> assert false

(*
Local Variables:
compile-command: "make"
End:
*)
