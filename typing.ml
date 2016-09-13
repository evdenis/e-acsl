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

let dkey = Options.dkey_typing

module Z = Integer

let is_representable n k = 
  if Options.Gmp_only.get () then
    match k with
    | IBool | IChar | ISChar | IUChar | IInt | IUInt | IShort | IUShort 
    | ILong | IULong ->
      true
    | ILongLong | IULongLong ->
      (* no GMP initializer from a long long *)
      false
  else
    Z.ge n Z.min_int64 && Z.le n Z.max_int64

(******************************************************************************)
(** Type Definitions: Intervals *)
(******************************************************************************)

type eacsl_typ =
  | Interv of Z.t * Z.t
  | Z
  | No_integral of logic_type

(* debugging purpose only *)
let pretty_eacsl_typ fmt = function
  | Interv(l, u) -> 
    Format.fprintf fmt "[ %a; %a ]" 
      (fun z -> Z.pretty z) l 
      (fun z -> Z.pretty z) u
  | Z -> Format.fprintf fmt "Z"
  | No_integral lty -> Format.fprintf fmt "%a" Printer.pp_logic_type lty

let ikind_of_integer i unsigned = 
  (* int whenever possible to prevent superfluous casts in the generated code *)
  if Cil.fitsInInt IInt i then IInt else Cil.intKindForValue i unsigned

let typ_of_eacsl_typ = function
  | Interv(l, u) -> 
    let is_pos = Z.ge l Z.zero in
    (try 
       let ty_l = TInt(ikind_of_integer l is_pos, []) in
       let ty_u = TInt(ikind_of_integer u is_pos, []) in
       Cil.arithmeticConversion ty_l ty_u
     with Cil.Not_representable -> 
       Mpz.t ())
  | Z -> Mpz.t ()
  | No_integral (Ctype ty) -> ty
  | No_integral ty when Logic_const.is_boolean_type ty -> assert false
  | No_integral (Ltype _) -> Error.not_yet "typing of user-defined logic type"
  | No_integral (Lvar _) -> Error.not_yet "type variable"
  | No_integral Linteger -> Mpz.t ()
  | No_integral Lreal -> TFloat(FLongDouble, [])
  | No_integral (Larrow _) -> Error.not_yet "functional type"

let eacsl_typ_of_typ ty = 
  match Cil.unrollType ty with
  | TInt(k, _) as ty -> 
    let n = Cil.bitsSizeOf ty in
    let l, u = 
      if Cil.isSigned k then Cil.min_signed_number n, Cil.max_signed_number n
      else Z.zero, Cil.max_unsigned_number n
    in
    Interv(l, u)
  | ty when Mpz.is_t ty -> Z
  | ty -> No_integral (Ctype ty)

exception Cannot_compare
let meet ty1 ty2 = match ty1, ty2 with
  | Interv(l1, u1), Interv(l2, u2) -> 
    let l = Z.max l1 l2 in
    let u = Z.min u1 u2 in
    if Z.gt l u then raise Cannot_compare;
    Interv(l, u)
  | Interv _, Z -> ty1
  | Z, Interv _ -> ty2
  | Z, Z -> Z
  | No_integral t1, No_integral t2 when Logic_type.equal t1 t2 -> ty1
  | No_integral _, No_integral _
  | (Z | Interv _), No_integral _
  | No_integral _, (Z | Interv _) -> raise Cannot_compare

let join ty1 ty2 = match ty1, ty2 with
  | Interv(l1, u1), Interv(l2, u2) -> Interv(Z.min l1 l2, Z.max u1 u2)
  | Interv _, Z | Z, Interv _ | Z, Z -> Z
  | No_integral t1, No_integral t2 when Logic_type.equal t1 t2 -> ty1
  | No_integral t, ty | ty, No_integral t when Cil.isLogicRealType t -> ty
  | No_integral t, _ when Cil.isLogicFloatType t -> ty1
  | (Z | Interv _), (No_integral _ as ty)
  | (No_integral _ as ty), (Interv _ | Z) -> 
    ty
  | No_integral _, No_integral _ ->
    Options.fatal "cannot join %a and %a" 
      pretty_eacsl_typ ty1 
      pretty_eacsl_typ ty2

let int_to_interv n = 
  let b = Z.of_int n in
  Interv (b, b)

(******************************************************************************)
(** Environments *)
(******************************************************************************)

module type Typing_env = sig
  type key
  type data
  val add: key -> data -> unit
  val find: key -> data
  val mem: key -> bool
  val clear: unit -> unit
end

module Make_env
  (Key: sig type t val hash: t -> int end) 
  (Data: sig type t end):
  Typing_env with type key = Key.t and type data = Data.t = 
struct

  type key = Key.t
  type data = Data.t

  module H = 
    Hashtbl.Make(struct include Key let equal (t1:key) t2 = t1 == t2 end)

  let tbl = H.create 17
  let add = H.replace tbl
  let find = H.find tbl
  let mem = H.mem tbl
  let clear () = H.clear tbl

end

module Term_env = Make_env(Term)(struct type t = eacsl_typ * eacsl_typ end)
module Logic_var_env = Make_env(Logic_var)(struct type t = eacsl_typ end)

let generic_typ (which: < f: 'a. 'a * 'a -> 'a >) t =
  Cil.CurrentLoc.set t.term_loc;
    if Options.Gmp_only.get () then 
      let ty = match t.term_type with
	| Linteger -> Mpz.t ()
	| Ctype ty when Cil.isIntegralType ty -> Mpz.t ()
	| Ctype ty -> ty
	| Ltype _ as ty when Logic_const.is_boolean_type ty -> Mpz.t ()
	| Ltype _ -> Error.not_yet "typing of user-defined logic type"
	| Lvar _ -> Error.not_yet "type variable"
	| Lreal -> TFloat(FLongDouble, [])
	| Larrow _ -> Error.not_yet "functional type"
      in
      which#f (ty, ty)
    else
      try 
	let typs = Term_env.find t in
	typ_of_eacsl_typ (which#f typs)
      with Not_found -> 
	Options.fatal "untyped term %a" Term.pretty t

let typ_of_term = generic_typ (object method f: 'a. 'a * 'a -> 'a = fst end)
let typ_of_term_operation = 
  generic_typ (object method f: 'a. 'a * 'a -> 'a = snd end)

let unsafe_set_term t ty =
  if not (Options.Gmp_only.get ()) then begin
    assert (not (Term_env.mem t));
    let ty = eacsl_typ_of_typ ty in
    Term_env.add t (ty, ty)
  end

let unsafe_unify ~from logic_v =
  try
    let ty = Logic_var_env.find from in
    assert (not (Logic_var_env.mem logic_v));
    Logic_var_env.add logic_v ty
  with Not_found ->
    Options.fatal "unknown logic variable %a" Printer.pp_logic_var logic_v

let clear () = 
  Options.feedback ~dkey ~level:2 "clearing environment.";
  Term_env.clear (); 
  Logic_var_env.clear ()

(******************************************************************************)
(** Typing rules *)
(******************************************************************************)

let type_constant ty = function
  | Integer(n, _) -> 
    if Cil.fitsInInt ILongLong n || Cil.fitsInInt IULongLong n then Interv(n, n)
    else Z
  | LChr c -> 
    let n = Cil.charConstToInt c in
    Interv(n, n)
  | LStr _ | LWStr _ | LReal _ | LEnum _ -> No_integral ty

let size_of ty =
  try int_to_interv (Cil.bytesSizeOf ty)
  with Cil.SizeOfError _ -> eacsl_typ_of_typ Cil.ulongLongType

let align_of ty = int_to_interv (Cil.bytesAlignOf ty)

type offset_ty = Ty_no_offset | Ty_field of eacsl_typ | Ty_index

let type_of_indexed_host = function
  | No_integral (Ctype ty) as ty_host -> 
    (match Cil.unrollType ty with
    | TArray(ty, _, _, _) -> eacsl_typ_of_typ ty
    | TPtr _ -> ty_host
    | _ -> assert  false)
  | _ -> assert false

let rec type_term t = 
  Cil.CurrentLoc.set t.term_loc;
  let lty = t.term_type in
  let get_cty t = match t.term_type with Ctype ty -> ty | _ -> assert false in
  let dup f x = let y = f x in y, y in
  let ty, _ as res = match t.term_node with
    | TConst c -> dup (type_constant lty) c
    | TLval lv -> dup type_term_lval lv
    | TSizeOf ty -> dup size_of ty
    | TSizeOfE t -> 
      ignore (type_term t);
      dup size_of (get_cty t)
    | TSizeOfStr s -> dup int_to_interv (String.length s + 1 (* '\0' *)) 
    | TAlignOf ty -> dup align_of ty
    | TAlignOfE t ->
      ignore (type_term t);
      dup align_of (get_cty t)
    | TUnOp(Neg _, t) -> 
      unary_arithmetic
	(fun l u -> let opp = Z.sub Z.zero in opp u, opp l) t
    | TUnOp(BNot, t) ->
      unary_arithmetic
	(fun l u -> 
	  let nl = Z.lognot l in
	  let nu = Z.lognot u in
	  Z.min nl nu, Z.max nl nu) 
	t
    | TUnOp(LNot, t) ->
      let ty_t = type_term t in
      let ty = Interv(Z.zero, Z.one) in
      ty, join ty ty_t
    | TBinOp(PlusA _, t1, t2) -> 
      let add l1 u1 l2 u2 = Z.add l1 l2, Z.add u1 u2 in
      binary_arithmetic t.term_type add t1 t2 t
    | TBinOp((PlusPI | IndexPI | MinusPI | MinusPP), t1, t2) -> 
      ignore (type_term t1);
      ignore (type_term t2);
      let ty = No_integral lty in
      ty, ty
    | TBinOp(MinusA _, t1, t2) -> 
      let sub l1 u1 l2 u2 = Z.sub l1 u2, Z.sub u1 l2 in
      binary_arithmetic t.term_type sub t1 t2 t
    | TBinOp(Mult _, t1, t2) -> signed_rule t.term_type Z.mul t1 t2 t
    | TBinOp(Div _, t1, t2) -> 
      let div a b = 
	try Z.c_div a b 
	with Division_by_zero -> 
	  (* either the generated code will be dead (e.g. [false && 1/0]) or
	     it contains a potential RTE and thus it is actually equivalent to
	     dead code. In any case, any type is correct at this point and we
	     generate the less restrictive one (0 is always representable) in
	     order to be as more precise as possible. *)
	  Z.zero
      in
      signed_rule t.term_type div t1 t2 t
    | TBinOp(Mod, t1, t2) -> 
      let modu a b =
	try Z.c_rem a b with Division_by_zero -> Z.zero (* see Div *)
      in
      signed_rule t.term_type modu t1 t2 t
    | TBinOp(Shiftlt _, _t1, _t2) | TBinOp(Shiftrt, _t1, _t2) ->
      Error.not_yet "left/right shift"
    | TBinOp((Lt | Gt | Le | Ge | Eq | Ne | LAnd | LOr), t1, t2) -> 
      let ty1 = type_term t1 in
      let ty2 = type_term t2 in
      let ty = Interv(Z.zero, Z.one) in
      ty, join ty (join ty1 ty2)
    | TBinOp((BAnd | BXor | BOr), _t1, _t2) -> 
      Error.not_yet "missing binary bitwise operator"
    | TCastE(ty, _, t) -> 
      let ty_t = type_term t in
      let ty_c = eacsl_typ_of_typ ty in
      let ty = try meet ty_c ty_t with Cannot_compare -> ty_c in
      ty, ty (* an alarm is emitted by RTE anyway *)
    | TAddrOf lv | TStartOf lv -> 
      ignore (type_term_lval lv);
      let ty = No_integral lty in
      ty, ty
    | Tapp _ -> Error.not_yet "applying logic function"
    | Tlambda _ -> Error.not_yet "functional"
    | TDataCons _ -> Error.not_yet "constructor"
    | Tif(t1, t2, t3) -> 
      ignore (type_term t1);
      let ty2 = type_term t2 in
      let ty3 = type_term t3 in
      dup (join ty2) ty3
    | Tat(t, _)
    | Tbase_addr(_, t) -> dup type_term t
    | Toffset(_, t) ->
      ignore (type_term t);
      let n = Z.div (Bit_utils.max_bit_address ()) (Z.of_int 8) in
      let ty =
        try TInt(ikind_of_integer n true, [])
        with Cil.Not_representable -> Mpz.t ()
      in
      dup eacsl_typ_of_typ ty
    | Tblock_length(_, t) ->
      ignore (type_term t);
      let n = Z.div (Bit_utils.max_bit_size ()) (Z.of_int 8) in
      let ty =
        try TInt(ikind_of_integer n true, [])
        with Cil.Not_representable -> Mpz.t ()
      in
      dup eacsl_typ_of_typ ty
    | Tnull -> dup int_to_interv 0
    | TLogic_coerce(_, t) -> dup type_term t
    | TCoerce(t, ty) -> 
      (* Jessie specific *)
      ignore (type_term t);
      dup size_of ty
    | TCoerceE(t1, t2) -> 
      (* Jessie specific *)
      ignore (type_term t1);
      ignore (type_term t2);
      dup size_of (get_cty t2)
    | TUpdate _ -> Error.not_yet "functional update"
    | Ttypeof _ -> Error.not_yet "typeof"
    | Ttype _ -> Error.not_yet "C type"
    | Tempty_set -> Error.not_yet "empty tset"
    | Tunion _ -> Error.not_yet "union of tsets"
    | Tinter _ -> Error.not_yet "intersection of tsets"
    | Tcomprehension _ -> Error.not_yet "tset comprehension"
    | Trange _ -> Error.not_yet "range"
    | Tlet _ -> Error.not_yet "let binding"
    | TOffsetOf _ -> Error.not_yet "OffsetOf"
    | Toffset_min _ -> Error.not_yet "offset_min"
    | Toffset_max _ -> Error.not_yet "offset_max"
  in
(*  Options.feedback "ADD %a --> %a" Printer.pp_term t pretty_eacsl_typ ty;*)
  Term_env.add t res;
  ty

and type_term_lval (h, o) =
  let ty_off = type_term_offset o in
  let ty_host = type_term_lhost h in
  match ty_off with
  | Ty_no_offset -> ty_host
  | Ty_field ty -> ty
  | Ty_index -> type_of_indexed_host ty_host

and type_term_lhost = function
  | TVar lv -> 
    (try Logic_var_env.find lv 
     with Not_found -> 
       (* C variable *)
       match lv.lv_type with
       | Ctype ty -> eacsl_typ_of_typ ty
       | _ -> 
	 Options.fatal "invalid type for logic var %a: %a" 
	   Logic_var.pretty lv Logic_type.pretty lv.lv_type)
  | TResult ty -> eacsl_typ_of_typ ty
  | TMem t -> 
    let ty = type_term t in
    (* got a pointer or an array *)
    match ty with
    | No_integral (Ctype ty) ->
      (match Cil.unrollType ty with
      | TPtr(ty, _) | TArray(ty, _, _, _) -> eacsl_typ_of_typ ty
      | _ -> assert false)
    | No_integral _ | Interv _ | Z -> assert false

and type_term_offset = function
  | TNoOffset -> Ty_no_offset
  | TField(f, o) -> 
    (match type_term_offset o with
    | Ty_no_offset -> Ty_field (eacsl_typ_of_typ f.ftype)
    | Ty_index -> Ty_field (type_of_indexed_host (eacsl_typ_of_typ f.ftype))
    | Ty_field _ as ty -> ty)
  | TIndex(t, o) ->
    ignore (type_term t);
    ignore (type_term_offset o);
    Ty_index
  | TModel _ -> Error.not_yet "model"

and unary_arithmetic op t = 
  let ty_t = type_term t in
  let ty = match ty_t with
    | Interv(l, u) -> 
      let l, u = op l u in
      Interv (l, u)
    | Z -> Z
    | No_integral _ -> ty_t
  in
  ty, join ty ty_t
      
and binary_arithmetic ty op t1 t2 _t =
  let ty1 = type_term t1 in
  let ty2 = type_term t2 in
  let ty = match ty1, ty2 with
    | Interv(l1, u1), Interv(l2, u2) -> 
      let l, u = op l1 u1 l2 u2 in
      Interv (l, u)
    | No_integral _, _ | _, No_integral _ -> No_integral ty
    | _, Z | Z, _ -> Z
  in
  ty, join ty (join ty1 ty2)

and signed_rule ty op t1 t2 t =
  (* probably not the most efficient way to compute the result, but the
     shortest *) 
  let compute l1 u1 l2 u2 = 
    let a = op l1 l2 in
    let b = op l1 u2 in
    let c = op u1 l2 in
    let d = op u1 u2 in
    Z.min a (Z.min b (Z.min c d)), Z.max a (Z.max b (Z.max c d))
  in
  binary_arithmetic ty compute t1 t2 t

let compute_quantif_guards_ref
    : (predicate named -> logic_var list -> predicate named -> 
       (term * relation * logic_var * relation * term) list) ref
    = Extlib.mk_fun "compute_quantif_guards_ref"

let rec type_predicate_named p = 
  Cil.CurrentLoc.set p.loc;
  match p.content with
  | Pfalse | Ptrue -> ()
  | Papp _ -> Error.not_yet "logic function application"
  | Pseparated _ -> Error.not_yet "\\separated"
  | Pdangling _ -> Error.not_yet "\\dangling"
  | Prel(_, t1, t2) -> 
    ignore (type_term t1);
    ignore (type_term t2)
  | Pand(p1, p2) | Por(p1, p2) | Pxor(p1, p2) | Pimplies(p1, p2) 
  | Piff(p1, p2) ->
    type_predicate_named p1;
    type_predicate_named p2
  | Pnot p -> type_predicate_named p
  | Pif(t, p1, p2) -> 
    ignore (type_term t);
    type_predicate_named p1;
    type_predicate_named p2
  | Plet _ -> Error.not_yet "let _ = _ in _"
  | Pforall(bounded_vars, { content = Pimplies(hyps, goal) })
  | Pexists(bounded_vars, { content = Pand(hyps, goal) }) ->
    let guards = !compute_quantif_guards_ref p bounded_vars hyps in
    List.iter
      (fun (t1, r1, x, r2, t2) -> 
	let ty1 = type_term t1 in
	let ty1 = match ty1, r1 with
	  | Interv(l, u), Rlt -> Interv(Z.add l Z.one, Z.add u Z.one)
	  | Interv(l, u), Rle -> Interv(l, u)
	  | Z, (Rlt | Rle) -> Z
	  | _, _ -> assert false
	in
	let ty2 = type_term t2 in
	(* add one here, since we increment the loop counter one more time
	   before going out the loop. *)
	let ty2 = match ty2, r2 with
	  | Interv(l, u), Rlt -> Interv(l, u)
	  | Interv(l, u), Rle -> Interv(Z.add l Z.one, Z.add u Z.one)
	  | Z, (Rlt | Rle) -> Z
	  | _, _ -> assert false
	in
	Logic_var_env.add x (join ty1 ty2))
      guards;
    type_predicate_named hyps;
    type_predicate_named goal
  | Pforall _ -> Error.not_yet "unguarded \\forall quantification"
  | Pexists _ -> Error.not_yet "unguarded \\exists quantification"
  | Pat(p, _) -> type_predicate_named p
  | Pfresh _ -> Error.not_yet "\\fresh"
  | Psubtype _ -> Error.not_yet "subtyping relation" (* Jessie specific *)
  | Pinitialized (_, x)
  | Pfreeable(_, x)
  | Pallocable(_, x)
  | Pvalid(_, x)
  | Pvalid_read(_, x) -> ignore (type_term x)

let type_term t = 
  if not (Options.Gmp_only.get ()) then begin
    Options.feedback ~dkey ~level:4 "typing term %a." Printer.pp_term t;
    let ty = type_term t in
    Options.debug ~dkey ~level:4 "got %a." pretty_eacsl_typ ty;
  end

let type_named_predicate ?(must_clear=true) p = 
  if not (Options.Gmp_only.get ()) then begin
    Options.feedback ~dkey ~level:3 "typing predicate %a." 
      Printer.pp_predicate_named p;
    if must_clear then clear ();
    type_predicate_named p
  end

(******************************************************************************)
(** Subtyping *)
(******************************************************************************)

(* convert [e] in a way that it is compatible with the given typing context. *)
let context_sensitive ~loc ?name env ctx is_mpz_string t_opt e = 
  let ty = Cil.typeOf e in
(*  Options.feedback "exp %a in context %a" 
    Printer.pp_exp e Printer.pp_typ ctx;*)
  let mk_mpz e = 
    let _, e, env = 
      Env.new_var 
	~loc
	?name
	env
	t_opt
	(Mpz.t ())
	(fun lv v -> [ Mpz.init_set ~loc (Cil.var lv) v e ])
    in
    e, env
  in
  let do_int_ctx ty =
    (* handle a C-integer context *)
    let e, env = if is_mpz_string then mk_mpz e else e, env in
    if (Mpz.is_t ty || is_mpz_string) then
      (* we get an mpz, but it fits into a C integer: convert it *)
      let fname, new_ty = 
	if Cil.isSignedInteger ty then 
	  "__gmpz_get_si", Cil.longType
	else
	  "__gmpz_get_ui", Cil.ulongType 
      in
      let _, e, env = 
	Env.new_var
	  ~loc
	  ?name
	  env
	  None
	  new_ty
	  (fun v _ -> [ Misc.mk_call ~loc ~result:(Cil.var v) fname [ e ] ])
      in
      e, env
    else
      (if Cil.isIntegralType ctx && Cil.isIntegralType ty then 
	  Cil.mkCast e (Cil.arithmeticConversion ctx ty)
       else
	  e),
      env
  in
  if Mpz.is_t ctx then
    if Mpz.is_t ty then
      e, env
    else
      (* Convert the C integer into a mpz. 
	 Remember: very long integer constants have been temporary converted
	 into strings;
	 also possible to get a non integralType (or Mpz.t) with a non-one in
	 the case of \null *)
      let e = 
	if Cil.isIntegralType ty || is_mpz_string then e
	else Cil.mkCast e Cil.longType (* \null *)
      in
      mk_mpz e
  else
    do_int_ctx ty

let principal_type t1 t2 = 
  let ty1 = typ_of_term t1 in
  let ty2 = typ_of_term t2 in
  (* possible to get an integralType (or Mpz.t) from a non-one in the case of
     \null *)
  if Cil.isIntegralType ty1 then
    if Cil.isIntegralType ty2 then Cil.arithmeticConversion ty1 ty2
    else if Mpz.is_t ty2 then ty2 else ty1
  else if Mpz.is_t ty1 then
    if Cil.isIntegralType ty2 || Mpz.is_t ty2 then ty1 else ty2
  else 
    ty2

(*
Local Variables:
compile-command: "make"
End:
*)
