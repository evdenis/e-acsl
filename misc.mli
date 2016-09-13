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

(** Utilities for E-ACSL. *)

open Cil_types
open Cil_datatype

(* ************************************************************************** *)
(** {2 Builders} *)
(* ************************************************************************** *)

exception Unregistered_library_function of string
val mk_call: loc:Location.t -> ?result:lval -> string -> exp list -> stmt
(** Call an E-ACSL library function.
    @raise Unregistered_library_function if the given string does not represent
    such a function or if these functions were never registered (only possible
    when using E-ACSL through its API. *)

val mk_debug_mmodel_stmt: stmt -> stmt

type annotation_kind = 
  | Assertion
  | Precondition
  | Postcondition
  | Invariant
  | RTE

val e_acsl_guard_name: string

val mk_e_acsl_guard: 
  ?reverse:bool -> annotation_kind -> kernel_function -> exp -> predicate named 
  -> stmt

val mk_block: Project.t -> stmt -> block -> stmt

(* ************************************************************************** *)
(** {2 Handling \result} *)
(* ************************************************************************** *)

val result_lhost: kernel_function -> lhost
(** @return the lhost corresponding to \result in the given function *)

val result_vi: kernel_function -> varinfo
(** @return the varinfo corresponding to \result in the given function *)

(* ************************************************************************** *)
(** {2 Handling the E-ACSL's C-libraries} *)
(* ************************************************************************** *)

val library_files: unit -> string list
val is_library_loc: location -> bool
val register_library_function: varinfo -> unit
val reset: unit -> unit

val mk_store_stmt: ?str_size:exp -> varinfo -> stmt
val mk_delete_stmt: varinfo -> stmt
val mk_full_init_stmt: ?addr:bool -> varinfo -> stmt
val mk_initialize: loc:location -> lval -> stmt
val mk_literal_string: varinfo -> stmt

(* ************************************************************************** *)
(** {2 Other stuff} *)
(* ************************************************************************** *)

val term_addr_of: loc:location -> term_lval -> typ -> term
val is_generated_varinfo: varinfo -> bool
val is_generated_kf: kernel_function -> bool

(*
Local Variables:
compile-command: "make"
End:
*)
