(**************************************************************************)
(*                                                                        *)
(*  This file is part of the Frama-C's E-ACSL plug-in.                    *)
(*                                                                        *)
(*  Copyright (C) 2012-2016                                               *)
(*    CEA (Commissariat � l'�nergie atomique et aux �nergies              *)
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

(** Convert quantifiers. *)

open Cil_types

val quantif_to_exp: kernel_function -> Env.t -> predicate -> exp * Env.t
(** The given predicate must be a quantification. *)

(* ***********************************************************************)
(** {2 Forward references} *)
(* ***********************************************************************)

val predicate_to_exp_ref: 
  (kernel_function -> Env.t -> predicate -> exp * Env.t) ref

val term_to_exp_ref: 
  (kernel_function -> Env.t -> term -> exp * Env.t) ref

(*
Local Variables:
compile-command: "make"
End:
*)
