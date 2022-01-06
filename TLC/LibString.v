(**************************************************************************
* TLC: A library for Coq                                                  *
* Strings                                                                 *
**************************************************************************)

Set Implicit Arguments.
From SLF (* TLC *) Require Import LibTactics LibReflect.
Require Export Coq.Strings.String.

(* ********************************************************************** *)
(* ################################################################# *)
(** * Inhabited *)

Instance Inhab_string : Inhab string.
Proof using. apply (Inhab_of_val EmptyString). Qed.

(* 2020-03-09 15:04:14 (UTC+01) *)
