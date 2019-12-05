(* *********************************************************************)
(*                                                                     *)
(*                 The Vélus verified Lustre compiler                  *)
(*                                                                     *)
(*             (c) 2019 Inria Paris (see the AUTHORS file)             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

From Velus Require Import Common.
From Velus Require Import Operators.

(** * The core dataflow expresion syntax *)

Module Type CESYNTAX (Import Op: OPERATORS).

  (** ** Expressions *)

  (* We do not want the too weak Coq generated induction principles *)
  Unset Elimination Schemes.

  Inductive exp : Type :=
  | Econst : const -> exp
  | Evar   : ident -> type -> exp
  | Ewhen  : exp -> ident -> bool -> exp
  | Eop    : operator -> list exp -> type -> exp.

  (* Back to normal *)
  Set Elimination Schemes.

  (* Let us define our own induction principle *)
  Definition exp_ind (P : exp -> Prop)
    (f_const : forall c, P (Econst c))
    (f_var   : forall id ty, P (Evar id ty))
    (f_when  : forall e, P e -> forall id b, P (Ewhen e id b))
    (f_op    : forall op el (IHe : List.Forall P el), forall ty, P (Eop op el ty)) :=
  fix F (x : exp) : P x :=
    match x as e return (P e) with
    | Econst c => f_const c
    | Evar id ty => f_var id ty
    | Ewhen e id b => f_when e (F e) id b
    | Eop op el ty => f_op op el (list_ind (List.Forall P) (List.Forall_nil P)
           (fun e el IHel => List.Forall_cons e (F e) IHel) el) ty
    end.

  (** ** Control expressions *)

  Inductive cexp : Type :=
  | Emerge : ident -> cexp -> cexp -> cexp
  | Eite   : exp -> cexp -> cexp -> cexp
  | Eexp   : exp -> cexp.

  Fixpoint typeof (le: exp): type :=
    match le with
    | Econst c => type_const c
    | Evar _ ty
    | Eop _ _ ty => ty
    | Ewhen e _ _ => typeof e
    end.

  (** Predicate used in [normal_args] in NLustre and Stc. *)
  Fixpoint noops_exp (ck: clock) (e : exp) : Prop :=
    match ck with
    | Cbase => True
    | Con ck' _ _ =>
      match e with
      | Econst _ | Evar _ _ => True
      | Ewhen e' _ _ => noops_exp ck' e'
      | _ => False
      end
    end.

End CESYNTAX.

Module CESyntaxFun (Op: OPERATORS) <: CESYNTAX Op.
  Include CESYNTAX Op.
End CESyntaxFun.
