From Velus Require Import Common.
From Velus Require Import Operators.

(** * The core dataflow expresion syntax *)

Module Type CESYNTAX (Import Op: OPERATORS).

  (** ** Expressions *)

  Inductive exp : Type :=
  | Econst : const -> exp
  | Evar   : ident -> type -> exp
  | Ewhen  : exp -> ident -> bool -> exp
  | Eunop  : unop -> exp -> type -> exp
  | Ebinop : binop -> exp -> exp -> type -> exp.

  (** ** Control expressions *)

  Inductive cexp : Type :=
  | Emerge : ident -> cexp -> cexp -> cexp
  | Eite   : exp -> cexp -> cexp -> cexp
  | Eexp   : exp -> cexp.

  Fixpoint typeof (le: exp): type :=
    match le with
    | Econst c => type_const c
    | Evar _ ty
    | Eunop _ _ ty
    | Ebinop _ _ _ ty => ty
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
