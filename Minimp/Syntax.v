Require Import Rustre.Nelist.
Require Import Rustre.Common.


Open Scope bool_scope.
Import List.ListNotations.
Open Scope list_scope.

(** * Minimp syntax *)

(**

  Minimp is a minimal object-oriented programming language exposing
  two methods: [step] and [reset].

 *)
Module Type PRE_SYNTAX
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op).

  Inductive exp : Type :=
  | Var   : ident -> typ -> exp                    (* variable  *)
  | State : ident -> typ -> exp                    (* state variable  *)
  | Const : const-> exp                            (* constant *)
  | Unop  : unary_op -> exp -> typ -> exp          (* unary operator *)
  | Binop : binary_op -> exp -> exp -> typ -> exp. (* binary operator *)

  Definition typeof (e: exp): typ :=
    match e with
    | Const c => typ_const c
    | Var _ ty
    | State _ ty
    | Unop _ _ ty
    | Binop _ _ _ ty => ty
    end.

  Inductive stmt : Type :=
  | Assign : ident -> exp -> stmt                               (* x = e *)
  | AssignSt : ident -> exp -> stmt                             (* self.x = e *)
  | Ifte : exp -> stmt -> stmt -> stmt                           (* if e then s1 else s2 *)
  | Step_ap : ident -> typ -> ident -> ident -> nelist exp -> stmt (* y:ty = (C x).step(es) *)
  | Reset_ap : ident -> ident -> stmt                           (* (C x).reset() *)
  | Comp : stmt -> stmt -> stmt                                 (* s1; s2 *)
  | Skip.

  Record obj_dec : Type :=
    mk_obj_dec {
        obj_inst  : ident;
        obj_class : ident
      }.

  (* TODO: lots of fields are not strictly necessary *)
  Record class : Type :=
    mk_class {
        c_name   : ident;

        c_input  : nelist (ident * typ);
        c_output : ident * typ;
        c_vars   : list (ident * typ);

        c_mems   : list (ident * typ);
        c_objs   : list obj_dec;

        c_step   : stmt;
        c_reset  : stmt
      }.

  Definition program : Type := list class.

  (* definition is needed in signature *)
  Definition find_class (n: ident) : program -> option (class * list class) :=
    fix find p :=
    match p with
    | [] => None
    | c :: p' => if ident_eqb c.(c_name) n then Some (c, p') else find p'
    end.

End PRE_SYNTAX.

Module Type SYNTAX
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op).

  Include PRE_SYNTAX Op OpAux.

  (** ** Decidable equality *)

  Parameter exp_eqb : exp -> exp -> bool.

  Axiom exp_eqb_eq:
    forall e1 e2, exp_eqb e1 e2 = true <-> e1 = e2.

End SYNTAX.

Module SyntaxFun
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op) <: SYNTAX Op OpAux.
  Include PRE_SYNTAX Op OpAux.

  Implicit Type e: exp.
  Implicit Type s: stmt.
  Implicit Type cl: class.
  Implicit Type p: program.

  (** ** Induction principle for [exp] *)

  (* Print exp_ind. *)

  (* Definition exp_ind2 : forall P : exp -> Prop, *)
  (*   (forall i, P (Var i)) -> *)
  (*   (forall i, P (State i)) -> *)
  (*   (forall c, P (Const c)) -> *)
  (*   (forall op es (IHes : Nelist.Forall P es), P (Op op es)) -> *)
  (*   forall e, P e. *)
  (* Proof. *)
  (* intros P Hvar Hstate Hcons Hop. fix 1. *)
  (* intros e. destruct e as [i | i | c | op es]. *)
  (* + apply Hvar. *)
  (* + apply Hstate. *)
  (* + apply Hcons. *)
  (* + apply Hop. now induction es as [e | e es]; constructor. *)
  (* Defined. *)

  (** ** Decidable equality *)

  (* XXX: use [exp_ind2] *)
  Definition exp_eqb : exp -> exp -> bool.
  Proof.
    fix 1.
    intros e1 e2.
    refine (match e1, e2 with
            | Var x1 ty1, Var x2 ty2 => ident_eqb x1 x2 && equiv_decb ty1 ty2
            | State s1 ty1, State s2 ty2 => ident_eqb s1 s2 && equiv_decb ty1 ty2
            | Const c1, Const c2 => equiv_decb c1 c2
            | Unop op1 e1' ty1, Unop op2 e2' ty2 => equiv_decb op1 op2
                                                 && equiv_decb ty1 ty2 && _
            | Binop op1 e11 e12 ty1, Binop op2 e21 e22 ty2 => equiv_decb op1 op2
                                                           && equiv_decb ty1 ty2
                                                           && _
            | _, _ => false
            end).
    - exact (exp_eqb e1' e2').
    - exact (exp_eqb e11 e21 && exp_eqb e12 e22).
  Defined.

  Lemma exp_eqb_eq:
    forall e1 e2,
      exp_eqb e1 e2 = true <-> e1 = e2.
  Proof.
    induction e1 (* using exp_ind2 *); intros e2; destruct e2; simpl; try now split; intro; discriminate.
    - rewrite Bool.andb_true_iff, ident_eqb_eq, equiv_decb_equiv.
      split; intro Heq; [now f_equal | now inversion Heq].
    - rewrite Bool.andb_true_iff, ident_eqb_eq, equiv_decb_equiv.
      split; intro Heq; [now f_equal | now inversion Heq].
    - rewrite equiv_decb_equiv.
      split; intro Heq; [now f_equal | now inversion Heq].
    - rewrite 2 Bool.andb_true_iff, equiv_decb_equiv, equiv_decb_equiv.
      split; intro Heq.
      + f_equal; try apply IHe1; apply Heq.
      + now inversion Heq; subst; rewrite IHe1.
    - rewrite 3 Bool.andb_true_iff, equiv_decb_equiv, equiv_decb_equiv.
      rewrite IHe1_1, IHe1_2.
      split; intro Heq.
      + f_equal; apply Heq.
      + now inversion Heq.
  Qed.

End SyntaxFun.

