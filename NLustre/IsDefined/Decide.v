Require Import PArith.
Require Import List.

Import List.ListNotations.
Open Scope list_scope.

Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.NLustre.Syntax.
Require Import Velus.NLustre.IsDefined.
Require Import Velus.NLustre.Memories.

(** * Defined variables : decision procedure *)

(**

Decision procedure for the [Is_defined_in] predicate. We show that it
is equivalent to its specification.

Remark: This development is not formally part of the correctness proof.

 *)

Module Type DECIDE
       (Ids : IDS)
       (Op  : OPERATORS)
       (Import Syn : SYNTAX Ids Op)
       (Import Mem : MEMORIES Ids Op Syn)
       (Import IsD : ISDEFINED Ids Op Syn Mem).

  (** ** Decision procedures: *)

  Fixpoint defined_eq (defs: PS.t) (eq: equation) {struct eq} : PS.t :=
    match eq with
    | EqDef x _ _   => PS.add x defs
    | EqApp xs _ _ _ => ps_adds xs defs
    | EqFby x _ _ _ => PS.add x defs
    end.

  Definition defined (eqs: list equation) : PS.t :=
    List.fold_left defined_eq eqs PS.empty.

  (** ** Silly unfolding property: *)

  Lemma In_fold_left_defined_eq:
    forall x eqs m,
      PS.mem x (List.fold_left defined_eq eqs m) = true
      <-> PS.mem x (List.fold_left defined_eq eqs PS.empty) = true \/ PS.In x m.
  Proof.
    induction eqs as [|eq].
    - split; auto.
      destruct 1 as [H|]; auto.
      now apply not_In_empty in H; contradiction.
    - split.
      + intro H.
        simpl; rewrite IHeqs.
        simpl in H; apply IHeqs in H; destruct H; auto;
        destruct eq;
        (* XXX: this is Ltac p0rn *)
        match goal with
        | |- context[ EqApp _ _ _ _ ] => generalize ps_adds_spec; intro add_spec
        | _ => generalize PS.add_spec; intro add_spec
        end;
        apply add_spec in H;
        destruct H;
        match goal with
        | H: PS.In x ?m |- context [PS.In x ?m] => now intuition
        | H: x = _ |- _ => subst x
        | H: In x ?i |- context [EqApp ?i _ _ _] => idtac
        end;
        constructor(constructor(apply add_spec; intuition)).

      + destruct 1 as [H|H].
        * simpl in H; rewrite IHeqs in H; apply IHeqs; destruct H; auto.
          right.
          destruct eq;
            match goal with
            | |- context[ EqApp _ _ _ _ ] =>
              generalize ps_adds_spec; intro add_spec
            | _ =>
              generalize PS.add_spec; intro add_spec
            end;
            simpl; apply add_spec;
            apply add_spec in H; destruct H;
            intuition;
            apply not_In_empty in H; contradiction.
        * apply IHeqs; right; destruct eq;
            match goal with
            | |- context[ EqApp _ _ _ _ ] =>
              generalize ps_adds_spec; intro add_spec
            | _ =>
              generalize PS.add_spec; intro add_spec
            end;
            apply add_spec; auto.
  Qed.

  (** ** Reflection lemmas: *)

  Lemma Is_defined_in_eqP :
    forall x eq, Is_defined_in_eq x eq <-> PS.mem x (defined_eq PS.empty eq) = true.
  Proof.
  intros x eq; split; [ intro Hdef | intro Hmem].
  - (* ==> *)
    destruct Hdef; simpl;
    match goal with
    | |- context[ PS.mem ?x (PS.add ?x _) ] =>
      now rewrite PSE.add_mem_1
    | |- context[ PS.mem _ (ps_adds _ _) ] =>
      now apply PS.mem_spec, ps_adds_spec; auto
    end.
  - (* <== *)
    destruct eq; simpl in *;
    match goal with
    | |- context[ EqApp _ _ _ _ ] =>
      edestruct (in_dec ident_eq_dec) as [Hin_xys | Hnin_xys];
        [ eauto using Is_defined_in_eq
        | exfalso;
          apply ps_adds_spec in Hmem as [Hmem | Hmem]; auto;
          eapply not_In_empty; eauto ]
    | _ =>
      destruct (ident_eq_dec i x) eqn:Hxi;
        [ subst; auto using Is_defined_in_eq
        | exfalso;
          rewrite PSP.Dec.F.add_neq_b, PSF.empty_b in Hmem; auto;
          discriminate ]
    end.
  Qed.

  Lemma Is_defined_inP:
    forall x eqs,
      Is_defined_in_eqs x eqs <-> PS.mem x (defined eqs) = true.
  Proof.
    unfold defined, Is_defined_in_eqs.
    induction eqs as [ | eq ].
    - rewrite List.Exists_nil; split; intro H;
      try apply not_In_empty in H; contradiction.
    - simpl;
        rewrite In_fold_left_defined_eq, PS.mem_spec.
      split.
      + (* ==> *)
        intro H; apply List.Exists_cons in H; destruct H.
        inversion H; destruct eq;
          match goal with
          | |- context[ EqApp _ _ _ _ ] =>
            generalize ps_adds_spec; intro add_spec
          | _ =>
            generalize PS.add_spec; intro add_spec
          end;
          (right; apply add_spec; intuition).
        left; apply IHeqs; apply H.
      + (* <== *)
        rewrite List.Exists_cons.
        destruct 1.
        * now intuition.
        * destruct eq;
            match goal with
            | |- context[ EqApp _ _ _ _ ] =>
              generalize ps_adds_spec; intro add_spec
            | _ =>
              generalize PS.add_spec; intro add_spec
            end;
          (simpl in H; apply add_spec in H; destruct H;
           [ try rewrite H; left; constructor; auto
           | apply not_In_empty in H; contradiction]).

  Qed.

  Lemma Is_defined_in_eq_dec:
    forall x eq, {Is_defined_in_eq x eq}+{~Is_defined_in_eq x eq}.
  Proof.
    intros;
      eapply Bool.reflect_dec,
             Bool.iff_reflect,
             Is_defined_in_eqP.
  Qed.

  Lemma Is_defined_in_dec:
    forall x eqs, {Is_defined_in_eqs x eqs}+{~Is_defined_in_eqs x eqs}.
  Proof.
    intros;
      eapply Bool.reflect_dec,
             Bool.iff_reflect,
             Is_defined_inP.
  Qed.


  Lemma decidable_Is_defined_in_eqs:
    forall x eqs,
      Decidable.decidable (Is_defined_in_eqs x eqs).
  Proof.
    intros. apply decidable_Exists.
    intros eq Hin.
    destruct (Is_defined_in_eq_dec x eq); [left|right]; auto.
  Qed.

  (** ** Properties *)

  Lemma Is_defined_in_eqs_var_defined:
    forall x eq,
      Is_defined_in_eq x eq <-> List.In x (var_defined eq).
  Proof.
  intros; rewrite Is_defined_in_eqP, PS.mem_spec.

  destruct eq; simpl;
    rewrite ?PSF.add_iff, ?ps_adds_spec, PSF.empty_iff;
    intuition.
  Qed.

  Lemma Is_defined_in_var_defined:
    forall x eqs,
      Is_defined_in_eqs x eqs
      <-> In x (vars_defined eqs).
  Proof.
  intros; rewrite Is_defined_inP, PS.mem_spec.

  induction eqs as [ | eq eqs IHeqs ]; simpl.
  - now rewrite PSF.empty_iff.
  - destruct eq;
    rewrite <- PS.mem_spec; unfold defined; simpl;
    match goal with
    | |- context[ EqApp _ _ _ _ ] =>
      unfold vars_defined;
        rewrite concatMap_cons, in_app
    | _ => idtac
    end;
    rewrite In_fold_left_defined_eq,
            ?PSF.add_iff, ?ps_adds_spec,
            PSF.empty_iff, IHeqs; intuition.
  Qed.

  Lemma Is_defined_in_cons:
    forall x eq eqs,
      Is_defined_in_eqs x (eq :: eqs) ->
      Is_defined_in_eq x eq
      \/ (~Is_defined_in_eq x eq /\ Is_defined_in_eqs x eqs).
  Proof.
    intros x eq eqs Hdef.
    apply List.Exists_cons in Hdef.
    destruct (Is_defined_in_eq_dec x eq); intuition.
  Qed.

  Lemma In_memory_eq_In_defined_eq:
    forall x eq S,
      PS.In x (memory_eq S eq)
      -> PS.In x (defined_eq S eq).
  Proof.
    intros x eq S HH.
    destruct eq;
      match goal with
      | |- context[ EqApp _ _ _ _ ] =>
        generalize ps_adds_spec; intro add_spec
      | _ =>
        generalize PS.add_spec; intro add_spec
      end;
      try (apply add_spec; now intuition).
    apply add_spec in HH.
    destruct HH as [HH|HH].
    - rewrite HH; apply add_spec; left; reflexivity.
    - apply add_spec; right; exact HH.
  Qed.

  Lemma In_fold_left_memory_eq_defined_eq:
    forall x eqs S,
      PS.In x (List.fold_left memory_eq eqs S)
      -> PS.In x (List.fold_left defined_eq eqs S).
  Proof.
    intros x eqs.
    induction eqs as [|eq eqs IH]; [now intuition|].
    intros S HH.
    apply IH in HH; clear IH.
    apply In_fold_left_defined_eq in HH.
    simpl. apply In_fold_left_defined_eq.
    destruct HH as [HH|HH].
    - left; exact HH.
    - right; now apply In_memory_eq_In_defined_eq with (1:=HH).
  Qed.

  Lemma not_Exists_Is_defined_in_eqs_n_in:
    forall n,
      ~Exists (fun ni=>Is_defined_in_eqs ni n.(n_eqs)) (map fst n.(n_in)).
  Proof.
    intros n HH.
    assert (forall {B} eqs (xs:list (ident*B)),
      Exists (fun ni=> Is_defined_in_eqs ni eqs) (map fst xs)
      <-> Exists (fun x=> Is_defined_in_eqs (fst x) eqs) xs) as Hexfst.
    { intros B eqs. induction xs as [|x xs].
      - simpl. now rewrite 2 Exists_nil.
      - simpl. split;
                 inversion_clear 1;
                 try (now constructor);
                 try (constructor (now apply IHxs)). }
    rewrite Hexfst in HH; clear Hexfst.
    apply decidable_Exists_not_Forall in HH.
    2:(intros; apply decidable_Is_defined_in_eqs).
    apply HH. clear HH.
    apply Forall_forall.
    intros x Hin.
    rewrite Is_defined_in_var_defined.
    rewrite n.(n_defd).
    destruct x as [x xty].
    apply In_InMembers in Hin.
    rewrite <-fst_InMembers. simpl.
    apply (NoDupMembers_app_InMembers _ _ _ n.(n_nodup) Hin).
  Qed.

End DECIDE.

Module DecideFun
       (Ids : IDS)
       (Op  : OPERATORS)
       (Import Syn : SYNTAX Ids Op)
       (Import Mem : MEMORIES Ids Op Syn)
       (Import IsD : ISDEFINED Ids Op Syn Mem)
       <: DECIDE Ids Op Syn Mem IsD.

  Include DECIDE Ids Op Syn Mem IsD.

End DecideFun.
