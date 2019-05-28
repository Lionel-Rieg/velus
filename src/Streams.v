From Coq Require Import List.
From Coq Require Export Lists.Streams.
From Coq Require Import Setoid.
From Coq Require Import Morphisms.
From Coq Require Import Arith.EqNat.
From Coq Require Import Omega.

From Velus Require Import Common.

Infix ":::" := Cons (at level 60, right associativity) : stream_scope.
Infix "≡" := EqSt (at level 70, no associativity) : stream_scope.

Delimit Scope stream_scope with Stream.
Open Scope stream_scope.

Lemma const_nth:
  forall {A} n (c: A),
    Str_nth n (Streams.const c) = c.
Proof.
  induction n; simpl; auto.
Qed.

Ltac unfold_Stv xs :=
  rewrite (unfold_Stream xs);
  destruct xs as [[|]];
  simpl.

Ltac unfold_St xs :=
  rewrite (unfold_Stream xs);
  destruct xs;
  simpl.

Add Parametric Relation A : (Stream A) (@EqSt A)
    reflexivity proved by (@EqSt_reflex A)
    symmetry proved by (@sym_EqSt A)
    transitivity proved by (@trans_EqSt A)
      as EqStrel.

Lemma eq_EqSt:
  forall {A}, inclusion (Stream A) eq (@EqSt A).
Proof.
  intros ? xs xs' E.
  now rewrite E.
Qed.

Add Parametric Morphism A : (@Cons A)
    with signature eq ==> @EqSt A ==> @EqSt A
      as Cons_EqSt.
Proof.
  cofix Cofix.
  intros x xs xs' Exs.
  constructor; simpl; auto.
Qed.

Add Parametric Morphism A : (@hd A)
    with signature @EqSt A ==> eq
      as hd_EqSt.
Proof.
  intros xs xs' Exs.
  destruct xs, xs'; inv Exs; simpl; auto.
Qed.

Add Parametric Morphism A : (@tl A)
    with signature @EqSt A ==> @EqSt A
      as tl_EqSt.
Proof.
  intros xs xs' Exs.
  destruct xs, xs'; inv Exs; simpl; auto.
Qed.

Add Parametric Morphism A (n: nat) : (@Str_nth A n)
    with signature @EqSt A ==> eq
      as Str_nth_EqSt.
Proof.
  intros xs xs' Exs.
  apply eqst_ntheq; auto.
Qed.

Section EqSts.
  Variable A: Type.

  Definition EqSts (xss yss: list (Stream A)) :=
    Forall2 (@EqSt A) xss yss.

  Theorem EqSts_reflex: forall xss, EqSts xss xss.
  Proof.
    induction xss; constructor; auto.
    reflexivity.
  Qed.

  Theorem EqSts_sym: forall xss yss, EqSts xss yss -> EqSts yss xss.
  Proof.
    induction xss, yss; intros * H; auto; try inv H.
    constructor.
    - now symmetry.
    - now apply IHxss.
  Qed.

  Theorem EqSts_trans: forall xss yss zss, EqSts xss yss -> EqSts yss zss -> EqSts xss zss.
  Proof.
    induction xss, yss, zss; intros * Hx Hy; auto; try inv Hx; try inv Hy.
    constructor.
    - now transitivity s.
    - eapply IHxss; eauto.
  Qed.

End EqSts.

Add Parametric Relation A : (list (Stream A)) (@EqSts A)
    reflexivity proved by (@EqSts_reflex A)
    symmetry proved by (@EqSts_sym A)
    transitivity proved by (@EqSts_trans A)
      as EqStsrel.

Add Parametric Morphism A : (@List.cons (Stream A))
    with signature @EqSt A ==> @EqSts A ==> @EqSts A
      as cons_EqSt.
Proof. constructor; auto. Qed.

Add Parametric Morphism A : (@List.app (Stream A))
    with signature @EqSts A ==> @EqSts A ==> @EqSts A
      as app_EqSts.
Proof.
  intros xss xss' Exss yss yss' Eyss.
  revert dependent yss; revert dependent xss'.
  induction xss; induction yss; intros; inv Exss; inv Eyss;
    simpl; try constructor; auto.
  - now rewrite 2 app_nil_r.
  - apply IHxss; auto.
    constructor; auto.
Qed.

Add Parametric Morphism
    A B (P: A -> Stream B -> Prop) xs
    (P_compat: Proper (eq ==> @EqSt B ==> Basics.impl) P)
  : (@Forall2 A (Stream B) P xs)
    with signature @EqSts B ==> Basics.impl
      as Forall2_EqSt.
Proof.
  intros ys ys' Eys.
  revert xs ys ys' Eys;
    induction xs, ys; intros ** H; inv H; inv Eys; auto.
  constructor; eauto.
  - eapply P_compat; eauto.
  - eapply IHxs; eauto.
Qed.

Add Parametric Morphism
    A B (P: Stream A -> B -> Prop)
    (P_compat: Proper (@EqSt A ==> eq ==> Basics.impl) P)
  : (@Forall2 (Stream A) B P)
    with signature @EqSts A ==> eq ==> Basics.impl
      as Forall2_EqSt'.
Proof.
  intros ys ys' Eys xs.
  revert xs ys ys' Eys;
    induction xs, ys; intros ** H; inv H; inv Eys; auto.
  constructor; eauto.
  - eapply P_compat; eauto.
  - eapply IHxs; eauto.
Qed.

Add Parametric Morphism
    A B
  : (@List.map (Stream A) (Stream B))
    with signature (fun (f f': Stream A -> Stream B) => forall xs xs', xs ≡ xs' -> f xs ≡ f' xs') ==> @EqSts A ==> @EqSts B
      as map_st_EqSt.
Proof.
  intros f f' Ef xs xs' Exs.
  revert xs xs' Exs; induction xs, xs'; intros * H; inv H; constructor.
  - now apply Ef.
  - now apply IHxs.
Qed.

Add Parametric Morphism
    A B
  : (@List.map (Stream A) B)
    with signature (fun (f f': Stream A -> B) => forall xs xs', xs ≡ xs' -> f xs = f' xs') ==> @EqSts A ==> eq
      as map_EqSt.
Proof.
  intros f f' Ef xs xs' Exs.
  revert xs xs' Exs; induction xs, xs'; intros * H; inv H; auto.
  simpl; f_equal.
  - now apply Ef.
  - now apply IHxs.
Qed.

Add Parametric Morphism
    A P
    (P_compat: Proper (@EqSt A ==> Basics.impl) P)
  : (@Forall (Stream A) P)
    with signature @EqSts A ==> Basics.impl
      as Forall_EqSt.
Proof.
  induction x; intros * E H; inversion E; subst; auto.
  constructor; inv H.
  - eapply P_compat; eauto.
  - apply IHx; auto.
Qed.

CoFixpoint mask {A} (opaque: A) (k: nat) (rs: Stream bool) (xs: Stream A)
  : Stream A :=
  let mask' k' := mask opaque k' (tl rs) (tl xs) in
  match k, hd rs with
  | 0, true    => Streams.const opaque
  | 0, false   => hd xs  ::: mask' 0
  | 1, true    => hd xs  ::: mask' 0
  | S k', true => opaque ::: mask' k'
  | S _, false => opaque ::: mask' k
  end.

CoFixpoint count_acc (s: nat) (rs: Stream bool): Stream nat :=
  let s := if hd rs then S s else s in
  s ::: count_acc s (tl rs).

Definition count := count_acc 0.

Lemma count_acc_grow_trans:
  forall s s' rs,
    s' <= s ->
    ForAll (fun x => s' <= hd x) (count_acc s rs).
Proof.
  cofix Cofix; intros.
  constructor; simpl; destruct (hd rs); auto.
Qed.

Corollary count_acc_grow:
  forall s rs,
    ForAll (fun x => s <= hd x) (count_acc s rs).
Proof.
  intros; apply count_acc_grow_trans; auto.
Qed.

Lemma count_S_nth:
  forall n s rs,
    hd (Str_nth_tl n (count_acc (S s) rs)) =
    S (hd (Str_nth_tl n (count_acc s rs))).
Proof.
  unfold Str_nth.
  induction n; simpl; intros; destruct (hd rs); auto.
Qed.

Lemma mask_nth:
  forall {A} n (o: A) k rs xs,
    Str_nth n (mask o k rs xs) =
    if beq_nat (Str_nth n (count rs)) k then Str_nth n xs else o.
Proof.
  unfold Str_nth.
  induction n, k as [|[|k]]; intros;
    unfold_Stv rs; simpl; auto.
  - pose proof (count_acc_grow 1 rs) as H.
    apply (ForAll_Str_nth_tl n) in H; inv H.
    assert (hd (Str_nth_tl n (count_acc 1 rs)) <> 0) as E by omega;
      apply beq_nat_false_iff in E; rewrite E.
    pose proof (const_nth n o); auto.
  - rewrite IHn; unfold count.
    destruct (beq_nat (hd (Str_nth_tl n (count_acc 1 rs))) 1) eqn: E;
      rewrite count_S_nth in E.
    + apply beq_nat_true_iff, eq_add_S, beq_nat_true_iff in E; rewrite E; auto.
    + rewrite beq_nat_false_iff, Nat.succ_inj_wd_neg, <-beq_nat_false_iff in E;
        rewrite E; auto.
  - rewrite IHn; unfold count.
    destruct (beq_nat (hd (Str_nth_tl n (count_acc 1 rs))) (S (S k))) eqn: E;
      rewrite count_S_nth in E.
    + apply beq_nat_true_iff, eq_add_S, beq_nat_true_iff in E; rewrite E; auto.
    + rewrite beq_nat_false_iff, Nat.succ_inj_wd_neg, <-beq_nat_false_iff in E;
        rewrite E; auto.
Qed.

Remark mask_const_opaque:
  forall {A} n rs (opaque: A),
    mask opaque n rs (Streams.const opaque) ≡ Streams.const opaque.
Proof.
  cofix Cofix; intros.
  unfold_Stv rs; rewrite (unfold_Stream (Streams.const opaque));
    constructor; destruct n as [|[]]; simpl; auto; try apply Cofix.
  reflexivity.
Qed.