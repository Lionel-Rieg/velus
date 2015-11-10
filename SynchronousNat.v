Require Import Rustre.Common.
Require Import Rustre.DataflowSyntax.

Inductive value :=
  | absent
  | present (v : const).
(* Coercion present : const >-> value. *)

Definition stream A := nat -> A.
Definition vstream := stream value.
Definition cstream := stream bool.

(* Definition const {A} (a: A): stream A := fun _ => a.  *)

Lemma present_injection:
  forall x y, x = y <-> present x = present y.
Proof.
  split; intro H; [rewrite H|injection H]; auto.
Qed.

Lemma not_absent_present:
  forall x, x <> absent <-> exists c, x = present c.
Proof.
  intros x.
  split; intro HH.
  destruct x; [intuition|eauto].
  destruct HH as [c HH]; rewrite HH.
  intro; discriminate.
Qed.

(** Synchronous functions *)

(* With auxiliary hold function. *)


Inductive holdR (v0: const) (xs: stream value) : nat -> const -> Prop :=
| holdR0:
    holdR v0 xs 0 v0
| holdR_absent:
    forall v n,
      xs n = absent ->
      holdR v0 xs n v ->
      holdR v0 xs (S n) v
| holdR_present:
    forall n c,
      xs n = (present c) ->
      holdR v0 xs (S n) c.

Inductive fbyR (v0: const) (xs: stream value) : nat -> value -> Prop :=
| fbyR_absent:
    forall n,
      xs n = absent ->
      fbyR v0 xs n absent
| fbyR_present:
    forall c n v,
      xs n = v ->
      v <> absent ->
      holdR v0 xs n c ->
      fbyR v0 xs n (present c).

Fixpoint hold (v0: const) (xs: stream value) (n: nat) : const :=
  match n with
  | 0 => v0
  | S m => match xs m with
           | absent => hold v0 xs m
           | present hv => hv
           end
  end.

Definition fby (v0: const) (xs: stream value) (n: nat) : value :=
  match xs n with
  | absent => absent
  | _ => present (hold v0 xs n)
  end.

Lemma hold_rel1: forall v0 xs n, holdR v0 xs n (hold v0 xs n).
Proof.
  induction n.
  - cbv; auto using holdR0.
  - simpl. case_eq (xs n).
    + auto using holdR_absent.
    + intros v xsn.
      apply holdR_present.
      apply xsn.
Qed.

Lemma hold_rel2: forall v0 xs n c, holdR v0 xs n c -> hold v0 xs n = c.
Proof.
  induction n as [|n IH].
  - inversion 1; auto.
  - intros v H; inversion_clear H as [|? ? xsn HR|? H1 H2].
    + simpl; rewrite xsn; apply (IH v HR).
    + simpl. case_eq (xs n).
      rewrite H2; intro H1; discriminate H1.
      intros v1 H3; rewrite H3 in H2; injection H2.
      trivial.
Qed.

Lemma hold_rel: forall v0 xs n v, hold v0 xs n = v <-> holdR v0 xs n v.
Proof.
  split.
  intro H; rewrite <- H; apply hold_rel1.
  apply hold_rel2.
Qed.

Lemma fby_rel1: forall v0 xs n, fbyR v0 xs n (fby v0 xs n).
Proof.
  intros v0 xs n.
  unfold fby.
  case_eq (xs n).
  - auto using fbyR_absent.
  - intros v xsn.
    eapply fbyR_present; try eassumption || discriminate.
    apply hold_rel; reflexivity.
Qed.

Lemma fby_rel2: forall v0 xs n v, fbyR v0 xs n v -> fby v0 xs n = v.
Proof.
  induction n.
  - inversion_clear 1 as [ ? H0 | ? ? ? ? ? HR].
    + unfold fby; rewrite H0; reflexivity.
    + unfold fby; case_eq (xs 0).
      subst; contradiction.
      intros v2 xsn.
      apply hold_rel2 in HR; inversion HR.
      trivial.
  - inversion_clear 1 as [ ? H0 | ? ? ? ? ? HR].
    + unfold fby; rewrite H0; reflexivity.
    + unfold fby; case_eq (xs (S n)).
      subst; contradiction.
      intros v2 xsn.
      apply hold_rel2 in HR; inversion HR.
      trivial.
Qed.

Lemma fby_rel: forall v0 xs n v, fby v0 xs n = v <-> fbyR v0 xs n v.
Proof.
  split.
  intro H; rewrite <- H; apply fby_rel1.
  apply fby_rel2.
Qed.

Lemma holdR_ext:
  forall xs ys,
    (forall n, xs n = ys n)
    -> forall v0 n c,
      holdR v0 xs n c
      <-> holdR v0 ys n c.
Proof.
  intros xs ys Heq.
  induction n.
  - split; inversion 1; constructor.
  - intro c.
    split;
    (inversion 1 as [|? ? Hv Hhold|? ? Hv];
     (rewrite Heq in Hv || rewrite <- Heq in Hv);
     [ apply IHn in Hhold; now constructor
     | apply holdR_present with (1:=Hv) ]).
Qed.

Lemma fbyR_holdR:
  forall v0 xs n c,
    fbyR v0 xs n (present c)
    -> holdR v0 xs n c.
Proof.
  inversion 1; intuition.
Qed.

Lemma hold_injection:
  forall xs ys c n,
    (forall n, xs n = ys n)
    -> hold c xs n = hold c ys n.
Proof.
  intros xs ys c n Heq.
  induction n.
  auto.
  case_eq (xs n).
  intro Habs.
  assert (ys n = absent) as Habs' by (rewrite Heq in Habs; intuition).
  unfold hold.
  rewrite Habs. rewrite Habs'.
  fold hold.
  apply IHn.

  intros v Habs.
  assert (ys n = present v) as Habs' by (rewrite Heq in Habs; intuition).
  unfold hold.
  rewrite Habs. rewrite Habs'.
  reflexivity.
Qed.
