Require Import List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Arith.Compare_dec.

Require Import Coq.FSets.FMapPositive.
Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.RMemory.
Require Import Velus.NLustre.Stream.
Require Import Velus.NLustre.NLSyntax.
Require Import Velus.NLustre.IsVariable.
Require Import Velus.NLustre.IsDefined.
Require Import Velus.NLustre.NLSemantics.
Require Import Velus.NLustre.Ordered.
Require Import Velus.NLustre.WellFormed.
Require Import Velus.NLustre.Memories.
Require Import Velus.NLustre.IsFree.
Require Import Velus.NLustre.NoDup.

Set Implicit Arguments.

(** * The NLustre+Memory semantics *)

(**

  We provide a "non-standard" dataflow semantics where the state
  introduced by an [fby] is kept in a separate [memory] of
  streams. The only difference is therefore in the treatment of the
  [fby].

 *)


(* XXX: Is this comment still relevant?

   NB: The history H is not really necessary here. We could just as well
       replay all the semantic definitions using a valueEnv N ('N' for now),
       since all the historical information is in ms. This approach would
       have two advantages:

       1. Conceptually cleanliness: N corresponds more or less to the
          temporary variables in the Obc implementation (except that it
          would also contain values for variables defined by EqFby).

       2. No index needed to access values in when reasoning about
          translation correctness.

       But this approach requires more uninteresting definitions and
       and associated proofs of properties, and a longer proof of equivalence
       with sem_node: too much work for too little gain.
 *)

Module Type MEMSEMANTICS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Op)
       (Import Clks  : CLOCKS      Ids)
       (Import Syn   : NLSYNTAX    Ids Op       Clks)
       (Import Str   : STREAM             Op OpAux)
       (Import Ord   : ORDERED     Ids Op       Clks Syn)
       (Import Sem   : NLSEMANTICS Ids Op OpAux Clks Syn Str Ord)
       (Import Mem   : MEMORIES    Ids Op       Clks Syn)
       (Import IsD   : ISDEFINED   Ids Op       Clks Syn         Mem)
       (Import IsV   : ISVARIABLE  Ids Op       Clks Syn         Mem IsD)
       (Import IsF   : ISFREE      Ids Op       Clks Syn)
       (Import NoD   : NODUP       Ids Op       Clks Syn         Mem IsD IsV)
       (Import WeF   : WELLFORMED  Ids Op       Clks Syn     Ord Mem IsD IsV IsF NoD).

  Definition memory := memory (stream val).

 Definition mask' {A} (k: nat) (rs: cstream) (xs ys: stream A) : Prop :=
    ys 0 = xs 0
    (* /\ forall n, ys n = if EqNat.beq_nat k (count rs n) then xs n else ys (pred n). *)
    /\ forall n, ys n = match nat_compare (count rs n) k with
                     | Lt => xs 0
                     | Eq => xs (if rs n then 0 else n)
                     | Gt => if EqNat.beq_nat (count rs n) (S k) && rs n
                            then xs n else ys (pred n)
                     end.

  (* Definition mask' {A} (k: nat) (rs: cstream) (xs: stream A) : stream A := *)
  (*   fun n => *)
  (*     xs match nat_compare (count rs n) k with *)
  (*        | Lt => 0 *)
  (*        | Eq => if rs n then 0 else n *)
  (*        | Gt => n *)
  (*        end. *)

  (* Lemma mask'_0: *)
  (*   forall {A} k rs (xs: stream A), *)
  (*     mask' k rs xs 0 = xs 0. *)
  (* Proof. *)
  (*   intros; unfold mask'. *)
  (*   destruct (nat_compare (count rs 0) k); auto. *)
  (*   destruct (rs 0); auto. *)
  (* Qed. *)

  (* Lemma mask'_spec: *)
  (*   forall {A} k rs (xs: stream A), *)
  (*     mask'' k rs xs (mask' k rs xs). *)
  (* Proof. *)
  (*   split; auto. *)
  (*   apply mask'_0. *)
  (* Qed. *)

  (* match nat_compare (count rs n) k with *)
  (*          | Eq => ys n = xs n *)
  (*          | Lt => ys n = xs 0 *)
  (*          | Gt => ys n = ys (pred n) *)
  (*          end. *)

  Definition mmask (k: nat) (rs: cstream) (M M': memory) : Prop :=
    forall x ms,
      mfind_mem x M = Some ms ->
      exists ms',
        mfind_mem x M' = Some ms'
        /\ mask' k rs ms ms'.

  Inductive mfby: ident -> val -> stream value -> memory -> stream value -> Prop :=
    mfby_intro:
      forall x v0 ls M xs ms,
        mfind_mem x M = Some ms ->
        ms 0 = v0 ->
        (forall n, match ls n with
              | absent    => ms (S n) = ms n /\ xs n = absent
              | present v => ms (S n) = v    /\ xs n = present (ms n)
              end) ->
        mfby x v0 ls M xs.

  (* Lemma mask'_S: *)
  (*   forall {A} k rs (xs ys: stream A) n, *)
  (*     mask' k rs xs ys -> *)
  (*     (count rs n = k ->  *)
  (*      ys (S n) = xs (S n) \/ ys (S n) = ys n. *)
  (* Admitted. *)

  (* Lemma count_S: *)
  (*   forall k rs n, *)
  (*     k = count rs n -> *)
  (*     k <= count rs (S n). *)
  (* Proof. *)
  (*   intros ** E; simpl; rewrite E. *)
  (*   destruct (rs (S n)); omega. *)
  (* Qed. *)

  Lemma foo:
    forall x v0 ls M xs k rs M',
      mfby x v0 ls M xs ->
      (forall ms,
          mfind_mem x M = Some ms ->
          forall n,
            rs n = true ->
            ms n = v0) ->
      mmask k rs M M' ->
      mfby x v0 (mask absent k rs ls) M' (mask absent k rs xs).
  Proof.
    intros ** Fby Rst Mask.
    inversion_clear Fby as [?????? Find ? Spec].
    specialize (Rst _ Find).
    apply Mask in Find as (ms' & Find & Mask').
    inversion Mask' as (Hinit & Spec').
    econstructor; eauto.
    - now rewrite Hinit.
    - pose proof Spec' as SpecS;
        intro n; specialize (Spec n); specialize (Spec' n);
          specialize (SpecS (S n));  simpl in *; specialize (Rst n).
      unfold mask.
      destruct (nat_compare (count rs n) k) eqn: E; rewrite SpecS; clear SpecS.
      + assert (EqNat.beq_nat k (count rs n) = true) as ->
            by now rewrite NPeano.Nat.eqb_sym, EqNat.beq_nat_true_iff,
               <-nat_compare_eq_iff.
        destruct (rs (S n)).
        *{ assert (nat_compare (S (count rs n)) k = Gt) as ->
               by (rewrite <-nat_compare_gt; apply Gt.le_gt_S;
                   apply nat_compare_eq_iff in E; omega).
           assert (EqNat.beq_nat (S (count rs n)) (S k) = true) as ->
               by now apply EqNat.beq_nat_true_iff, eq_sym,
                  eq_S, EqNat.beq_nat_true_iff; simpl.
           destruct (ls n), (rs n); intuition;
             try rewrite Spec'; auto.
           - now rewrite H3, H5.
           - now rewrite H, <-H5.
         }
        *{ rewrite E.
           destruct (ls n), (rs n); intuition;
             try rewrite Spec'; auto.
           - now rewrite H1, H.
           - now rewrite H, <-H3.
         }
      + assert (EqNat.beq_nat k (count rs n) = false) as ->
            by (apply nat_compare_lt in E; apply EqNat.beq_nat_false_iff;
                intro; subst; omega).
        destruct (rs (S n)).
        * destruct (nat_compare (S (count rs n)) k) eqn: E'; intuition;
            try rewrite Spec'; auto.
          apply nat_compare_lt in E; apply nat_compare_gt in E'; omega.
        * now rewrite E.
      + assert (EqNat.beq_nat k (count rs n) = false) as ->
            by (apply nat_compare_gt in E; apply EqNat.beq_nat_false_iff;
                intro; subst; omega).
        destruct (rs (S n)).
        * assert (nat_compare (S (count rs n)) k = Gt) as ->
              by (rewrite <-nat_compare_gt in *; omega).
          assert (EqNat.beq_nat (S (count rs n)) (S k) = false) as ->
              by now apply EqNat.beq_nat_false_iff, not_eq_S,
                 not_eq_sym, EqNat.beq_nat_false_iff.
          now rewrite Bool.andb_false_l.
        * now rewrite E, Bool.andb_false_r.
  Qed.

  Implicit Type M : memory.

  Section NodeSemantics.

    Variable G: global.

    Inductive msem_equation: stream bool -> history -> memory -> equation -> Prop :=
    | SEqDef:
        forall bk H M x ck xs ce,
          sem_var bk H x xs ->
          sem_caexp bk H ck ce xs ->
          msem_equation bk H M (EqDef x ck ce)
    | SEqApp:
        forall bk H M x xs ck f M' arg ls xss,
          Some x = hd_error xs ->
          mfind_inst x M = Some M' ->
          sem_laexps bk H ck arg ls ->
          sem_vars bk H xs xss ->
          msem_node f ls M' xss ->
          msem_equation bk H M (EqApp xs ck f arg None)
    | SEqReset:
        forall bk H M x xs ck f M' arg y ck_r ys ls xss,
          Some x = hd_error xs ->
          mfind_inst x M = Some M' ->
          sem_laexps bk H ck arg ls ->
          sem_vars bk H xs xss ->
          sem_var bk H y ys ->
          msem_reset f (reset_of ys) ls M' xss ->
          msem_equation bk H M (EqApp xs ck f arg (Some (y, ck_r)))
    | SEqFby:
        forall bk H M x ck ls xs c0 le,
          sem_laexp bk H ck le ls ->
          sem_var bk H x xs ->
          mfby x (sem_const c0) ls M xs ->
          msem_equation bk H M (EqFby x ck c0 le)

    with msem_reset: ident -> stream bool -> stream (list value) -> memory -> stream (list value) -> Prop :=
         | SReset:
             forall f r xss M yss,
               (forall n, exists M',
                     mmask n r M M'
                     /\ msem_node f
                                 (mask (all_absent (xss 0)) n r xss)
                                 M'
                                 (mask (all_absent (yss 0)) n r yss)) ->
               msem_reset f r xss M yss

    with msem_node:
           ident -> stream (list value) -> memory -> stream (list value) -> Prop :=
         | SNode:
             forall bk H f xss M yss n,
               clock_of xss bk ->
               find_node f G = Some n ->
               sem_vars bk H (map fst n.(n_in)) xss ->
               sem_vars bk H (map fst n.(n_out)) yss ->
               same_clock xss ->
               same_clock yss ->
               (forall n, absent_list (xss n) <-> absent_list (yss n)) ->
               Forall (msem_equation bk H M) n.(n_eqs) ->
               msem_node f xss M yss.

    Definition msem_equations bk H M eqs := Forall (msem_equation bk H M) eqs.

  End NodeSemantics.

  (** ** Induction principle for [msem_equation] and [msem_node] *)

  (** The automagically-generated induction principle is not strong
enough: it does not support the internal fixpoint introduced by
[Forall] *)

  Section msem_node_mult.

    Variable G: global.

    Variable P_equation: stream bool -> history -> memory -> equation -> Prop.
    Variable P_reset: ident -> stream bool -> stream (list value) -> memory -> stream (list value) -> Prop.
    Variable P_node: ident -> stream (list value) -> memory -> stream (list value) -> Prop.

    Hypothesis EqDefCase:
      forall bk H M x ck xs ce,
        sem_var bk H x xs ->
        sem_caexp bk H ck ce xs ->
        P_equation bk H M (EqDef x ck ce).

    Hypothesis EqAppCase:
      forall bk H M x xs ck f M' arg ls xss,
        Some x = hd_error xs ->
        mfind_inst x M = Some M' ->
        sem_laexps bk H ck arg ls ->
        sem_vars bk H xs xss ->
        msem_node G f ls M' xss ->
        P_node f ls M' xss ->
        P_equation bk H M (EqApp xs ck f arg None).

    Hypothesis EqResetCase:
      forall bk H M x xs ck f M' arg y ck_r ys ls xss,
        Some x = hd_error xs ->
        mfind_inst x M = Some M' ->
        sem_laexps bk H ck arg ls ->
        sem_vars bk H xs xss ->
        sem_var bk H y ys ->
        msem_reset G f (reset_of ys) ls M' xss ->
        P_reset f (reset_of ys) ls M' xss ->
        P_equation bk H M (EqApp xs ck f arg (Some (y, ck_r))).

    Hypothesis EqFbyCase:
      forall bk H M x ck ls xs c0 le,
        sem_laexp bk H ck le ls ->
        sem_var bk H x xs ->
        mfby x (sem_const c0) ls M xs ->
        P_equation bk H M (EqFby x ck c0 le).

    Hypothesis ResetCase:
      forall f r xss M yss,
        (forall n, exists M',
              mmask n r M M'
              /\ msem_node G f
                          (mask (all_absent (xss 0)) n r xss)
                          M'
                          (mask (all_absent (yss 0)) n r yss)) ->
        (forall n, exists M',
              mmask n r M M'
              /\ P_node f
                       (mask (all_absent (xss 0)) n r xss)
                       M'
                       (mask (all_absent (yss 0)) n r yss)) ->
        P_reset f r xss M yss.

    Hypothesis NodeCase:
      forall bk H f xss M yss n,
        clock_of xss bk ->
        find_node f G = Some n ->
        sem_vars bk H (map fst n.(n_in)) xss ->
        sem_vars bk H (map fst n.(n_out)) yss ->
        same_clock xss ->
        same_clock yss ->
        (forall n, absent_list (xss n) <-> absent_list (yss n)) ->
        Forall (msem_equation G bk H M) n.(n_eqs) ->
        Forall (P_equation bk H M) n.(n_eqs) ->
        P_node f xss M yss.

    Fixpoint msem_equation_mult
             (b: stream bool) (H: history) (M: memory) (e: equation)
             (Sem: msem_equation G b H M e) {struct Sem}
      : P_equation b H M e
    with msem_reset_mult
           (f: ident) (r: stream bool)
           (xss: stream (list value))
           (M: memory)
           (oss: stream (list value))
           (Sem: msem_reset G f r xss M oss) {struct Sem}
         : P_reset f r xss M oss
    with msem_node_mult
           (f: ident)
           (xss: stream (list value))
           (M: memory)
           (oss: stream (list value))
           (Sem: msem_node G f xss M oss) {struct Sem}
         : P_node f xss M oss.
    Proof.
      - destruct Sem; eauto.
      - destruct Sem; eauto.
        apply ResetCase; intro n; destruct (H n); econstructor; intuition; eauto.
      - destruct Sem; eauto.
        eapply NodeCase; eauto.
        (* clear H1 defd vout good. *)
        induction H7; auto.
    Qed.

    Combined Scheme msem_equation_node_ind from msem_equation_mult, msem_node_mult, msem_reset_mult.

  End msem_node_mult.

  Definition msem_nodes (G: global) : Prop :=
    Forall (fun no => exists xs M ys, msem_node G no.(n_name) xs M ys) G.

  (** ** Properties *)

  (** *** Equation non-activation *)

  (* Lemma subrate_property_eqn: *)
  (*   forall G H M bk xss eqn n, *)
  (*     clock_of xss bk -> *)
  (*     msem_equation G bk H M eqn -> *)
  (*     0 < length (xss n) -> *)
  (*     absent_list (xss n) -> *)
  (*     rhs_absent_instant (bk n) (restr H n) eqn. *)
  (* Proof. *)
  (*   intros * Hck Hsem Hlen Habs. *)
  (*   assert (Hbk: bk n = false). *)
  (*   { *)
  (*     destruct (Bool.bool_dec (bk n) false) as [Hbk | Hbk]; eauto. *)
  (*     exfalso. *)
  (*     apply Bool.not_false_is_true in Hbk. *)
  (*     eapply Hck in Hbk. *)
  (*     eapply not_absent_present_list in Hbk; auto. *)
  (*   } *)
  (*   rewrite Hbk in *. *)
  (*   destruct eqn. *)
  (*   constructor. *)
  (*   apply SCabs; try apply subrate_clock. *)

  (*   ; *)
  (*     try repeat *)
  (*         match goal with *)
  (*         | |- rhs_absent_instant false _ (EqDef _ _ _) => *)
  (*           constructor *)
  (*         | |- rhs_absent_instant false _ (EqFby _ _ _ _) => *)
  (*           constructor *)
  (*         | |- sem_caexp_instant false _ ?ck ?ce absent => *)
  (*           apply SCabs *)
  (*         | |- sem_clock_instant false _ ?ck false => *)
  (*           apply subrate_clock *)
  (*         | |- sem_laexp_instant false _ ?ck ?le absent => *)
  (*           apply SLabs *)
  (*         | |- sem_laexps_instant false _ ?ck ?les _ => *)
  (*           apply SLabss; eauto *)
  (*         end. *)
  (*   clear Hsem Habs. *)
  (*   apply AEqApp with (vs:=map (fun _ =>absent) l). *)
  (*   apply SLabss; auto. apply subrate_clock. *)
  (*   induction l; [constructor|]. *)
  (*   apply Forall_cons; auto. *)
  (* Qed. *)

  (* Lemma subrate_property_eqns: *)
  (*   forall G H M bk xss eqns n, *)
  (*     clock_of xss bk -> *)
  (*     msem_equations G bk H M eqns -> *)
  (*     0 < length (xss n) -> *)
  (*     absent_list (xss n) -> *)
  (*     Forall (rhs_absent_instant (bk n) (restr H n)) eqns. *)
  (* Proof. *)
  (*   intros * Hck Hsem Habs. *)
  (*   induction eqns as [|eqn eqns]; auto. *)
  (*   inversion_clear Hsem. *)
  (*   constructor. *)
  (*   eapply subrate_property_eqn; eauto. *)
  (*   eapply IHeqns; eauto. *)
  (* Qed. *)

  (** *** Environment cons-ing lemmas *)

  (* Instead of repeating all these cons lemmas (i.e., copying and pasting them),
   and dealing with similar obligations multiple times in translation_correct,
   maybe it would be better to bake Ordered_nodes into msem_node and to make
   it like Miniimp, i.e.,
      find_node f G = Some (nd, G') and msem_node G' nd xs ys ?
   TODO: try this when the other elements are stabilised. *)

  Lemma msem_node_cons:
    forall n G f xs M ys,
      Ordered_nodes (n :: G) ->
      msem_node (n :: G) f xs M ys ->
      n.(n_name) <> f ->
      msem_node G f xs M ys.
  Proof.
    Hint Constructors msem_equation msem_reset.
    intros ** Hord Hsem Hnf.
    revert Hnf.
    induction Hsem as [| | | |?????? IH |???????? Hf ?????? IH ]
        using msem_node_mult
      with (P_equation := fun bk H M eq =>
                            ~Is_node_in_eq n.(n_name) eq ->
                            msem_equation G bk H M eq)
           (P_reset := fun f r xss M yss =>
                         n_name n <> f ->
                         msem_reset G f r xss M yss); eauto.
    - intro Hnin.
      econstructor; eauto.
      apply IHHsem. intro Hnf; apply Hnin; rewrite Hnf. constructor.
    - intro Hnin.
      econstructor; eauto.
      apply IHHsem. intro Hnf; apply Hnin; rewrite Hnf. constructor.
    - intro; econstructor.
      intro k; destruct (IH k); econstructor; intuition; eauto.
    - intro.
      rewrite find_node_tl with (1:=Hnf) in Hf.
      econstructor; eauto.
      apply find_node_later_not_Is_node_in with (2:=Hf) in Hord.
      apply Is_node_in_Forall in Hord.
      apply Forall_Forall with (1:=Hord) in IH.
      apply Forall_impl with (2:=IH).
      intuition.
  Qed.

  Corollary msem_reset_cons:
    forall n G f r xs M ys,
      Ordered_nodes (n :: G) ->
      msem_reset (n :: G) f r xs M ys ->
      n.(n_name) <> f ->
      msem_reset G f r xs M ys.
  Proof.
    intros ** Sem ?.
    inversion_clear Sem as [????? SemN].
    constructor; intro k.
    destruct (SemN k).
    intuition; eauto using msem_node_cons.
  Qed.

  Lemma msem_node_cons2:
    forall n G f xs M ys,
      Ordered_nodes G ->
      msem_node G f xs M ys ->
      Forall (fun n' => n_name n <> n_name n') G ->
      msem_node (n :: G) f xs M ys.
  Proof.
    Hint Constructors msem_equation.
    intros ** Hord Hsem Hnin.
    assert (Hnin':=Hnin).
    revert Hnin'.
    induction Hsem as [| | | |?????? IH|?????? n' ? Hfind ????? Heqs IH]
        using msem_node_mult
      with (P_equation := fun bk H M eq =>
                            ~Is_node_in_eq n.(n_name) eq ->
                            msem_equation (n :: G) bk H M eq)
           (P_reset := fun f r xss M yss =>
                         Forall (fun n' : node => n_name n <> n_name n') G ->
                         msem_reset (n :: G) f r xss M yss); eauto.
    - intros; constructor; intro k.
      destruct (IH k); intuition; eauto.
    - intro HH; clear HH.
      assert (n.(n_name) <> f) as Hnf.
      { intro Hnf.
        rewrite Hnf in *.
        pose proof (find_node_name _ _ _ Hfind).
        apply find_node_split in Hfind.
        destruct Hfind as [bG [aG Hge]].
        rewrite Hge in Hnin.
        apply Forall_app in Hnin.
        destruct Hnin as [H' Hfg]; clear H'.
        inversion_clear Hfg.
        match goal with H:f<>_ |- False => now apply H end.
      }
      apply find_node_other with (2:=Hfind) in Hnf.
      econstructor; eauto.
      assert (forall g, Is_node_in g n'.(n_eqs) -> Exists (fun nd=> g = nd.(n_name)) G)
        as Hniex by (intros g Hini;
                     apply find_node_find_again with (1:=Hord) (2:=Hfind) in Hini;
                     exact Hini).
      assert (Forall (fun eq => forall g,
                          Is_node_in_eq g eq -> Exists (fun nd=> g = nd.(n_name)) G)
                     n'.(n_eqs)) as HH.
      {
        clear Heqs IH.
        induction n'.(n_eqs) as [|eq eqs]; [now constructor|].
        constructor.
        - intros g Hini.
          apply Hniex.
          constructor 1; apply Hini.
        - apply IHeqs.
          intros g Hini; apply Hniex.
          constructor 2; apply Hini.
      }
      apply Forall_Forall with (1:=HH) in IH.
      apply Forall_impl with (2:=IH).
      intros eq (Hsem & IH1).
      apply IH1.
      intro Hini.
      apply Hsem in Hini.
      apply Forall_Exists with (1:=Hnin) in Hini.
      apply Exists_exists in Hini.
      destruct Hini as [nd' [Hin [Hneq Heq]]].
      intuition.
  Qed.

  Lemma msem_reset_cons2:
    forall n G f r xs M ys,
      Ordered_nodes G ->
      msem_reset G f r xs M ys ->
      Forall (fun n' => n_name n <> n_name n') G ->
      msem_reset (n :: G) f r xs M ys.
  Proof.
    intros ** Sem ?.
    inversion_clear Sem as [????? SemN].
    constructor; intro k.
    destruct (SemN k).
    intuition; eauto using msem_node_cons2.
  Qed.

  Lemma msem_equation_cons2:
    forall G bk H M eqs n,
      Ordered_nodes (n :: G) ->
      Forall (msem_equation G bk H M) eqs ->
      ~Is_node_in n.(n_name) eqs ->
      Forall (msem_equation (n :: G) bk H M) eqs.
  Proof.
    Hint Constructors msem_equation.
    intros ** Hord Hsem Hnini.
    induction eqs as [|eq eqs IH]; [now constructor|].
    apply Forall_cons2 in Hsem.
    destruct Hsem as [Heq Heqs].
    apply not_Is_node_in_cons in Hnini.
    destruct Hnini as [Hnini Hninis].
    apply IH with (2:=Hninis) in Heqs.
    constructor; [|now apply Heqs].
    inv Hord.
    destruct Heq as [| |? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hmsem|];
      try now eauto.
    - eauto using msem_node_cons2.
    - eauto using msem_reset_cons2.
  Qed.

  Lemma find_node_msem_node:
    forall G f,
      msem_nodes G ->
      find_node f G <> None ->
      exists xs M ys,
        msem_node G f xs M ys.
  Proof.
    intros G f Hnds Hfind.
    apply find_node_Exists in Hfind.
    apply Exists_exists in Hfind.
    destruct Hfind as [nd [Hin Hf]].
    unfold msem_nodes in Hnds.
    rewrite Forall_forall in Hnds.
    apply Hnds in Hin.
    destruct Hin as [xs [M [ys Hmsem]]].
    exists xs; exists M; exists ys.
    rewrite Hf in *.
    exact Hmsem.
  Qed.

  (* TODO: Tidy this up... *)
  Lemma Forall_msem_equation_global_tl:
    forall n G bk H M eqs,
      Ordered_nodes (n :: G) ->
      (forall f, Is_node_in f eqs -> find_node f G <> None) ->
      ~ Is_node_in n.(n_name) eqs ->
      Forall (msem_equation (n :: G) bk H M) eqs ->
      Forall (msem_equation G bk H M) eqs.
  Proof.
    intros ? ? ? ? ? ? Hord.
    induction eqs as [|eq eqs IH]; trivial; [].
    intros Hfind Hnini Hmsem.
    apply Forall_cons2 in Hmsem; destruct Hmsem as [Hseq Hseqs].
    apply IH in Hseqs.
    - apply Forall_cons; trivial.
      apply not_Is_node_in_cons in Hnini.
      destruct Hnini.
      inv Hseq; eauto;
        assert (n.(n_name) <> f)
        by (intro HH; apply H0; rewrite HH; constructor).
      + eauto using msem_node_cons.
      + eauto using msem_reset_cons.
    - intros f Hini.
      apply (Exists_cons_tl eq) in Hini.
      now apply (Hfind _ Hini).
    - apply not_Is_node_in_cons in Hnini.
      now destruct Hnini.
  Qed.

  (** *** Memory management *)

  Lemma mfby_madd_mem:
    forall x v0 ls M xs y ms,
      x <> y ->
      mfby x v0 ls M xs ->
      mfby x v0 ls (madd_mem y ms M) xs.
  Proof.
    inversion 2; econstructor; eauto.
    rewrite mfind_mem_gso; auto.
  Qed.

  Lemma mfby_madd_obj:
    forall x v0 ls M xs y M',
      mfby x v0 ls M xs ->
      mfby x v0 ls (madd_obj y M' M) xs.
  Proof.
    inversion 1; econstructor; eauto.
  Qed.

  Hint Resolve mfby_madd_mem mfby_madd_obj.

  Lemma msem_equation_madd_mem:
    forall G bk H M x ms eqs,
      ~Is_defined_in_eqs x eqs ->
      Forall (msem_equation G bk H M) eqs ->
      Forall (msem_equation G bk H (madd_mem x ms M)) eqs.
  Proof.
    Hint Constructors msem_equation.
    intros ** Hnd Hsem.
    induction eqs as [|eq eqs IH]; [now constructor|].
    apply not_Is_defined_in_cons in Hnd.
    destruct Hnd as [Hnd Hnds].
    apply Forall_cons2 in Hsem.
    destruct Hsem as [Hsem Hsems].
    constructor; [|now apply IH with (1:=Hnds) (2:=Hsems)].
    destruct Hsem; eauto.
    apply not_Is_defined_in_eq_EqFby in Hnd.
    eapply SEqFby; eauto.
  Qed.

  Lemma msem_equation_madd_obj:
    forall G bk H M M' x eqs,
      ~Is_defined_in_eqs x eqs ->
      Forall (msem_equation G bk H M) eqs ->
      Forall (msem_equation G bk H (madd_obj x M' M)) eqs.
  Proof.
    Hint Constructors msem_equation.
    intros * Hnd Hsem.
    induction eqs as [|eq eqs IH]; [now constructor|].
    apply not_Is_defined_in_cons in Hnd.
    destruct Hnd as [Hnd Hnds].
    apply Forall_cons2 in Hsem.
    destruct Hsem as [Hsem Hsems].
    constructor; [|now apply IH with (1:=Hnds) (2:=Hsems)].
    destruct Hsem as [|? ? ? x' ? ? ? ? ? ? ? Hsome
                         |? ? ? x' ? ? ? ? ? ? ? ? ? ? Hsome|];
      eauto;
      assert (mfind_inst x' (madd_obj x M' M) = Some M'0)
        by (apply not_Is_defined_in_eq_EqApp in Hnd;
            rewrite mfind_inst_gso; auto;
            intro; subst x; destruct xs; inv Hsome; apply Hnd; now constructor);
      eauto.
  Qed.

  (* XXX: I believe that this comment is outdated ([no_dup_defs] is long gone)

   - The no_dup_defs hypothesis is essential for the EqApp case.

     If the set of equations contains two EqApp's to the same variable:
        eq::eqs = [ EqApp x f lae; ...; EqApp x g lae' ]

     Then it is possible to have a coherent H, namely if
        f(lae) = g(lae')

     But nothing forces the 'memory streams' (internal memories) of
     f(lae) and g(lae') to be the same. This is problematic since they are
     both 'stored' at M x...

   - The no_dup_defs hypothesis is not essential for the EqFby case.

     If the set of equations contains two EqFby's to for the same variable:
        eq::eqs = [ EqFby x v0 lae; ...; EqFby x v0' lae'; ... ]

     then the 'memory streams' associated with each, ms and ms', must be
     identical since if (Forall (sem_equation G H) (eq::eqs)) exists then
     then the H forces the coherence between 'both' x's, and necessarily also
     between v0 and v0', and lae and lae'.

     That said, proving this result is harder than just assuming something
     that should be true anyway: that there are no duplicate definitions in
     eqs.

   Note that the no_dup_defs hypothesis requires a stronger definition of
   either Is_well_sch or Welldef_global.
   *)

  (** ** Fundamental theorem *)

  (**

We show that the standard semantics implies the existence of a
dataflow memory for which the non-standard semantics holds true.

   *)

  Lemma sem_msem_eq:
    forall G bk H eqs M eq mems argIn,
      (forall f xs ys,
          sem_node G f xs ys ->
          exists M, msem_node G f xs M ys) ->
      (forall f r xs ys,
          sem_reset G f r xs ys ->
          exists M, msem_reset G f r xs M ys) ->
      sem_equation G bk H eq ->
      Is_well_sch mems argIn (eq :: eqs) ->
      Forall (msem_equation G bk H M) eqs ->
      exists M', Forall (msem_equation G bk H M') (eq :: eqs).
  Proof.
    intros ** IH IH' Heq Hwsch Hmeqs.
    inversion Heq as [|? ? ? ? ? ? ? ? Hls Hxs Hsem
                         |? ? ? ? ? ? ? ? ? ? ? Hls Hxs Hy Hsem
                         |? ? ? ? ? ? ? ? Hle Hvar];
      match goal with H:_=eq |- _ => rewrite <-H in * end.
    - exists M.
      repeat (econstructor; eauto).
    - apply IH in Hsem as [M' Hmsem].
      exists (madd_obj (hd Ids.default x) M' M).

      assert (exists i, Some i = hd_error x) as [i Hsome].
      {
        assert (Hlen: 0 < length x).
        {
          assert (length x = length (xs 0))
            by (specialize (Hxs 0); simpl in Hxs; eapply Forall2_length; eauto).

          assert (exists n, length (map fst n.(n_out)) = length (xs 0)
                       /\ 0 < length n.(n_out)) as (n & ? & ?).
          {
            inv Hmsem.
            exists n; split; auto.
            - eapply Forall2_length; eauto.
            - exact n.(n_outgt0).
          }

          assert (length (map fst n.(n_out)) = length n.(n_out))
            by apply map_length.

          intuition.
        }

        destruct x; try now inv Hlen.
        eexists; simpl; eauto.
      }

      assert (Hhd: hd Ids.default x = i).
      {
        destruct x; simpl in *; try discriminate.
        injection Hsome; congruence.
      }
      rewrite Hhd; clear Hhd.

      constructor.
      + econstructor; eauto.
        now apply mfind_inst_gss.
      + inversion_clear Hwsch.
        assert (Is_defined_in_eq i (EqApp x ck f arg None)).
        {
          constructor. destruct x; try discriminate.
          injection Hsome. intro; subst i. constructor (auto).
        }
        now apply msem_equation_madd_obj; auto.

    - pose proof Hsem as Hsem'.
      apply IH' in Hsem as [M' Hmsem].
      exists (madd_obj (hd Ids.default x) M' M).

      assert (exists i, Some i = hd_error x) as [i Hsome].
      {
        assert (Hlen: 0 < length x).
        {
          assert (length x = length (xs 0))
            by (specialize (Hxs 0); simpl in Hxs; eapply Forall2_length; eauto).

          assert (exists n, length (map fst n.(n_out)) = length (xs 0)
                       /\ 0 < length n.(n_out)) as (n & ? & ?).
          {
            inversion_clear Hmsem as [? ? ? ? ? Hmsem'].
            destruct (Hmsem' 0) as (? & ? & Hmsem); inv Hmsem.
            exists n; split; auto.
            - unfold sem_vars, lift in H10; specialize (H10 0).
              apply Forall2_length in H10; rewrite H10.
              rewrite mask_length; auto.
              inversion_clear Hsem' as [? ? ? ? Hsem].
              eapply wf_streams_mask.
              intro n'; specialize (Hsem n');
                apply sem_node_wf in Hsem as (? & ?); eauto.
            - exact n.(n_outgt0).
          }

          assert (length (map fst n.(n_out)) = length n.(n_out))
            by apply map_length.

          intuition.
        }

        destruct x; try now inv Hlen.
        eexists; simpl; eauto.
      }

      assert (Hhd: hd Ids.default x = i).
      {
        destruct x; simpl in *; try discriminate.
        injection Hsome; congruence.
      }

      rewrite Hhd; clear Hhd.

      constructor.
      + econstructor; eauto.
        now apply mfind_inst_gss.
      + inversion_clear Hwsch.
        assert (Is_defined_in_eq i (EqApp x ck f arg (Some (y, ck_r)))).
        {
          constructor. destruct x; try discriminate.
          injection Hsome. intro; subst i. constructor (auto).
        }
        apply msem_equation_madd_obj; auto.

    - exists (madd_mem x (hold (sem_const c0) ls) M).
      constructor.
      + do 2 (econstructor; eauto).
        * now apply mfind_mem_gss.
        * reflexivity.
        * rewrite H1; unfold fby; simpl.
          intro n; destruct (ls n); auto.
      + inversion_clear Hwsch.
        apply msem_equation_madd_mem; eauto.
  Qed.

  (* XXX: for this lemma, and the ones before/after it, factorize 'G',
'bk' and possibly other variables in a Section *)
  Corollary sem_msem_eqs:
    forall G bk H eqs mems argIn,
      (forall f xs ys,
          sem_node G f xs ys ->
          exists M, msem_node G f xs M ys) ->
      (forall f r xs ys,
          sem_reset G f r xs ys ->
          exists M, msem_reset G f r xs M ys) ->
      Is_well_sch mems argIn eqs ->
      Forall (sem_equation G bk H) eqs ->
      exists M', Forall (msem_equation G bk H M') eqs.
  Proof.
    intros ** IH Hwsch Heqs.
    induction eqs as [|eq eqs IHeqs]; [exists (empty_memory _); now constructor|].
    apply Forall_cons2 in Heqs as [Heq Heqs].
    eapply IHeqs with (1:=Is_well_sch_cons _ _ _ _ Hwsch)
      in Heqs
      as [M Heqs]; eauto.
    eapply sem_msem_eq; eauto.
  Qed.

  Theorem sem_msem_node:
    forall G f xs ys,
      Welldef_global G ->
      sem_node G f xs ys ->
      exists M, msem_node G f xs M ys.
  Proof.
    induction G as [|node].
    inversion 2;
      match goal with Hf: find_node _ [] = _ |- _ => inversion Hf end.
    intros ** Hwdef Hsem.
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [??????? Hfind ????? Heqs].
    pose proof (Welldef_global_Ordered_nodes _ Hwdef) as Hord.
    pose proof (Welldef_global_cons _ _ Hwdef) as HwdefG.
    pose proof (find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    simpl in Hfind.
    destruct (ident_eqb node.(n_name) f) eqn:Hnf.
    - assert (Hord':=Hord).
      inversion_clear Hord as [|? ? Hord'' Hnneqs Hnn].
      injection Hfind; intro HR; rewrite HR in *; clear HR; simpl in *.
      eapply Forall_sem_equation_global_tl in Heqs; eauto.
      assert (forall f xs ys,
                 sem_node G f xs ys ->
                 exists M, msem_node G f xs M ys) as IHG'
          by auto.
      assert (forall f r xs ys,
                 sem_reset G f r xs ys ->
                 exists M, msem_reset G f r xs M ys) as IHG''.
      { clear - IHG'.
        intros ** Sem.
        inversion_clear Sem as [???? Sem'].
        (* eexists. *)
        (* constructor. *)
        admit.
      }
      inversion_clear Hwdef as [|??? neqs].
      simpl in neqs; unfold neqs in *.
      assert (exists M', Forall (msem_equation G bk H M') n.(n_eqs))
        as (M & Hmsem) by now eapply sem_msem_eqs; eauto.
      exists M.
      econstructor; eauto.
      + simpl; now rewrite Hnf.
      + eapply msem_equation_cons2; eauto.
    - apply ident_eqb_neq in Hnf.
      apply sem_node_cons with (1:=Hord) (3:=Hnf) in Hsem.
      inv Hord.
      eapply IHG in Hsem as [M]; eauto.
      exists M.
      now eapply msem_node_cons2; eauto.
  Qed.

  (* We use the mem-semantics to assert the absence of applications
  with no return arguments. This is a bit of a hack, if you ask me. So
  don't ask. *)
  Lemma non_trivial_EqApp:
    forall G bk H M eqs ,
      Forall (msem_equation G bk H M) eqs ->
      forall ck f les y, ~ In (EqApp [] ck f les y) eqs.
  Proof.
  induction eqs; intros ** Hsem ? ? ? ? Hin.
  - match goal with
    | H: In _ [] |- _ => inv H
    end.
  - destruct Hin as [Hin_eq | Hin_eqs ]; subst.
    + inversion_clear Hsem as [ | ? ? Hsem_eq ];
      inv Hsem_eq; discriminate.
    + eapply IHeqs. inv Hsem; auto.
      repeat eexists. eauto.
  Qed.


End MEMSEMANTICS.

Module MemSemanticsFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Op)
       (Clks  : CLOCKS      Ids)
       (Syn   : NLSYNTAX    Ids Op       Clks)
       (Str   : STREAM             Op OpAux)
       (Ord   : ORDERED     Ids Op       Clks Syn)
       (Sem   : NLSEMANTICS Ids Op OpAux Clks Syn Str Ord)
       (Mem   : MEMORIES    Ids Op       Clks Syn)
       (IsD   : ISDEFINED   Ids Op       Clks Syn         Mem)
       (IsV   : ISVARIABLE  Ids Op       Clks Syn         Mem IsD)
       (IsF   : ISFREE      Ids Op       Clks Syn)
       (NoD   : NODUP       Ids Op       Clks Syn         Mem IsD IsV)
       (WeF   : WELLFORMED  Ids Op       Clks Syn     Ord Mem IsD IsV IsF NoD)
       <: MEMSEMANTICS Ids Op OpAux Clks Syn Str Ord Sem Mem IsD IsV IsF NoD WeF.
  Include MEMSEMANTICS Ids Op OpAux Clks Syn Str Ord Sem Mem IsD IsV IsF NoD WeF.
End MemSemanticsFun.
