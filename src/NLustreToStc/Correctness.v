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

From Coq Require Import FSets.FMapPositive.
From Coq Require Import PArith.
From Coq Require Import Logic.FunctionalExtensionality.

From Velus Require Import NLustre.
From Velus Require Import Stc.

From Velus Require Import NLustreToStc.Translation.

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import VelusMemory.

From Coq Require Import Omega.

From Coq Require Import List.
Import List.ListNotations.

Open Scope list.
Open Scope nat.

Module Type CORRECTNESS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Op)
       (Import CStr  : COINDSTREAMS    Op OpAux)
       (Import IStr  : INDEXEDSTREAMS  Op OpAux)
       (Import CE    : COREEXPR    Ids Op OpAux      IStr)
       (Import NL    : NLUSTRE     Ids Op OpAux CStr IStr CE)
       (Import Stc   : STC         Ids Op OpAux      IStr CE)
       (Import Trans : TRANSLATION Ids Op                 CE.Syn NL.Syn Stc.Syn NL.Mem).

  Lemma In_snd_gather_eqs_Is_node_in:
    forall eqs i f,
      In (i, f) (snd (gather_eqs eqs)) ->
      Is_node_in f eqs.
  Proof.
    unfold gather_eqs.
    intro.
    generalize (@nil (ident * (Op.const * clock))).
    induction eqs as [|[]]; simpl; try contradiction; intros * Hin; auto.
    - right; eapply IHeqs; eauto.
    - destruct l.
      + right; eapply IHeqs; eauto.
      + apply In_snd_fold_left_gather_eq in Hin as [Hin|Hin].
        * destruct Hin as [E|]; try contradiction; inv E.
          left; constructor.
        * right; eapply IHeqs; eauto.
    - right; eapply IHeqs; eauto.
  Qed.

  Lemma Ordered_nodes_systems:
    forall G,
      Ordered_nodes G ->
      Ordered_systems (translate G).
  Proof.
    induction 1 as [|??? IH NodeIn Nodup]; simpl; constructor; auto.
    - destruct nd; simpl in *; clear - NodeIn.
      apply Forall_forall; intros * Hin.
      destruct x; apply In_snd_gather_eqs_Is_node_in in Hin.
      apply NodeIn in Hin as [? E]; split; auto.
      clear NodeIn.
      induction nds as [|n].
      + inv E.
      + simpl; destruct (ident_eqb (n_name n) i0) eqn: Eq.
        * inv E; eauto.
        * inv E; eauto.
          rewrite ident_eqb_refl in Eq; discriminate.
    - clear - Nodup.
      induction Nodup; simpl; auto.
  Qed.

  Lemma msem_eqs_reset_lasts:
    forall G bk H M n,
      memory_closed_n M (n_eqs n) ->
      Forall (msem_equation G bk H M) (n_eqs n) ->
      reset_lasts (translate_node n) (M 0).
  Proof.
    intros * Closed Heqs ??? Hin.
    destruct n; simpl in *.
    unfold gather_eqs in *.
    clear - Heqs Hin.
    revert Hin; generalize (@nil (ident * ident)).
    induction n_eqs0 as [|[] ? IH]; simpl in *; intros; try contradiction;
      inversion_clear Heqs as [|?? Heq]; inv Heq; eauto.
    - destruct l; try discriminate; eauto.
    - destruct l; try discriminate; eauto.
    - apply In_fst_fold_left_gather_eq in Hin as [Hin|]; eauto.
      destruct Hin as [E|]; try contradiction; inv E.
      match goal with H: mfby _ _ _ _ _ |- _ => destruct H as (?&?) end; auto.
  Qed.

  Lemma msem_eqs_In_snd_gather_eqs_spec:
    forall eqs G bk H M x f,
      Forall (msem_equation G bk H M) eqs ->
      In (x, f) (snd (gather_eqs eqs)) ->
      exists xss Mx yss,
        (msem_node G f xss Mx yss
         \/ exists r, forall k, exists Mk, msem_node G f (mask k r xss) Mk (mask k r yss)
                           /\ memory_masked k r Mx Mk)
        /\ sub_inst_n x M Mx.
  Proof.
    unfold gather_eqs.
    intro; generalize (@nil (ident * (Op.const * clock))).
    induction eqs as [|[]]; simpl; intros ??????? Heqs Hin;
      inversion_clear Heqs as [|?? Heq];
      try inversion_clear Heq as [|??????????? Hd|
                                  ??????????????? Hd ?????? Rst|];
      try contradiction; eauto.
    - destruct l; try discriminate.
      apply In_snd_fold_left_gather_eq in Hin as [Hin|]; eauto.
      destruct Hin as [E|]; try contradiction; inv E; inv Hd.
      do 3 eexists; split; eauto.
    - destruct l; try discriminate.
      apply In_snd_fold_left_gather_eq in Hin as [Hin|]; eauto.
      destruct Hin as [E|]; try contradiction; inv E; inv Hd.
      exists ls, Mx, xss.
      split; auto.
      right; eexists; intro k; destruct (Rst k) as (?&?&?); eauto.
  Qed.

  Lemma msem_node_initial_state:
    forall G f xss M yss,
      Ordered_nodes G ->
      msem_node G f xss M yss ->
      initial_state (translate G) f (M 0).
  Proof.
    induction G as [|node ? IH].
    inversion 2;
      match goal with Hf: find_node _ [] = _ |- _ => inversion Hf end.
    intros * Hord Hsem.
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [??????? Clock Hfind Ins ?? Heqs Closed].
    pose proof (find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    pose proof Hord; inversion_clear Hord as [|??? NodeIn].
    pose proof Hfind as Hfind'.
    simpl in Hfind.
    destruct (ident_eqb node.(n_name) f) eqn:Hnf.
    - inversion Hfind; subst n.
      apply find_node_translate in Hfind' as (?&?&Hfind'&?); subst.
      pose proof Hfind';
        simpl in Hfind'; rewrite Hnf in Hfind'; inv Hfind'.
      eapply msem_equations_cons in Heqs; eauto.
      econstructor; eauto.
      + eapply msem_eqs_reset_lasts; eauto.
      + intros * Hin.
        destruct node; simpl in *.
        edestruct msem_eqs_In_snd_gather_eqs_spec
          as (?& Mx &?& [Node|(rs & Reset)] & Sub); eauto.
        destruct (Reset (if rs 0 then pred (count rs 0) else count rs 0))
          as (M0 & Node & Mmask).
        apply IH in Node; auto.
        specialize (Mmask 0); specialize (Sub 0).
        rewrite Mmask in Sub.
        * eexists; split; eauto.
        * simpl; cases.
    - assert (n_name node <> f) by now apply ident_eqb_neq.
      eapply msem_node_cons in Hsem; eauto.
      simpl; rewrite <-initial_state_other; eauto.
  Qed.

  Definition sem_trconstrs_n
             (P: program) (bk: stream bool) (H: history)
             (E: stream state) (T: stream state) (E': stream state)
             (tcs: list trconstr) :=
    forall n, Forall (sem_trconstr P (bk n) (H n) (E n) (T n) (E' n)) tcs.

  Definition sem_system_n
             (P: program) (f: ident)
             (E: stream state) (xss yss: stream (list value)) (E': stream state) :=
    forall n, sem_system P f (E n) (xss n) (yss n) (E' n).

  Lemma sem_trconstrs_n_add_n:
    forall P tcs bk H S S' Is x Sx,
      sem_trconstrs_n P bk H S Is S' tcs ->
      (forall k, ~ Is_sub_in x k tcs) ->
      sem_trconstrs_n P bk H S (add_inst_n x Sx Is) S' tcs.
  Proof.
    induction tcs as [|tc tcs]; intros * Sem Notin n; constructor.
    - specialize (Sem n); inversion_clear Sem as [|?? Sem'].
      inv Sem'; eauto using sem_trconstr.
      + econstructor; eauto.
        unfold add_inst_n; rewrite find_inst_gso; auto.
        intro E; eapply Notin; rewrite E; do 2 constructor.
      + econstructor; eauto.
        unfold add_inst_n; rewrite find_inst_gso; auto.
        intro E; eapply Notin; rewrite E; do 2 constructor.
    - apply IHtcs.
      + intro n'; specialize (Sem n'); inv Sem; auto.
      + apply not_Is_sub_in_cons in Notin as []; auto.
  Qed.

  Inductive translate_eqn_nodup_subs: NL.Syn.equation -> list trconstr -> Prop :=
    | TrNodupEqDef:
        forall x ck e eqs,
          translate_eqn_nodup_subs (NL.Syn.EqDef x ck e) eqs
    | TrNodupEqApp:
        forall xs ck f es r eqs x,
          hd_error xs = Some x ->
          (forall k, ~ Is_sub_in x k eqs) ->
          translate_eqn_nodup_subs (EqApp xs ck f es r) eqs
    | TrNodupEqFby:
        forall x ck c e eqs,
          translate_eqn_nodup_subs (EqFby x ck c e) eqs.

  Inductive memory_closed_rec: global -> ident -> memory val -> Prop :=
    memory_closed_rec_intro:
      forall G f M n,
        find_node f G = Some n ->
        (forall x, find_val x M <> None -> In x (gather_mems n.(n_eqs))) ->
        (forall i Mi, find_inst i M = Some Mi ->
              exists f',
                In (i, f') (gather_insts n.(n_eqs))
                /\ memory_closed_rec G f' Mi) ->
        memory_closed_rec G f M.

  Definition memory_closed_rec_n (G: global) (f: ident) (M: memories) : Prop :=
    forall n, memory_closed_rec G f (M n).

  Lemma memory_closed_rec_other:
    forall M G f node,
      Ordered_nodes (node :: G) ->
      node.(n_name) <> f ->
      (memory_closed_rec (node :: G) f M
       <-> memory_closed_rec G f M).
  Proof.
    induction M as [? IH] using memory_ind'.
    split; inversion_clear 1 as [???? Find ? Insts].
    - apply find_node_other in Find; auto.
      econstructor; eauto.
      intros * Find'; pose proof Find';
        apply Insts in Find' as (?& Hin & Closed).
      erewrite IH in Closed; eauto.
      rewrite <-gather_eqs_snd_spec in Hin.
      apply In_snd_gather_eqs_Is_node_in in Hin.
      intro; subst; contradict Hin.
      eapply find_node_later_not_Is_node_in; eauto.
    - pose proof Find; eapply find_node_other in Find; eauto.
      econstructor; eauto.
      intros * Find'; pose proof Find';
        apply Insts in Find' as (?& Hin & Closed).
      erewrite <-IH in Closed; eauto.
      rewrite <-gather_eqs_snd_spec in Hin.
      apply In_snd_gather_eqs_Is_node_in in Hin.
      intro; subst; contradict Hin.
      eapply find_node_later_not_Is_node_in; eauto.
  Qed.

  Lemma memory_closed_rec_n_other:
    forall M G f node,
      Ordered_nodes (node :: G) ->
      node.(n_name) <> f ->
      (memory_closed_rec_n (node :: G) f M
       <-> memory_closed_rec_n G f M).
  Proof.
    split; intros Closed n; specialize (Closed n).
    - apply memory_closed_rec_other in Closed; auto.
    - apply memory_closed_rec_other; auto.
  Qed.

  Lemma msem_equations_memory_closed_rec:
    forall eqs G bk H M n x f Mx,
      (forall f xss M yss,
          msem_node G f xss M yss ->
          memory_closed_rec_n G f M) ->
      Forall (msem_equation G bk H M) eqs ->
      find_inst x (M n) = Some Mx ->
      In (x, f) (gather_insts eqs) ->
      memory_closed_rec G f Mx.
  Proof.
    unfold gather_insts.
    induction eqs as [|eq]; simpl; intros * IH Heqs Find Hin;
      inversion_clear Heqs as [|?? Heq]; try contradiction.
    apply in_app in Hin as [Hin|]; eauto.
    destruct eq; simpl in Hin; try contradiction.
    destruct l; try contradiction.
    inversion_clear Hin as [E|]; try contradiction; inv E.
    inversion_clear Heq as [|??????????? Hd Sub|
                            ??????????????? Hd Sub ????? Rst|];
      inv Hd; rewrite Sub in Find; inv Find.
    - eapply IH; eauto.
    - specialize (Rst (if rs n then pred (count rs n) else count rs n));
        destruct Rst as (?& Node & Mask).
      apply IH in Node.
      rewrite Mask; auto.
      cases_eqn Hr; apply count_true_ge_1 in Hr.
      erewrite <-Lt.S_pred; eauto.
  Qed.

  Lemma msem_node_memory_closed_rec_n:
    forall G f xss M yss,
      Ordered_nodes G ->
      msem_node G f xss M yss ->
      memory_closed_rec_n G f M.
  Proof.
    induction G as [|node]; intros ???? Ord;
      inversion_clear 1 as [???????? Find ??? Heqs Closed];
      try now inv Find.
    pose proof Find; simpl in Find.
    destruct (ident_eqb node.(n_name) f) eqn:Eq.
    - inv Find.
      econstructor; eauto.
      + apply Closed.
      + intros * Find_i.
        assert (exists f', In (i, f') (gather_insts (n_eqs n))) as (f' & Hin)
            by (eapply InMembers_In, Closed, not_None_is_Some; eauto).
        eexists; split; eauto.
        assert (f' <> n.(n_name)).
        { rewrite <-gather_eqs_snd_spec in Hin.
          apply In_snd_gather_eqs_Is_node_in in Hin.
          intro; subst; contradict Hin; eapply find_node_not_Is_node_in; eauto.
        }
        apply memory_closed_rec_other; auto.
        assert (~ Is_node_in (n_name n) (n_eqs n))
          by (eapply find_node_not_Is_node_in; eauto).
        apply msem_equations_cons in Heqs; auto.
        inv Ord.
        eapply msem_equations_memory_closed_rec; eauto.
    - apply ident_eqb_neq in Eq.
      assert (~ Is_node_in (n_name node) (n_eqs n))
        by (eapply find_node_later_not_Is_node_in; eauto).
      apply msem_equations_cons in Heqs; auto.
      apply memory_closed_rec_n_other; auto; inv Ord; eauto.
  Qed.

  Lemma memory_closed_rec_state_closed:
    forall M G f,
      Ordered_nodes G ->
      memory_closed_rec G f M ->
      state_closed (translate G) f M.
  Proof.
    induction M as [? IH] using memory_ind'.
    intros * Ord Closed; inversion_clear Closed as [???? Find ? Insts].
    apply find_node_translate in Find as (?&?&?&?); subst.
    econstructor; eauto; simpl.
    - intros * ??; rewrite gather_eqs_fst_spec; auto.
    - intros * Find; pose proof Find as Find'.
      apply Insts in Find as (?& Hin & Closed).
      rewrite <-gather_eqs_snd_spec in Hin.
      eexists; split; eauto.
      eapply IH in Closed; eauto.
      apply Ordered_nodes_systems in Ord.
      eapply state_closed_find_system_other; eauto.
  Qed.

  Corollary msem_node_state_closed:
     forall G f xss M yss,
      Ordered_nodes G ->
      msem_node G f xss M yss ->
      forall n, state_closed (translate G) f (M n).
  Proof.
    intros; apply memory_closed_rec_state_closed; auto.
    eapply msem_node_memory_closed_rec_n; eauto.
  Qed.

  Lemma state_closed_insts_add:
    forall P insts I x f M,
      state_closed_insts P insts I ->
      state_closed P f M ->
      state_closed_insts P ([(x, f)] ++ insts) (add_inst x M I).
  Proof.
    intros * Trans Closed.
    intros i ? Find.
    destruct (ident_eq_dec i x).
    - subst. rewrite find_inst_gss in Find; inv Find.
      exists f; split; auto.
      apply in_app; left; constructor; auto.
    - rewrite find_inst_gso in Find; auto.
      apply Trans in Find as (g&?&?).
      exists g; split; auto.
      apply in_app; auto.
  Qed.

  Definition next (M: memories) : memories := fun n => M (S n).

  Lemma equation_correctness:
    forall G eq tcs bk H M Is vars insts,
      (forall f xss M yss,
          msem_node G f xss M yss ->
          sem_system_n (translate G) f M xss yss (next M)) ->
      Ordered_nodes G ->
      NL.Clo.wc_equation G vars eq ->
      CE.Sem.sem_clocked_vars bk H vars ->
      translate_eqn_nodup_subs eq tcs ->
      (forall n, state_closed_insts (translate G) insts (Is n)) ->
      (forall n, forall x, find_val x (Is n) = None) ->
      msem_equation G bk H M eq ->
      sem_trconstrs_n (translate G) bk H M Is (next M) tcs ->
      exists Is',
        sem_trconstrs_n (translate G) bk H M Is' (next M) (translate_eqn eq ++ tcs)
        /\ (forall n, state_closed_insts (translate G) (gather_inst_eq eq ++ insts) (Is' n))
        /\ forall n x, find_val x (Is' n) = None.
  Proof.
    intros * IHnode Hord WC ClkM TrNodup Closed SpecLasts Heq Htcs.
    destruct Heq as [|???????????????? Node|
                     ???????????????????? Var Hr Reset|
                     ????????? Arg Var Mfby];
      inversion_clear TrNodup as [|???????? Notin|]; simpl.

    - eexists; split; eauto.
      do 2 (econstructor; eauto).

    - destruct xs; try discriminate.
      match goal with
      | H: hd_error ?l = Some x,
           H': hd_error ?l = _ |- _ =>
        rewrite H' in H; inv H; simpl in H'; inv H'
      end.
      exists (add_inst_n x Mx Is); split; [|split]; auto.
      + constructor; auto.
        *{ econstructor; eauto.
           - intro; apply orel_eq_weaken; auto.
           - apply Env.gss.
           - now apply IHnode.
         }
        * apply sem_trconstrs_n_add_n; auto.
      + intro; apply state_closed_insts_add; auto.
        eapply msem_node_state_closed; eauto.

    - destruct xs; try discriminate.
      match goal with
      | H: hd_error ?l = Some x,
           H': hd_error ?l = _ |- _ =>
        rewrite H' in H; inv H; simpl in H'; inv H'
      end.
      assert (forall Mx, sem_trconstrs_n (translate G) bk H M (add_inst_n x Mx Is) (next M) tcs) as Htcs'
          by now intro; apply sem_trconstrs_n_add_n.
      assert (CE.Sem.sem_clocked_var bk H y cky) as Cky.
      { intro n; specialize (ClkM n).
        eapply Forall_forall in ClkM; eauto; inv WC; eauto; auto.
      }
      exists (fun n => add_inst x (if rs n then Mx 0 else Mx n) (Is n)); split; [|split]; auto;
        intro;
        destruct (Reset (count rs n)) as (Mn & Node_n & Mmask_n),
                                         (Reset 0) as (M0 & Node_0 & Mmask_0);
        specialize (Var n); specialize (Hr n); specialize (Cky n); simpl in Cky;
          pose proof Node_n as Node_n'; apply IHnode in Node_n; specialize (Node_n n);
            rewrite 2 mask_transparent in Node_n; auto.
      + destruct (rs n) eqn: Hrst.
        *{ assert (find_inst x (add_inst x (Mx 0) (Is n)) = Some (Mx 0))
             by apply find_inst_gss.
           specialize (Htcs' (fun n => Mx 0) n).
           destruct (ys n) eqn: E'; try discriminate.
           do 2 (econstructor; eauto using sem_trconstr).
           - eapply Sem.Son; eauto.
             apply Cky; eauto.
           - simpl; rewrite Mmask_0; auto.
             eapply msem_node_initial_state; eauto.
           - econstructor; eauto.
             + discriminate.
             + assert (Mn n ≋ Mn 0) as Eq.
               { eapply msem_node_absent_until; eauto.
                 intros * Spec.
                 rewrite mask_opaque.
                 - apply all_absent_spec.
                 - eapply count_positive in Spec; eauto; omega.
               }
               eapply same_initial_memory with (2 := Node_n') in Node_0; eauto.
               unfold next in Node_n; simpl in Node_n.
               specialize (Mmask_n (S n)).
               rewrite Mmask_n, Mmask_0, <-Node_0, <-Eq; auto.
         }
        *{ rewrite <-Mmask_n in Node_n; try rewrite Hrst; auto.
           assert (find_inst x (add_inst x (Mx n) (Is n)) = Some (Mx n))
             by apply find_inst_gss.
           specialize (Htcs' Mx n).
           destruct (ys n) eqn: E'.
           - do 2 (econstructor; eauto using sem_trconstr).
             + apply Sem.Son_abs1; auto.
               apply Cky; auto.
             + simpl; apply orel_eq_weaken; auto.
             + econstructor; eauto.
               * discriminate.
               * unfold next; simpl.
                 rewrite <-Mmask_n; auto.
           - do 2 (econstructor; eauto using sem_trconstr).
             + change true with (negb false).
               eapply Sem.Son_abs2; eauto.
               apply Cky; eauto.
             + simpl; apply orel_eq_weaken; auto.
             + econstructor; eauto.
               * discriminate.
               * unfold next; simpl.
                 rewrite <-Mmask_n; auto.
         }
      + apply state_closed_insts_add; auto.
        destruct (rs n) eqn: Hrst.
        * rewrite Mmask_0.
          -- eapply msem_node_state_closed; eauto.
          -- simpl; cases.
        * rewrite Mmask_n; try rewrite Hrst; auto.
          eapply msem_node_state_closed; eauto.

    - do 3 (econstructor; auto).
      destruct Mfby as (?& Spec).
      specialize (Spec n); destruct (find_val x (M n)) eqn: E; try contradiction.
      specialize (Var n); specialize (Arg n).
      pose proof Arg as Arg'.
      destruct (ls n); destruct Spec as (?& Hxs); rewrite Hxs in Var; inv Arg';
        econstructor; eauto; simpl; auto.
  Qed.

  Lemma not_Is_defined_not_Is_sub_in_eqs:
    forall x eqs,
      ~ NL.IsD.Is_defined_in x eqs ->
      (forall k, ~ Is_sub_in x k (translate_eqns eqs)).
  Proof.
    unfold translate_eqns.
    induction eqs as [|eq]; simpl; intros Notin k Hin.
    - inv Hin.
    - apply Exists_app' in Hin as [Hin|].
      + destruct eq; simpl in Hin.
        * inversion_clear Hin as [?? Hin'|?? Hin']; inv Hin'.
        *{ destruct l; try destruct o as [(?&?)|]; inversion_clear Hin as [?? Hin'|?? Hin'].
           - inv Hin'; apply Notin; do 3 constructor; auto.
           - inversion_clear Hin' as [?? Hin|?? Hin]; inv Hin;
               apply Notin; do 3 constructor; auto.
           - inv Hin'; apply Notin; do 3 constructor; auto.
           - inv Hin'.
         }
        * inversion_clear Hin as [?? Hin'|?? Hin']; inv Hin'.
      + eapply IHeqs; eauto.
        eapply NL.IsD.not_Is_defined_in_cons in Notin as []; auto.
  Qed.

  Lemma Nodup_defs_translate_eqns:
    forall eq eqs G bk H M,
      msem_equation G bk H M eq ->
      NoDup_defs (eq :: eqs) ->
      translate_eqn_nodup_subs eq (translate_eqns eqs).
  Proof.
    destruct eq; inversion_clear 1; inversion_clear 1; econstructor; eauto.
    - apply not_Is_defined_not_Is_sub_in_eqs.
      assert (In x l) by (now apply hd_error_Some_In); auto.
    - apply not_Is_defined_not_Is_sub_in_eqs.
      assert (In x l) by (now apply hd_error_Some_In); auto.
  Qed.

  Lemma gather_insts_Is_sub_in_translate_eqns:
    forall eqs x,
      InMembers x (gather_insts eqs) ->
      exists k, Is_sub_in x k (translate_eqns eqs).
  Proof.
    unfold gather_insts, translate_eqns.
    induction eqs as [|[]]; simpl; try contradiction; intros * Hin.
    - edestruct IHeqs; eauto; eexists; right; eauto.
    - destruct l; simpl in *; auto.
      destruct o as [(?&?)|].
      + destruct Hin; subst.
        * exists 1; apply Exists_app'; left; right; left; constructor.
        * edestruct IHeqs; eauto; eexists; apply Exists_app; eauto.
      + destruct Hin; subst.
        * exists 1; apply Exists_app'; left; left; constructor.
        * edestruct IHeqs; eauto; eexists; apply Exists_app; eauto.
    - edestruct IHeqs; eauto; eexists; right; eauto.
  Qed.

  Lemma state_closed_insts_empty:
    forall P insts,
      state_closed_insts P insts (empty_memory _).
  Proof.
    intros ???? Find.
    rewrite find_inst_gempty in Find; discriminate.
  Qed.

  Corollary equations_correctness:
    forall G bk H M eqs vars,
      (forall f xss M yss,
          msem_node G f xss M yss ->
          sem_system_n (translate G) f M xss yss (next M)) ->
      Ordered_nodes G ->
      Forall (NL.Clo.wc_equation G vars) eqs ->
      CE.Sem.sem_clocked_vars bk H vars ->
      NoDup_defs eqs ->
      Forall (msem_equation G bk H M) eqs ->
      exists Is, sem_trconstrs_n (translate G) bk H M Is (next M) (translate_eqns eqs)
            /\ (forall n, state_closed_insts (translate G) (gather_insts eqs) (Is n))
            /\ forall n x, find_val x (Is n) = None.
  Proof.
    intros ???????? WC ?? Heqs.
    unfold translate_eqns.
    induction eqs as [|eq eqs IHeqs]; simpl; inv WC.
    - exists (fun n => empty_memory _); split; try constructor.
      + intro; apply state_closed_insts_empty.
      + intro; apply find_val_gempty.
    - apply Forall_cons2 in Heqs as [Heq Heqs].
      apply IHeqs in Heqs as (?&?&?&?); auto.
      + unfold gather_insts; simpl.
        eapply equation_correctness; eauto.
        eapply Nodup_defs_translate_eqns; eauto.
      + eapply NoDup_defs_cons; eauto.
  Qed.

  Lemma not_Is_node_in_not_Is_system_in:
    forall eqs f,
      ~ Is_node_in f eqs ->
      ~ Is_system_in f (translate_eqns eqs).
  Proof.
    unfold translate_eqns.
    induction eqs as [|eq]; simpl; intros * Hnin Hin.
    - inv Hin.
    - apply not_Is_node_in_cons in Hnin as (Hnineq & Hnin).
      apply IHeqs in Hnin.
      destruct eq; simpl in *.
      + inversion_clear Hin as [?? E|?? Hins]; try inv E; auto.
      + destruct l; auto.
        destruct o as [(?&?)|]; inversion_clear Hin as [?? E|?? Hins]; auto.
        * inv E; apply Hnineq; constructor.
        * inversion_clear Hins as [?? E|?? Hins']; auto.
          inv E; apply Hnineq; constructor.
        * inv E; apply Hnineq; constructor.
      + inversion_clear Hin as [?? E|?? Hins]; try inv E; auto.
  Qed.

  Theorem correctness:
    forall G f xss M yss,
      Ordered_nodes G ->
      wc_global G ->
      msem_node G f xss M yss ->
      sem_system_n (translate G) f M xss yss (next M).
  Proof.
    induction G as [|node ? IH].
    inversion 3;
      match goal with Hf: find_node _ [] = _ |- _ => inversion Hf end.
    intros * Hord WC Hsem n.
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [??????? Clock Hfind Ins Outs Ck Heqs Closed].
    pose proof (find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    pose proof Hord; inversion_clear Hord as [|??? NodeIn].
    pose proof Hfind as Hfind'.
    simpl in Hfind.
    assert (Ordered_systems (translate_node node :: translate G))
      by (change (translate_node node :: translate G) with (translate (node :: G));
          apply Ordered_nodes_systems; auto).
    inversion WC as [|??? (?&?&?& WCeqs)]; subst.
    destruct (ident_eqb node.(n_name) f) eqn:Hnf.
    - inversion Hfind; subst n0.
      apply find_node_translate in Hfind' as (?&?& Hfind' &?); subst.
      eapply msem_equations_cons in Heqs; eauto.
      pose proof (NoDup_defs_node node).
      eapply equations_correctness in Heqs as (I & Heqs &?&?); eauto.
      + econstructor; eauto.
        * apply sem_trconstrs_cons; eauto.
          apply not_Is_node_in_not_Is_system_in; auto.
        * eapply msem_node_state_closed; eauto.
        * econstructor; eauto; try congruence.
          eapply state_closed_insts_find_system_other, state_closed_insts_cons; eauto.
          simpl; rewrite gather_eqs_snd_spec; auto.
        * unfold next; eapply msem_node_state_closed; eauto.
      + rewrite idck_app.
        intro k; specialize (Ck k); setoid_rewrite Forall_app; split; auto.
        apply Forall_forall; intros (x, ck) ?.
        rewrite idck_app in WCeqs.
        eapply sem_clocked_var_eqs with (eqs := node.(n_eqs)); eauto.
        * rewrite <-idck_app, NoDupMembers_idck.
          apply n_nodup.
        * eapply msem_sem_equations; eauto.
        * rewrite map_fst_idck.
          apply n_defd.
    - assert (n_name node <> f) by now apply ident_eqb_neq.
      eapply msem_node_cons, IH in Hsem; eauto.
      apply sem_system_cons2; auto using Ordered_systems.
  Qed.

  Corollary correctness_loop:
    forall G f xss M yss,
      Ordered_nodes G ->
      wc_global G ->
      msem_node G f xss M yss ->
      initial_state (translate G) f (M 0)
      /\ loop (translate G) f xss yss (M 0) 0.
  Proof.
    intros; split.
    - eapply msem_node_initial_state; eauto.
    - apply loop_coind with (R := fun P b xss yss S n =>
                                    P = translate G
                                    /\ S ≋ M n
                                    /\ msem_node G b xss M yss);
        try now intuition.
      intros * (?& E & Sem); subst.
      pose proof Sem; apply correctness in Sem; auto.
      exists (next M n); intuition eauto.
      + rewrite E; auto.
      + unfold next; simpl; reflexivity.
  Qed.

End CORRECTNESS.

Module CorrectnessFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Op)
       (CStr  : COINDSTREAMS    Op OpAux)
       (IStr  : INDEXEDSTREAMS  Op OpAux)
       (CE    : COREEXPR    Ids Op OpAux      IStr)
       (NL    : NLUSTRE     Ids Op OpAux CStr IStr CE)
       (Stc   : STC         Ids Op OpAux      IStr CE)
       (Trans : TRANSLATION Ids Op                 CE.Syn NL.Syn Stc.Syn NL.Mem)
<: CORRECTNESS Ids Op OpAux CStr IStr CE NL Stc Trans.
  Include CORRECTNESS Ids Op OpAux CStr IStr CE NL Stc Trans.
End CorrectnessFun.
