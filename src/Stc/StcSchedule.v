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

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Sorting.Mergesort.
From Coq Require Import Morphisms.
From Coq Require Import Setoid.

From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import Stc.StcIsSystem.
From Velus Require Import Stc.StcOrdered.
From Velus Require Import IndexedStreams.
From Velus Require Import Stc.StcSemantics.
From Velus Require Import Stc.StcTyping.
From Velus Require Import Stc.StcIsVariable.
From Velus Require Import Stc.StcIsLast.
From Velus Require Import Stc.StcIsDefined.
From Velus Require Import Stc.StcClocking.
From Velus Require Import Stc.StcIsFree.
From Velus Require Import Stc.StcWellDefined.

From Velus Require Import VelusMemory.

(** * Scheduling of N-Lustre equations *)

(**

  The scheduler routines are parameterized over an external scheduler
  (EXT_NLSCHEDULER) that provides a schedule function.

  The schedule function should map a list of equations to a list of priority
  values (positive integers). If the output list has the same length as the
  input list, the equations are sorted in ascending order of their priorities.

  The idea is to allow an external scheduler to be written in OCaml. The
  scheduler should order the equations by their dependencies. If this is
  impossible, it should print an explanatory error message and return the
  empty list.

 *)

Module Type EXT_STCSCHEDULER
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import CESyn : CESYNTAX Op)
       (Import Syn   : STCSYNTAX Ids Op CESyn).

  Parameter schedule : ident -> list trconstr -> list positive.

End EXT_STCSCHEDULER.

Module Type STCSCHEDULE
       (Import Ids    : IDS)
       (Import Op     : OPERATORS)
       (Import OpAux  : OPERATORS_AUX        Op)
       (Import Str    : INDEXEDSTREAMS       Op OpAux)
       (Import CE     : COREEXPR         Ids Op OpAux Str)
       (Import StcSyn : STCSYNTAX        Ids Op       CE.Syn)
       (Import Syst   : STCISSYSTEM      Ids Op       CE.Syn StcSyn)
       (Import Ord    : STCORDERED       Ids Op       CE.Syn StcSyn Syst)
       (Import StcSem : STCSEMANTICS     Ids Op OpAux CE.Syn StcSyn Syst Ord Str CE.Sem)
       (Import StcTyp : STCTYPING        Ids Op       CE.Syn StcSyn CE.Typ)
       (Import Var    : STCISVARIABLE    Ids Op       CE.Syn StcSyn)
       (Import Last   : STCISLAST        Ids Op       CE.Syn StcSyn)
       (Import Def    : STCISDEFINED     Ids Op       CE.Syn StcSyn Var Last)
       (Import StcClo : STCCLOCKING      Ids Op       CE.Syn StcSyn Last Var Def Syst Ord CE.Clo)
       (Import Free   : STCISFREE        Ids Op       CE.Syn StcSyn                        CE.IsF)
       (Import Wdef   : STCWELLDEFINED   Ids Op       CE.Syn StcSyn Syst Ord Var Last Def CE.IsF Free)
       (Import Sch    : EXT_STCSCHEDULER Ids Op       CE.Syn StcSyn).

  Section OCombine.
    Context {A B: Type}.

    Fixpoint ocombine (l : list A) (l' : list B) : option (list (A * B)) :=
      match l, l' with
      | [], [] => Some []
      | x::xs, y::ys =>
        match ocombine xs ys with
        | None => None
        | Some rs => Some ((x, y) :: rs)
        end
      | _, _ => None
      end.

    Lemma ocombine_combine:
      forall l l' ll,
        ocombine l l' = Some ll ->
        combine l l' = ll.
    Proof.
      induction l, l'; simpl;
        try (now inversion_clear 1; auto).
      intros * HH; cases_eqn Hoc; inv HH.
      erewrite IHl; eauto.
    Qed.

    Lemma ocombine_length:
      forall l l' ll,
        ocombine l l' = Some ll ->
        length l = length l'.
    Proof.
      induction l, l'; simpl; inversion 1; auto.
      destruct (ocombine l l') eqn:Hoc.
      now rewrite (IHl _ _ Hoc).
      inv H.
    Qed.

  End OCombine.

  Module SchTcOrder <: Orders.TotalLeBool'.

    Definition t : Type := (positive * trconstr)%type.

    (* The arguments are inversed to put the list in the reverse order
       expected by [Is_well_sch]. *)
    Definition leb (s1 s2 : t) : bool := ((fst s2) <=? (fst s1))%positive.

    Lemma leb_total:
      forall s1 s2,
        leb s1 s2 = true \/ leb s2 s1 = true.
    Proof.
      destruct s1 as (p1 & eq1).
      destruct s2 as (p2 & eq2).
      unfold leb; simpl.
      setoid_rewrite POrderedType.Positive_as_OT.leb_compare.
      destruct (p1 ?= p2)%positive eqn:Hp; auto.
      apply Pos.compare_gt_iff in Hp.
      apply Pos.compare_lt_iff in Hp.
      rewrite Hp; auto.
    Qed.

  End SchTcOrder.

  Module SchSort := Sort SchTcOrder.

  Definition schedule_tcs (f: ident) (tcs: list trconstr) : list trconstr :=
    let sch := Sch.schedule f tcs in
    match ocombine sch tcs with
    | None        => tcs
    | Some schtcs => map snd (SchSort.sort schtcs)
    end.

  Lemma schedule_tcs_permutation:
    forall f tcs,
      Permutation (schedule_tcs f tcs) tcs.
  Proof.
    unfold schedule_tcs.
    intros f tcs.
    destruct (ocombine (schedule f tcs) tcs) eqn:Hoc; auto.
    rewrite <-SchSort.Permuted_sort.
    pose proof (ocombine_length _ _ _ Hoc) as Hlen.
    apply ocombine_combine in Hoc.
    rewrite <-Hoc, map_snd_combine; auto.
  Qed.

  Add Parametric Morphism : (calls_of)
      with signature @Permutation trconstr ==> @Permutation (ident * ident)
        as calls_of_permutation.
  Proof.
    induction 1; simpl; auto.
    - cases; rewrite IHPermutation.
    - cases; apply perm_swap.
    - etransitivity; eauto.
  Qed.

  Add Parametric Morphism : (resets_of)
      with signature @Permutation trconstr ==> @Permutation (ident * ident)
        as resets_of_permutation.
  Proof.
    induction 1; simpl; auto.
    - cases; rewrite IHPermutation.
    - cases; apply perm_swap.
    - etransitivity; eauto.
  Qed.

  Add Parametric Morphism : (lasts_of)
      with signature @Permutation trconstr ==> @Permutation ident
        as lasts_of_permutation.
  Proof.
    induction 1; simpl; auto.
    - cases; rewrite IHPermutation.
    - cases; apply perm_swap.
    - etransitivity; eauto.
  Qed.

  Add Parametric Morphism : (variables)
      with signature @Permutation trconstr ==> @Permutation ident
        as variables_permutation.
  Proof.
    unfold variables.
    induction 1; simpl; auto.
    - now rewrite IHPermutation.
    - rewrite <-2 Permutation_app_assoc; apply Permutation_app_tail, Permutation_app_comm.
    - etransitivity; eauto.
  Qed.

  Add Parametric Morphism A P: (Exists P)
      with signature @Permutation A ==> Basics.impl
        as Exists_permutation.
  Proof.
    induction 1; intros Ex; auto.
    - inv Ex.
      + now left.
      + right; auto.
    - inversion_clear Ex as [|?? Ex'].
      + now right; left.
      + inv Ex'.
        * now left.
        * now right; right.
  Qed.

  Add Parametric Morphism i k: (Is_sub_in i k)
      with signature @Permutation trconstr ==> Basics.impl
        as Is_sub_in_permutation.
  Proof.
    unfold Is_sub_in; intros * E St.
    now rewrite <-E.
  Qed.

  Program Definition schedule_system (b: system) : system :=
    {| s_name  := b.(s_name);
       s_subs  := b.(s_subs);
       s_in    := b.(s_in);
       s_vars  := b.(s_vars);
       s_lasts := b.(s_lasts);
       s_out   := b.(s_out);
       s_tcs   := schedule_tcs b.(s_name) b.(s_tcs);

       s_ingt0            := b.(s_ingt0);
       s_nodup            := b.(s_nodup);
       s_nodup_lasts_subs := b.(s_nodup_lasts_subs);
       s_good             := b.(s_good)
    |}.
  Next Obligation.
    rewrite schedule_tcs_permutation; apply s_subs_calls_of.
  Qed.
  Next Obligation.
    rewrite schedule_tcs_permutation; apply s_lasts_in_tcs.
  Qed.
  Next Obligation.
    rewrite schedule_tcs_permutation; apply s_vars_out_in_tcs.
  Qed.
  Next Obligation.
    rewrite schedule_tcs_permutation; apply s_reset_incl.
  Qed.
  Next Obligation.
    intros ?? Spec; unfold Step_with_reset_in in Spec; rewrite schedule_tcs_permutation in Spec.
    apply s_reset_consistency in Spec.
    cases; rewrite schedule_tcs_permutation; auto.
  Qed.

  Definition schedule (P: program) : program :=
    map schedule_system P.

  Lemma schedule_system_name:
    forall s, (schedule_system s).(s_name) = s.(s_name).
  Proof. destruct s; auto. Qed.

  Lemma schedule_map_name:
    forall P,
      map s_name (schedule P) = map s_name P.
  Proof.
    induction P as [|b]; auto.
    destruct b; simpl.
    now rewrite IHP.
  Qed.

  Lemma scheduler_find_system:
    forall P P' f s,
      find_system f P = Some (s, P') ->
      find_system f (schedule P) = Some (schedule_system s, schedule P').
  Proof.
    induction P as [|s']; [now inversion 1|].
    intros * Hfind.
    simpl in *.
    destruct (ident_eqb s'.(s_name) f); auto.
    inv Hfind; auto.
  Qed.

  Lemma scheduler_find_system':
    forall P f s P',
      find_system f (schedule P) = Some (s, P') ->
      exists s' P'',
        find_system f P = Some (s', P'')
        /\ s = schedule_system s'
        /\ P' = schedule P''.
  Proof.
    induction P as [|sys]; [now inversion 1|].
    intros * Hfind.
    simpl in *.
    destruct (ident_eqb sys.(s_name) f); eauto.
    inv Hfind; eauto.
  Qed.

  Lemma scheduler_wt_trconstr:
    forall P vars lasts tc,
      wt_trconstr P vars lasts tc ->
      wt_trconstr (schedule P) vars lasts tc.
  Proof.
    induction P as [|b].
    - destruct tc; inversion_clear 1; eauto.
    - destruct tc; inversion_clear 1; eauto;
        match goal with H:find_system _ _ = _ |- _ =>
                        apply scheduler_find_system in H end;
        eauto using wt_trconstr.
  Qed.

  Lemma scheduler_wt_system:
    forall P s,
      wt_system P s ->
      wt_system (schedule P) (schedule_system s).
  Proof.
    unfold wt_system; simpl; intros * WT.
    rewrite schedule_tcs_permutation.
    apply Forall_impl with (2 := WT), scheduler_wt_trconstr.
  Qed.

  Lemma scheduler_wt_program:
    forall P,
      wt_program P ->
      wt_program (schedule P).
  Proof.
    induction P as [|s]; inversion_clear 1; simpl;
      constructor; auto.
    - now apply scheduler_wt_system.
    - change (Forall (fun s' =>
                        (fun x => s_name (schedule_system s) <> x) s'.(s_name))
                     (schedule P)).
      rewrite <-Forall_map, schedule_map_name, Forall_map.
      destruct s; auto.
  Qed.

  Lemma scheduler_wc_trconstr:
    forall P vars tc,
      wc_trconstr P vars tc ->
      wc_trconstr (schedule P) vars tc.
  Proof.
    induction P as [|s P IH]; auto.
    intros vars tc Hwc.
    destruct tc; inv Hwc; eauto using wc_trconstr.
    econstructor; auto.
    - now apply scheduler_find_system; eauto.
    - eauto.
    - eauto.
  Qed.

  Lemma scheduler_wc_system:
    forall P s,
      wc_system P s ->
      wc_system (schedule P) (schedule_system s).
  Proof.
    inversion_clear 1 as [? (?&?& Htcs)].
    constructor; simpl; auto.
    intuition.
    rewrite schedule_tcs_permutation; auto.
    induction Htcs; constructor; auto.
    apply scheduler_wc_trconstr; auto.
  Qed.

  Lemma scheduler_wc_program:
    forall P,
      wc_program P ->
      wc_program (schedule P).
  Proof.
    induction P; intros * WT; inv WT; simpl; constructor; auto.
    now apply scheduler_wc_system.
  Qed.

  Lemma scheduler_initial_state:
    forall S P f,
      initial_state P f S ->
      initial_state (schedule P) f S.
  Proof.
    induction S as [? IH] using memory_ind'.
    inversion_clear 1 as [????? Find ? Insts].
    apply scheduler_find_system in Find.
    econstructor; eauto.
    simpl; intros * Hin.
    apply Insts in Hin as (?&?&?).
    eexists; intuition; eauto.
  Qed.
  Hint Resolve scheduler_initial_state : core.

  Lemma scheduler_state_closed:
    forall S P f,
      state_closed P f S ->
      state_closed (schedule P) f S.
  Proof.
    induction S as [? IH] using memory_ind'.
    inversion_clear 1 as [????? Find ? Insts].
    apply scheduler_find_system in Find.
    econstructor; eauto.
    simpl; intros * Hin; pose proof Hin.
    apply Insts in Hin as (?&?&?).
    eexists; intuition; eauto.
  Qed.
  Hint Resolve scheduler_state_closed : core.

  Theorem scheduler_sem_system:
    forall P f xs S S' ys,
      sem_system P f xs S S' ys ->
      sem_system (schedule P) f xs S S' ys.
  Proof.
    intro P;
      induction 1 using sem_system_mult
        with (P_trconstr := fun base R S I S' tc =>
                              sem_trconstr (schedule P) base R S I S' tc);
      eauto using sem_trconstr.
    - econstructor; eauto.
      cases; eauto.
    - match goal with H: find_system _ _ = _ |- _ => apply scheduler_find_system in H end.
      eapply SSystem with (I := I); eauto; simpl.
      rewrite schedule_tcs_permutation; eauto.
  Qed.

  Corollary scheduler_loop:
    forall n P f xss yss S,
      loop P f xss yss S n ->
      loop (schedule P) f xss yss S n.
  Proof.
    cofix COFIX; inversion_clear 1.
    econstructor; eauto.
    apply scheduler_sem_system; eauto.
  Qed.

  Lemma scheduler_ordered:
    forall P,
      Ordered_systems P ->
      Ordered_systems (schedule P).
  Proof.
    induction 1 as [|????? Names]; simpl; constructor; simpl; auto.
    - apply Forall_forall; intros (?&?) Hin;
        eapply Forall_forall in Hin; eauto; destruct Hin as (?& Find); intuition.
      destruct Find as (?&?& Find); apply scheduler_find_system in Find; eauto.
    - clear - Names; induction P; simpl; inv Names; constructor; auto.
  Qed.

  Lemma scheduler_normal_args_tc:
    forall P tc,
      normal_args_tc P tc ->
      normal_args_tc (schedule P) tc.
  Proof.
    induction 1; eauto using normal_args_tc.
    econstructor; auto.
    - apply scheduler_find_system; eauto.
    - auto.
  Qed.

Lemma scheduler_normal_args_system:
  forall P s,
    normal_args_system P s ->
    normal_args_system (schedule P) (schedule_system s).
Proof.
  intros * Normal.
  apply Forall_forall; simpl.
  setoid_rewrite schedule_tcs_permutation.
  intros; eapply Forall_forall in Normal; eauto.
  apply scheduler_normal_args_tc; auto.
Qed.

Lemma scheduler_normal_args:
  forall P,
    normal_args P ->
    normal_args (schedule P).
Proof.
  induction P as [|s]; auto.
  intros (?&?); split; auto.
  change (schedule_system s :: schedule P) with (schedule (s :: P)).
  apply scheduler_normal_args_system; auto.
Qed.

End STCSCHEDULE.

Module StcScheduleFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX        Op)
       (Str   : INDEXEDSTREAMS       Op OpAux)
       (CE    : COREEXPR         Ids Op OpAux Str)
       (Syn   : STCSYNTAX        Ids Op       CE.Syn)
       (Syst  : STCISSYSTEM      Ids Op       CE.Syn Syn)
       (Ord   : STCORDERED       Ids Op       CE.Syn Syn Syst)
       (Sem   : STCSEMANTICS     Ids Op OpAux CE.Syn Syn Syst Ord Str CE.Sem)
       (Typ   : STCTYPING        Ids Op       CE.Syn Syn CE.Typ)
       (Var   : STCISVARIABLE    Ids Op       CE.Syn Syn)
       (Last  : STCISLAST        Ids Op       CE.Syn Syn)
       (Def   : STCISDEFINED     Ids Op       CE.Syn Syn Var Last)
       (Clo   : STCCLOCKING      Ids Op       CE.Syn Syn Last Var Def Syst Ord CE.Clo)
       (Free  : STCISFREE        Ids Op       CE.Syn Syn                        CE.IsF)
       (Wdef  : STCWELLDEFINED   Ids Op       CE.Syn Syn Syst Ord Var Last Def CE.IsF Free)
       (Sch   : EXT_STCSCHEDULER Ids Op       CE.Syn Syn)
<: STCSCHEDULE Ids Op OpAux Str CE Syn Syst Ord Sem Typ Var Last Def Clo Free Wdef Sch.
  Include STCSCHEDULE Ids Op OpAux Str CE Syn Syst Ord Sem Typ Var Last Def Clo Free Wdef Sch.
End StcScheduleFun.
