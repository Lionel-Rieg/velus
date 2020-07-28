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

From compcert Require Import lib.Coqlib.
From compcert Require Import common.Errors.
From compcert Require Import common.AST.
From compcert Require Import common.Linking.
From compcert Require Import common.Smallstep.
From compcert Require Import common.Behaviors.

From compcert Require cfrontend.Clight.
From compcert Require Import driver.Compopts.
From compcert Require Import driver.Complements.
From compcert Require Import driver.Compiler.

(* we omit the prefix to be target-parametric *)
From compcert Require Asm.

(** Compilation from Clight to Asm *)

Definition transf_clight2_program (p: Clight.program) : res Asm.program :=
  OK p
  @@@ time "C#minor generation" Cshmgen.transl_program
  @@@ time "Cminor generation" Cminorgen.transl_program
  @@@ transf_cminor_program.

Local Open Scope linking_scope.

Definition clight2_to_asm_passes :=
      mkpass Cshmgenproof.match_prog
  ::: mkpass Cminorgenproof.match_prog
  ::: mkpass Selectionproof.match_prog
  ::: mkpass RTLgenproof.match_prog
  ::: mkpass (match_if Compopts.optim_tailcalls Tailcallproof.match_prog)
  ::: mkpass Inliningproof.match_prog
  ::: mkpass (match_if Compopts.profile_arcs Profilingproof.match_prog)
  ::: mkpass (match_if Compopts.branch_probabilities ProfilingExploitproof.match_prog)
  ::: mkpass (match_if Compopts.optim_move_loop_invariants FirstNopproof.match_prog)
  ::: mkpass Renumberproof.match_prog
  ::: mkpass (match_if Compopts.optim_duplicate Duplicateproof.match_prog)
  ::: mkpass Renumberproof.match_prog
  ::: mkpass (match_if Compopts.optim_constprop Constpropproof.match_prog)
  ::: mkpass Renumberproof.match_prog
  ::: mkpass (match_if Compopts.optim_CSE CSEproof.match_prog)
  ::: mkpass (match_if Compopts.optim_CSE2 CSE2proof.match_prog)
  ::: mkpass (match_if Compopts.optim_CSE3 CSE3proof.match_prog)
  ::: mkpass (match_if optim_forward_moves ForwardMovesproof.match_prog)
  ::: mkpass (match_if Compopts.optim_redundancy Deadcodeproof.match_prog)
  ::: mkpass (match_if Compopts.optim_move_loop_invariants LICMproof.match_prog)
  ::: mkpass (match_if Compopts.optim_move_loop_invariants Renumberproof.match_prog)
  ::: mkpass (match_if Compopts.optim_move_loop_invariants CSE3proof.match_prog)
  ::: mkpass (match_if Compopts.optim_move_loop_invariants Deadcodeproof.match_prog)
  ::: mkpass (match_if all_loads_nontrap Allnontrapproof.match_prog)
  ::: mkpass Unusedglobproof.match_prog
  ::: mkpass Allocationproof.match_prog
  ::: mkpass Tunnelingproof.match_prog
  ::: mkpass Linearizeproof.match_prog
  ::: mkpass CleanupLabelsproof.match_prog
  ::: mkpass (match_if Compopts.debug Debugvarproof.match_prog)
  ::: mkpass Stackingproof.match_prog
  ::: mkpass Asmgenproof.match_prog
  ::: pass_nil _.

(** Composing the [match_prog] relations above, we obtain the relation
  between Clight sources and Asm code that characterize CompCert's
  compilation. *)

Definition match_prog: Clight.program -> Asm.program -> Prop :=
  pass_match (compose_passes clight2_to_asm_passes).


(** The [transf_clight2_program] function, when successful, produces
  assembly code that is in the [match_prog] relation with the source C program. *)

Theorem transf_clight_program_match:
  forall p tp,
  transf_clight2_program p = OK tp ->
  match_prog p tp.
Proof.
  intros p tp T.
  unfold transf_clight2_program, time in T. simpl in T.
  destruct (Cshmgen.transl_program p) as [p3|e] eqn:P3; simpl in T; try discriminate.
  destruct (Cminorgen.transl_program p3) as [p4|e] eqn:P4; simpl in T; try discriminate.
  unfold transf_cminor_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  destruct (Selection.sel_program p4) as [p5|e] eqn:P5; simpl in T; try discriminate.
  destruct (RTLgen.transl_program p5) as [p6|e] eqn:P6; simpl in T; try discriminate.
  unfold transf_rtl_program, time in T. rewrite ! compose_print_identity in T. cbn in T.
  set (p7 := total_if optim_tailcalls Tailcall.transf_program p6) in *.
  destruct (Inlining.transf_program p7) as [p8|e] eqn:P8; cbn in T; try discriminate.
  set (p9 := total_if profile_arcs Profiling.transf_program p8) in *.
  set (p10 := total_if branch_probabilities ProfilingExploit.transf_program p9) in *.
  set (p11 := total_if optim_move_loop_invariants FirstNop.transf_program p10) in *.
  set (p12 := Renumber.transf_program p11) in *.
  destruct (partial_if optim_duplicate Duplicate.transf_program p12) as [p13|e] eqn:P13; cbn in T; try discriminate.
  set (p14 := Renumber.transf_program p13) in *.
  set (p15 := total_if optim_constprop Constprop.transf_program p14) in *.
  set (p16 := Renumber.transf_program p15) in *.
  destruct (partial_if optim_CSE CSE.transf_program p16) as [p17|e] eqn:P17; cbn in T; try discriminate.
  set (p18 := total_if optim_CSE2 CSE2.transf_program p17) in *.
  destruct (partial_if optim_CSE3 CSE3.transf_program p18) as [p19|e] eqn:P19; cbn in T; try discriminate.
  set (p20 := total_if optim_forward_moves ForwardMoves.transf_program p19) in *.
  destruct (partial_if optim_redundancy Deadcode.transf_program p20) as [p21|e] eqn:P21; cbn in T; try discriminate.
  destruct (partial_if optim_move_loop_invariants LICM.transf_program p21) as [p22|e] eqn:P22; cbn in T; try discriminate.
  set (p23 := total_if optim_move_loop_invariants Renumber.transf_program p22) in *.
  destruct (partial_if optim_move_loop_invariants CSE3.transf_program p23) as [p24|e] eqn:P24; cbn in T; try discriminate.
  destruct (partial_if optim_move_loop_invariants Deadcode.transf_program p24) as [p25|e] eqn:P25; simpl in T; try discriminate.
  set (p26 := total_if all_loads_nontrap Allnontrap.transf_program p25) in *.
  destruct (Unusedglob.transf_program p26) as [p27|e] eqn:P27; simpl in T; try discriminate.
  destruct (Allocation.transf_program p27) as [p28|e] eqn:P28; simpl in T; try discriminate.
  set (p29 := Tunneling.transf_program p28) in *.
  destruct (Linearize.transf_program p29) as [p30|e] eqn:P30; simpl in T; try discriminate.
  set (p31 := CleanupLabels.transf_program p30) in *.
  destruct (partial_if debug Debugvar.transf_program p31) as [p32|e] eqn:P32; simpl in T; try discriminate.
  destruct (Stacking.transf_program p32) as [p33|e] eqn:P33; simpl in T; try discriminate.
  unfold match_prog; simpl.
  exists p3; split. apply Cshmgenproof.transf_program_match; auto.
  exists p4; split. apply Cminorgenproof.transf_program_match; auto.
  exists p5; split. apply Selectionproof.transf_program_match; auto.
  exists p6; split. apply RTLgenproof.transf_program_match; auto.
  exists p7; split. apply total_if_match. apply Tailcallproof.transf_program_match.
  exists p8; split. apply Inliningproof.transf_program_match; auto.
  exists p9; split. apply total_if_match. apply Profilingproof.transf_program_match; auto.
  exists p10; split. apply total_if_match. apply ProfilingExploitproof.transf_program_match; auto.
  exists p11; split. apply total_if_match. apply FirstNopproof.transf_program_match; auto.
  exists p12; split. apply Renumberproof.transf_program_match; auto.
  exists p13; split. eapply partial_if_match; eauto. apply Duplicateproof.transf_program_match; auto.
  exists p14; split. apply Renumberproof.transf_program_match.
  exists p15; split. apply total_if_match. apply Constpropproof.transf_program_match.
  exists p16; split. apply Renumberproof.transf_program_match.
  exists p17; split. eapply partial_if_match; eauto. apply CSEproof.transf_program_match.
  exists p18; split. apply total_if_match. apply CSE2proof.transf_program_match.
  exists p19; split. eapply partial_if_match; eauto. apply CSE3proof.transf_program_match.
  exists p20; split. apply total_if_match. apply ForwardMovesproof.transf_program_match.
  exists p21; split. eapply partial_if_match; eauto. apply Deadcodeproof.transf_program_match.
  exists p22; split. eapply partial_if_match; eauto. apply LICMproof.transf_program_match.
  exists p23; split. apply total_if_match. apply Renumberproof.transf_program_match.
  exists p24; split. eapply partial_if_match; eauto. apply CSE3proof.transf_program_match.
  exists p25; split. eapply partial_if_match; eauto. apply Deadcodeproof.transf_program_match.
  exists p26; split. apply total_if_match. apply Allnontrapproof.transf_program_match.
  exists p27; split. apply Unusedglobproof.transf_program_match; auto.
  exists p28; split. apply Allocationproof.transf_program_match; auto.
  exists p29; split. apply Tunnelingproof.transf_program_match.
  exists p30; split. apply Linearizeproof.transf_program_match; auto.
  exists p31; split. apply CleanupLabelsproof.transf_program_match; auto.
  exists p32; split. eapply partial_if_match; eauto. apply Debugvarproof.transf_program_match.
  exists p33; split. apply Stackingproof.transf_program_match; auto.
  exists tp; split. apply Asmgenproof.transf_program_match; auto.
  reflexivity.
Qed.

(** Missing result from Clight.v: receptiveness of the Clight2 semantics *)

Lemma clight2_semantics_receptive:
  forall (p: Clight.program), receptive (Clight.semantics2 p).
Proof.
  intros. unfold Clight.semantics2.
  set (ge := Clight.globalenv p). constructor; simpl; intros.
(* receptiveness *)
  assert (t1 = Events.E0 -> exists s2, Clight.step2 ge s t2 s2).
    intros. subst. inv H0. exists s1; auto.
  inversion H; subst; auto.
  (* builtin *)
  exploit Events.external_call_receptive; eauto. intros [vres2 [m2 EC2]].
  econstructor; econstructor; eauto.
  (* external *)
  exploit Events.external_call_receptive; eauto. intros [vres2 [m2 EC2]].
  exists (Clight.Returnstate vres2 k m2). econstructor; eauto.
(* trace length *)
  red; simpl; intros. inv H; simpl; try omega.
  eapply Events.external_call_trace_length; eauto.
  eapply Events.external_call_trace_length; eauto.
Qed.

(** Semantic preservation (forward and backward simulation) between Clight and Asm *)

Theorem clight2_semantic_preservation:
  forall p tp,
  match_prog p tp ->
  forward_simulation (Clight.semantics2 p) (Asm.semantics tp) /\
  backward_simulation (Clight.semantics2 p) (Asm.semantics tp).
Proof.
  intros p tp M. unfold match_prog, pass_match in M; simpl in M.
Ltac DestructM :=
  match goal with
    [ H: exists p, _ /\ _ |- _ ] =>
      let p := fresh "p" in let M := fresh "M" in let MM := fresh "MM" in
      destruct H as (p & M & MM); clear H
  end.
  repeat DestructM. subst tp.
  assert (F: forward_simulation (Clight.semantics2 p) (Asm.semantics p32)).
  {
  eapply compose_forward_simulations.
    eapply Cshmgenproof.transl_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Cminorgenproof.transl_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Selectionproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply RTLgenproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Tailcallproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply Inliningproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Profilingproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact ProfilingExploitproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact FirstNopproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply Renumberproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Duplicateproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply Renumberproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Constpropproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply Renumberproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact CSEproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact CSE2proof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact CSE3proof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact ForwardMovesproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Deadcodeproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact LICMproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Renumberproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact CSE3proof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Deadcodeproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Allnontrapproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply Unusedglobproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Allocationproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Tunnelingproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Linearizeproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply CleanupLabelsproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Debugvarproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply Stackingproof.transf_program_correct.
      exact Asmgenproof.return_address_exists.
      eassumption.
  eapply Asmgenproof.transf_program_correct; eassumption.
  }
  split. auto.
  apply forward_to_backward_simulation.
  exact F.
  apply clight2_semantics_receptive.
  apply Asm.semantics_determinate.
Qed.

(** The corollary for Tim and Lelio *)

Theorem diverges_trace_preservation:
  forall p tp,
  transf_clight2_program p = OK tp ->
  forall t,
  program_behaves (Clight.semantics2 p) (Diverges t) -> program_behaves (Asm.semantics tp) (Diverges t).
Proof.
  intros.
  assert (M: match_prog p tp) by (apply transf_clight_program_match; auto).
  exploit clight2_semantic_preservation; eauto. intros [FWD BACK].
  exploit forward_simulation_behavior_improves; eauto. intros (beh & B & I).
  inv I. auto. destruct H1 as (? & ? & ?); discriminate.
Qed.

Theorem reacts_trace_preservation:
  forall p tp,
  transf_clight2_program p = OK tp ->
  forall T,
  program_behaves (Clight.semantics2 p) (Reacts T) -> program_behaves (Asm.semantics tp) (Reacts T).
Proof.
  intros.
  assert (M: match_prog p tp) by (apply transf_clight_program_match; auto).
  exploit clight2_semantic_preservation; eauto. intros [FWD BACK].
  exploit forward_simulation_behavior_improves; eauto. intros (beh & B & I).
  inv I. auto. destruct H1 as (t & ? & ?); discriminate.
Qed.
