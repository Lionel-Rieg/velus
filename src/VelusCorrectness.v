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
From Velus Require Import Ident.
From Velus Require Import CoindStreams.
From Velus Require Import ObcToClight.Generation.
From Velus Require Import Traces.
From Velus Require Import ClightToAsm.

From compcert Require Import common.Errors.
From compcert Require Import common.Events.
From compcert Require Import common.Behaviors.
From compcert Require Import cfrontend.Clight.
From compcert Require Import cfrontend.ClightBigstep.
From compcert Require Import lib.Integers.
From compcert Require Import driver.Compiler.

From Velus Require Import Interface.
From Velus Require Import Instantiator.
Import Stc.Syn.
Import NL.
Import Obc.Syn.
Import Obc.Sem.
Import Obc.Typ.
Import Obc.Equ.
Import Obc.Def.
Import Fusion.
Import Stc2ObcInvariants.
Import IStr.
Import CStr.
Import OpAux.
Import Op.
From Velus Require Import ObcToClight.Correctness.
From Velus Require Import NLustre.NLElaboration.

From Coq Require Import String.
From Coq Require Import List.
Import List.ListNotations.
From Coq Require Import Omega.

Open Scope error_monad_scope.
Open Scope stream_scope.

Parameter schedule      : ident -> list trconstr -> list positive.
Parameter print_nlustre : global -> unit.
Parameter print_stc     : Stc.Syn.program -> unit.
Parameter print_sch     : Stc.Syn.program -> unit.
Parameter print_obc     : Obc.Syn.program -> unit.
Parameter do_fusion     : unit -> bool.
Parameter do_sync       : unit -> bool.
Parameter do_expose     : unit -> bool.

Module ExternalSchedule.
  Definition schedule := schedule.
End ExternalSchedule.

Module Scheduler := Stc.Scheduler ExternalSchedule.

Definition is_well_sch_system (r: res unit) (s: system) : res unit :=
  do _ <- r;
    let args := map fst s.(s_in) in
    let mems := ps_from_list (map fst s.(s_lasts)) in
    if Stc.Wdef.well_sch mems args s.(s_tcs)
    then OK tt
    else Error (Errors.msg ("system " ++ pos_to_str s.(s_name) ++ " is not well scheduled.")).

Definition is_well_sch (P: Stc.Syn.program) : res Stc.Syn.program :=
  do _ <- fold_left is_well_sch_system P (OK tt);
    OK P.

Lemma is_well_sch_error:
  forall G e,
    fold_left is_well_sch_system G (Error e) = Error e.
Proof.
  induction G as [|n G]; simpl; auto.
Qed.

Lemma is_well_sch_program:
  forall P,
    fold_left is_well_sch_system P (OK tt) = OK tt ->
    Stc.Wdef.Well_scheduled P.
Proof.
  unfold Stc.Wdef.Well_scheduled.
  induction P as [|s]; simpl.
  - constructor.
  - intro Fold.
    destruct (Stc.Wdef.well_sch (ps_from_list (map fst (Stc.Syn.s_lasts s)))
                               (map fst (Stc.Syn.s_in s)) (Stc.Syn.s_tcs s)) eqn: E.
    + apply Stc.Wdef.Is_well_sch_by_refl in E.
      constructor; auto.
    + rewrite is_well_sch_error in Fold; discriminate.
Qed.

Definition schedule_program (P: Stc.Syn.program) : res Stc.Syn.program :=
  is_well_sch (Scheduler.schedule P).

Definition nl_to_cl (main_node: ident) (g: global) : res Clight.program :=
  OK g
     @@ print print_nlustre
     @@ NL2Stc.translate
     @@ print print_stc
     @@@ schedule_program
     @@ print print_sch
     @@ Stc2Obc.translate
     @@ total_if do_fusion (map Obc.Fus.fuse_class)
     @@ add_defaults
     @@ print print_obc
     @@@ Generation.translate (do_sync tt) (do_expose tt) main_node.

Axiom add_builtins: Clight.program -> Clight.program.
Axiom add_builtins_spec:
  forall B p,
    (forall t, B <> Goes_wrong t) ->
    program_behaves (semantics2 p) B -> program_behaves (semantics2 (add_builtins p)) B.

Definition nl_to_asm (main_node: ident) (g: global) : res Asm.program :=
  OK g
     @@@ nl_to_cl main_node
     @@ print print_Clight
     @@ add_builtins
     @@@ transf_clight2_program.

Definition compile (D: list LustreAst.declaration) (main_node: ident) : res Asm.program :=
  elab_declarations D
                    (* @@@ (fun G => L2NL.to_global (proj1_sig G)) *)
                    @@@ (fun G => nl_to_asm main_node (proj1_sig G)).

Section ForallStr.
  Context {A: Type}.
  Variable P: A -> Prop.
  CoInductive Forall_Str: Stream A -> Prop :=
  Always:
    forall x xs,
      P x ->
      Forall_Str xs ->
      Forall_Str (x ⋅ xs).

  Lemma Forall_Str_nth:
    forall s,
      Forall_Str s <-> (forall n, P (s # n)).
  Proof.
    split.
    - intros H n.
      revert dependent s; induction n; intros.
      + inv H; rewrite Str_nth_0; auto.
      + destruct s; rewrite Str_nth_S.
        inv H; auto.
    - revert s; cofix CoFix; intros * H.
      destruct s.
      constructor.
      + specialize (H 0); rewrite Str_nth_0 in H; auto.
      + apply CoFix.
        intro n; specialize (H (S n)); rewrite Str_nth_S in H; auto.
  Qed.
End ForallStr.

Definition wt_streams: list (Stream val) -> list (ident * type) -> Prop :=
  Forall2 (fun s xt => Forall_Str (fun v => wt_val v (snd xt)) s).

Lemma wt_streams_spec:
  forall vss xts,
    wt_streams vss xts <->
    forall n, wt_vals (tr_Streams vss n) xts.
Proof.
  unfold wt_vals.
  split.
  - intros * WTs n; revert dependent vss; induction n; intros.
    + rewrite tr_Streams_hd.
      induction WTs as [|???? WT]; simpl; auto.
      constructor; auto.
      inv WT; auto.
    + rewrite <-tr_Streams_tl.
      apply IHn.
      clear - WTs; induction WTs as [|???? WT]; simpl;
        constructor; auto.
      inv WT; auto.
  - intros WTs.
    unfold wt_streams.
    revert dependent vss.
    induction xts, vss; intros; try now (specialize (WTs 0); simpl in WTs; inv WTs).
    constructor; auto.
    + rewrite Forall_Str_nth; intro n; specialize (WTs n); inv WTs; auto.
    + apply IHxts; intro n; specialize (WTs n); inv WTs; auto.
Qed.

Section WtStream.

  Variable G: global.
  Variable main: ident.
  Variable ins: list (Stream val).
  Variable outs: list (Stream val).

  Definition wt_ins :=
    forall node,
      find_node main G = Some node ->
      wt_streams ins (idty node.(n_in)).

  Definition wt_outs :=
    forall node,
      find_node main G = Some node ->
      wt_streams outs (idty node.(n_out)).

End WtStream.

Hint Resolve
     Obc.Fus.fuse_wt_program
     Obc.Fus.fuse_call
     Obc.Fus.fuse_wt_mem
     Obc.Fus.fuse_loop_call
(*      NL2StcTyping.translate_wt *)
(*      Scheduler.scheduler_wt_program *)
     (*      Stc2ObcTyping.translate_wt *)
     wt_add_defaults_class
     wt_mem_add_defaults
     stmt_call_eval_add_defaults
     loop_call_add_defaults
     ClassFusible_translate
     Scheduler.scheduler_wc_program
     NL2StcClocking.translate_wc
     No_Naked_Vars_add_defaults_class
     Obc.Fus.fuse_No_Overwrites
     translate_No_Overwrites
     Obc.Fus.fuse_cannot_write_inputs
     translate_cannot_write_inputs
  : core.

(** The trace of a NLustre node *)
Section NLTrace.

  Variable (node: node) (ins outs: list (Stream val)).

  Hypothesis Spec_in_out : node.(n_in) <> [] \/ node.(n_out) <> [].
  Hypothesis Len_ins     : Datatypes.length ins = Datatypes.length node.(n_in).
  Hypothesis Len_outs    : Datatypes.length outs = Datatypes.length node.(n_out).

  Program Definition trace_node (n: nat): traceinf :=
    traceinf_of_traceinf' (mk_trace (tr_Streams ins) (tr_Streams outs)
                                    (idty node.(n_in)) (idty node.(n_out))
                                    _ _ _ n).
  Next Obligation.
    destruct Spec_in_out.
    - left; intro E; apply map_eq_nil in E; auto.
    - right; intro E; apply map_eq_nil in E; auto.
  Qed.
  Next Obligation.
    unfold tr_Streams, idty; rewrite 2 map_length; auto.
  Qed.
  Next Obligation.
    unfold tr_Streams, idty; rewrite 2 map_length; auto.
  Qed.

  (** Simply link the trace of a Lustre node with the trace of an Obc step method with the same parameters *)
  Lemma trace_inf_sim_step_node:
    forall n m Spec_in_out_m Len_ins_m Len_outs_m,
      m_in m = idty (n_in node) ->
      m_out m = idty (n_out node) ->
      traceinf_sim (trace_step m (tr_Streams ins) (tr_Streams outs) Spec_in_out_m Len_ins_m Len_outs_m n)
                   (trace_node n).
  Proof.
    intros; unfold trace_step, trace_node.
    apply traceinf_sim'_sim.
    revert n; cofix COFIX; intro.
    rewrite unfold_mk_trace.
    rewrite unfold_mk_trace with (xs := idty (n_in node)).
    simpl.
    replace (load_events (tr_Streams ins n) (idty (n_in node)) ** store_events (tr_Streams outs n) (idty (n_out node)))
      with (load_events (tr_Streams ins n) (m_in m) ** store_events (tr_Streams outs n) (m_out m)); try congruence.
    constructor.
    - intro E; eapply Eapp_E0_inv in E.
      pose proof (load_store_events_not_E0 _ _ _ _ Spec_in_out_m Len_ins_m Len_outs_m n).
      intuition.
    - apply COFIX.
  Qed.

End NLTrace.

(** A bisimulation relation between a declared node's trace and a given trace *)
Inductive bisim_IO (G: global) (f: ident) (ins outs: list (Stream val)): traceinf -> Prop :=
  IOStep:
    forall T node
      (Spec_in_out : node.(n_in) <> [] \/ node.(n_out) <> [])
      (Len_ins     : Datatypes.length ins = Datatypes.length node.(n_in))
      (Len_outs    : Datatypes.length outs = Datatypes.length node.(n_out)),
      find_node f G = Some node ->
      traceinf_sim T (trace_node node ins outs Spec_in_out Len_ins Len_outs 0) ->
      bisim_IO G f ins outs T.

(** streams of present values *)
Definition pstr (xss: stream (list val)) : stream (list value) :=
  fun n => map present (xss n).
Definition pStr: list (Stream val) -> list (Stream value) := map (Streams.map present).

Lemma tr_Streams_pStr:
  forall xss,
    tr_Streams (pStr xss) ≈ pstr (tr_Streams xss).
Proof.
  intros ? n; unfold pstr, pStr.
  revert xss; induction n; intros.
  - rewrite 2 tr_Streams_hd, 2 map_map; induction xss; simpl; auto.
  - rewrite <-2 tr_Streams_tl.
    rewrite <-IHn, 2 map_map; auto.
Qed.

Lemma value_to_option_pstr:
  forall xs,
    (fun n => map Stc2ObcCorr.value_to_option (pstr xs n)) ≈ (fun n => map Some (xs n)).
Proof.
  intros; unfold Stc2ObcCorr.value_to_option, pstr; intro.
  rewrite map_map; auto.
Qed.

(** Correctness from NLustre to Clight *)
Lemma behavior_nl_to_cl:
  forall G P main ins outs,
    wc_global G ->
    wt_global G ->
    wt_ins G main ins ->
    normal_args G ->
    CoindSem.sem_node G main (pStr ins) (pStr outs) ->
    nl_to_cl main G = OK P ->
    exists T, program_behaves (semantics2 P) (Reacts T)
         /\ bisim_IO G main ins outs T.
Proof.
  intros * Hwc Hwt Hwti Hnorm Hsem COMP.
  unfold nl_to_cl in COMP.
  simpl in COMP; repeat rewrite print_identity in COMP.

  (* well-scheduled Stc program *)
  destruct (schedule_program (NL2Stc.translate G)) eqn: Sch;
    simpl in COMP; try discriminate.
  unfold schedule_program, is_well_sch in Sch; simpl in Sch.
  destruct (fold_left is_well_sch_system (Scheduler.schedule (NL2Stc.translate G))
                      (OK tt)) eqn: Wsch; simpl in *; try discriminate; destruct u.
  inv Sch.
  apply is_well_sch_program in Wsch.

  (* a main Stc system exists *)
  repeat rewrite print_identity in COMP.
  pose proof COMP as COMP'.
  assert (exists n, find_node main G = Some n) as (main_node & Find)
      by (inv Hsem; eauto).
  pose proof Find as Find_node.
  apply NL2Stc.find_node_translate in Find as (bl & P' & Find& ?); subst.
  apply Scheduler.scheduler_find_system in Find.

  (* a main Obc class exists *)
  apply Stc2Obc.find_system_translate in Find as (?&?& Find &?&?); subst.

  (* Coinductive NLustre to nat->values *)
  assert (Ordered_nodes G) by (eapply wt_global_Ordered_nodes; eauto).
  apply implies in Hsem.
  rewrite 2 tr_Streams_pStr in Hsem.

  set (ins' := tr_Streams ins) in *;
    set (outs' := tr_Streams outs) in *.
  assert (forall n, 0 < length (ins' n)) as Length.
  { inversion_clear Hsem as [???????? Ins].
    intro k; specialize (Ins k); apply Forall2_length in Ins.
    unfold pstr in Ins; rewrite 2 map_length in Ins.
    rewrite <-Ins.
    apply n_ingt0.
  }

  (* NLustre to Nlustre with memory *)
  apply sem_msem_node in Hsem as (M & Hsem); auto.

  (* NLustre with memory to Stc loop *)
  assert (Stc.Wdef.Well_defined (Scheduler.schedule (NL2Stc.translate G))).
  { split; [|split]; auto.
    - apply Scheduler.scheduler_ordered, NL2StcCorr.Ordered_nodes_systems; auto.
    - apply Scheduler.scheduler_normal_args, NL2StcNormalArgs.translate_normal_args; auto.
  }
  apply NL2StcCorr.correctness_loop in Hsem as (?& Hsem); auto.
  apply Scheduler.scheduler_loop in Hsem; auto.

  assert (forall n, Forall2 Stc2ObcCorr.eq_if_present (pstr ins' n) (map Some (ins' n)))
    by (unfold pstr; intros; clear; induction (ins' n); constructor; simpl; auto).
  assert (forall n, Exists (fun v => v <> absent) (pstr ins' n))
         by (unfold pstr; intros; specialize (Length n);
             destruct (ins' n); simpl in *; try omega;
             constructor; discriminate).

  (* Stc loop to Obc loop *)
  apply Stc2ObcCorr.correctness_loop_call with (ins := fun n => map Some (ins' n))
    in Hsem as (me0 & Rst & Hsem &?); auto.
  setoid_rewrite value_to_option_pstr in Hsem.

  (* aliases *)
  set (tr_G := NL2Stc.translate G) in *;
    set (sch_tr_G := Scheduler.schedule tr_G) in *;
    set (tr_sch_tr_G := Stc2Obc.translate sch_tr_G) in *;
    set (tr_main_node := NL2Stc.translate_node main_node) in *;
    set (sch_tr_main_node := Scheduler.schedule_system tr_main_node) in *.

  (* Obc methods step and reset *)
  pose proof (Stc2Obc.exists_reset_method sch_tr_main_node) as Find_reset.
  pose proof (Stc2Obc.exists_step_method sch_tr_main_node) as Find_step.
  set (m_step := Stc2Obc.step_method sch_tr_main_node) in *;
    set (m_reset := Stc2Obc.reset_method sch_tr_main_node) in *.

  (* well-typing *)
  assert (wt_program tr_sch_tr_G)
    by (apply Stc2ObcTyping.translate_wt, Scheduler.scheduler_wt_program,
        NL2StcTyping.translate_wt; auto).
  assert (wt_mem me0 (Stc2Obc.translate (Scheduler.schedule P'))
                 (Stc2Obc.translate_system sch_tr_main_node))
    by (eapply pres_sem_stmt_call with (f := reset) in Find as (? & ?);
        eauto; simpl; constructor).
  assert (wt_outs G main outs) as Hwto.
  { unfold wt_outs.
    intros * Find_node'; rewrite Find_node' in Find_node; inv Find_node.
    apply wt_streams_spec.
    intro n.
    eapply pres_loop_call with (n := n) in Hsem; eauto.
    - rewrite Forall2_map_1 in Hsem; simpl in Hsem; auto.
    - apply Hwti in Find_node'.
      rewrite wt_streams_spec in Find_node'.
      setoid_rewrite Forall2_map_1; eauto.
  }

  (* IO specs *)
  assert (n_in main_node <> [] \/ n_out main_node <> []) as Step_in_out_spec'.
  { left. pose proof (n_ingt0 main_node) as Hin.
    intro E; rewrite E in Hin; simpl in Hin; omega.
  }
  assert (m_in m_step <> nil \/ m_out m_step <> nil) as Step_in_out_spec.
  { erewrite Stc2Obc.find_method_stepm_in, Stc2Obc.find_method_stepm_out; eauto.
    simpl; destruct Step_in_out_spec'.
    - left; intro E; apply map_eq_nil in E; intuition.
    - right; intro E; apply map_eq_nil in E; intuition.
  }
  assert (forall n, wt_vals (ins' n) (m_in m_step)) as Hwt_in
      by (erewrite Stc2Obc.find_method_stepm_in; eauto;
          apply wt_streams_spec, Hwti; auto).
  assert (forall n, wt_vals (outs' n) (m_out m_step)) as Hwt_out
      by (erewrite Stc2Obc.find_method_stepm_out; eauto;
          apply wt_streams_spec, Hwto; auto).
  assert (m_in m_step = idty main_node.(n_in)) as Ein by auto.
  assert (m_out m_step = idty main_node.(n_out)) as Eout by auto.
  assert (Datatypes.length ins = Datatypes.length (n_in main_node)) as Len_ins.
  { transitivity (Datatypes.length (idty main_node.(n_in))); try apply map_length.
    rewrite <-Ein.
    specialize (Hwt_in 0); unfold ins' in Hwt_in; setoid_rewrite Forall2_map_1 in Hwt_in.
    eapply Forall2_length; eauto.
  }
  assert (Datatypes.length outs = Datatypes.length (n_out main_node)) as Len_outs.
 { transitivity (Datatypes.length (idty main_node.(n_out))); try apply map_length.
    rewrite <-Eout.
    specialize (Hwt_out 0); unfold outs' in Hwt_out; setoid_rewrite Forall2_map_1 in Hwt_out.
    eapply Forall2_length; eauto.
  }

  (* proceed to monadic compilation to Clight *)
  unfold Generation.translate in COMP.
  unfold total_if in *.
  destruct (do_fusion tt); clear COMP.

  (* activated Fusion optimization *)
  - (* assert some equalities between classes and methods *)
    Opaque add_defaults_class Obc.Fus.fuse_class Obc.Fus.fuse_method.
    pose proof (GenerationProperties.find_main_class _ _ _ _ _ COMP') as Find'.
    apply Obc.Fus.fuse_find_class, find_class_add_defaults_class in Find.
    rewrite Find in Find'; injection Find'; intros Eq_prog Eq_main.

    pose proof (GenerationProperties.find_main_step _ _ _ _ _ COMP') as Find_step'.
    rewrite <-Eq_main in Find_step'; rewrite add_defaults_class_find_method in Find_step'.
    apply Obc.Fus.fuse_find_method' in Find_step.
    rewrite Find_step in Find_step'; simpl option_map in Find_step'; injection Find_step'; intros Eq_step.
    clear Find Find' Find_step Find_step'.

    rewrite <-Obc.Fus.fuse_method_in, <-add_defaults_method_m_in, Eq_step in Step_in_out_spec, Hwt_in, Ein;
      rewrite <-Obc.Fus.fuse_method_out, <-add_defaults_method_m_out, Eq_step in Step_in_out_spec, Hwt_out, Eout.

    assert (Forall_methods (fun m => Obc.Inv.No_Overwrites (m_body m)) (map Obc.Fus.fuse_class tr_sch_tr_G))
           by (apply Obc.Fus.fuse_No_Overwrites, translate_No_Overwrites; auto).
    assert (Forall_methods
              (fun m => Forall (fun x => ~ Obc.Inv.Can_write_in x (m_body m)) (map fst (m_in m)))
              (map Obc.Fus.fuse_class tr_sch_tr_G))
      by (apply Obc.Fus.fuse_cannot_write_inputs, translate_cannot_write_inputs).
    econstructor; split.
    + assert (Forall Obc.Fus.ClassFusible tr_sch_tr_G)
        by (apply ClassFusible_translate; auto;
            apply Scheduler.scheduler_wc_program; eauto;
            apply NL2StcClocking.translate_wc; auto).
      eapply correctness with (TRANSL := COMP') (me0 := me0)
                              (WTins := Hwt_in) (WTouts := Hwt_out)
                              (Step_in_out_spec := Step_in_out_spec); eauto.
      * intros ??????? Call; eapply stmt_call_eval_add_defaults_class_not_None with (3 := Call); eauto.
      * change [] with (map Some (@nil val)); eauto.
      * rewrite <-Eq_prog, <-Eq_main; eauto.
    + apply IOStep with (Spec_in_out := Step_in_out_spec') (Len_ins := Len_ins) (Len_outs := Len_outs); auto.
      apply trace_inf_sim_step_node; auto.

  (* activated Fusion optimization *)
  - (* assert some equalities between classes and methods *)
    pose proof (GenerationProperties.find_main_class _ _ _ _ _ COMP') as Find'.
    apply find_class_add_defaults_class in Find.
    rewrite Find in Find'; injection Find'; intros Eq_prog Eq_main.

    Opaque add_defaults_method.
    pose proof (GenerationProperties.find_main_step _ _ _ _ _ COMP') as Find_step'.
    rewrite <-Eq_main in Find_step'; rewrite add_defaults_class_find_method in Find_step'.
    rewrite Find_step in Find_step'; simpl option_map in Find_step'; injection Find_step'; intros Eq_step.

    rewrite <-add_defaults_method_m_in, Eq_step in Step_in_out_spec, Hwt_in, Ein;
      rewrite <-add_defaults_method_m_out, Eq_step in Step_in_out_spec, Hwt_out, Eout.

    assert (Forall_methods (fun m => Obc.Inv.No_Overwrites (m_body m)) tr_sch_tr_G)
      by (apply translate_No_Overwrites; auto).
    assert (Forall_methods
              (fun m => Forall (fun x => ~ Obc.Inv.Can_write_in x (m_body m)) (map fst (m_in m)))
              tr_sch_tr_G)
           by (apply translate_cannot_write_inputs).
    econstructor; split.
    + eapply correctness with (TRANSL := COMP') (me0 := me0)
                              (WTins := Hwt_in) (WTouts := Hwt_out)
                              (Step_in_out_spec := Step_in_out_spec); eauto.
      * intros ??????? Call; eapply stmt_call_eval_add_defaults_class_not_None with (3 := Call); eauto.
      * change [] with (map Some (@nil val)); eauto.
      * rewrite <-Eq_prog, <-Eq_main; eauto.
    + apply IOStep with (Spec_in_out := Step_in_out_spec') (Len_ins := Len_ins) (Len_outs := Len_outs); auto.
      apply trace_inf_sim_step_node; auto.
Qed.

(** Correctness from NLustre to ASM  *)
Lemma behavior_nl_to_asm:
  forall G P main ins outs,
    wc_global G ->
    wt_global G ->
    wt_ins G main ins ->
    normal_args G ->
    CoindSem.sem_node G main (pStr ins) (pStr outs) ->
    nl_to_asm main G = OK P ->
    exists T, program_behaves (Asm.semantics P) (Reacts T)
         /\ bisim_IO G main ins outs T.
Proof.
  unfold nl_to_asm; simpl.
  intros * ????? Comp.
  destruct (nl_to_cl main G) as [p|] eqn: Comp'; simpl in Comp; try discriminate.
  eapply  behavior_nl_to_cl in Comp' as (T & Beh & Bisim); eauto.
  eapply reacts_trace_preservation in Comp; eauto.
  apply add_builtins_spec; auto.
  intros ? ?; discriminate.
Qed.

(** The ultimate lemma states that, if
    - the parsed declarations [D] elaborate to a dataflow program [G] and
      a proof [Gp] that it satisfies [wt_global G] and [wc_global G],
    - the values on input streams [ins] are well-typed according to the
      interface of the [main] node,
    - similarly for output streams [outs],
    - the input and output streams are related by the dataflow semantics
      of the node [main] in [G], and
    - compilation succeeds in generating an assembler program [P],
    then the assembler program generates an infinite sequence of volatile
    reads and writes that correspond to the successive values on the
    input and output streams. *)

Theorem correctness:
  forall D G Gp P main ins outs,
    elab_declarations D = OK (exist _ G Gp) ->
    wt_ins G main ins ->
    CoindSem.sem_node G main (pStr ins) (pStr outs) ->
    compile D main = OK P ->
    exists T, program_behaves (Asm.semantics P) (Reacts T)
         /\ bisim_IO G main ins outs T.
Proof.
  intros D G (WT & WC & NormalArgs) P main ins outs Elab ?? Comp.
  unfold compile in Comp.
  rewrite Elab in Comp; simpl in Comp.
  apply behavior_nl_to_asm; eauto.
Qed.
