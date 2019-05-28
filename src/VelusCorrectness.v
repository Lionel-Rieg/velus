From Velus Require Import Common.
From Velus Require Import Ident.
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

From Velus Require Import Instantiator.
Import SB.Syn.
Import NL.
Import Obc.Syn.
Import Obc.Sem.
Import Obc.Typ.
Import Obc.Equ.
Import Obc.Def.
Import Fusion.
Import SB2ObcInvariants.
Import Str.
Import OpAux.
Import Interface.Op.
From Velus Require Import ObcToClight.Correctness.
From Velus Require Import Lustre.LustreElab.

From Coq Require Import String.
From Coq Require Import List.
Import List.ListNotations.
From Coq Require Import Omega.

Open Scope error_monad_scope.

Parameter schedule      : ident -> list SB.Syn.equation -> list positive.
Parameter print_nlustre : global -> unit.
Parameter print_sybloc  : SB.Syn.program -> unit.
Parameter print_obc     : Obc.Syn.program -> unit.
Parameter do_fusion     : unit -> bool.
Parameter do_sync       : unit -> bool.
Parameter do_expose     : unit -> bool.

Module ExternalSchedule.
  Definition schedule := schedule.
End ExternalSchedule.

Module Scheduler := SB.Scheduler ExternalSchedule.

Definition is_well_sch_block (r: res unit) (b: block) : res unit :=
  do _ <- r;
    let args := map fst b.(b_in) in
    let mems := ps_from_list (map fst b.(b_lasts)) in
    if SB.Wdef.well_sch mems args b.(b_eqs)
    then OK tt
    else Error (Errors.msg ("block " ++ pos_to_str b.(b_name) ++ " is not well scheduled.")).

Definition is_well_sch (P: SB.Syn.program) : res SB.Syn.program :=
  do _ <- fold_left is_well_sch_block P (OK tt);
    OK P.

Lemma is_well_sch_error:
  forall G e,
    fold_left is_well_sch_block G (Error e) = Error e.
Proof.
  induction G as [|n G]; simpl; auto.
Qed.

Lemma is_well_sch_program:
  forall P,
    fold_left is_well_sch_block P (OK tt) = OK tt ->
    SB.Wdef.Well_scheduled P.
Proof.
  unfold SB.Wdef.Well_scheduled.
  induction P as [|bl]; simpl.
  - constructor.
  - intro Fold.
    destruct (SB.Wdef.well_sch (ps_from_list (map fst (SB.Syn.b_lasts bl)))
                               (map fst (SB.Syn.b_in bl)) (SB.Syn.b_eqs bl)) eqn: E.
    + apply SB.Wdef.Is_well_sch_by_refl in E; constructor; auto.
    + rewrite is_well_sch_error in Fold; discriminate.
Qed.

Definition schedule_program (P: SB.Syn.program) : res SB.Syn.program :=
  is_well_sch (Scheduler.schedule P).

Definition nl_to_cl (main_node: ident) (g: global): res Clight.program :=
  OK g
     @@ print print_nlustre
     @@ NL2SB.translate
     @@ print print_sybloc
     @@@ schedule_program
     @@ SB2Obc.translate
     @@ total_if do_fusion (map Obc.Fus.fuse_class)
     @@ add_defaults
     @@ print print_obc
     @@@ Generation.translate (do_sync tt) (do_expose tt) main_node.

Axiom add_builtins: Clight.program -> Clight.program.
Axiom add_builtins_spec:
  forall B p,
    (forall t, B <> Goes_wrong t) ->
    program_behaves (semantics2 p) B -> program_behaves (semantics2 (add_builtins p)) B.

Definition compile (D: list LustreAst.declaration) (main_node: ident) : res Asm.program :=
  elab_declarations D
                    @@@ (fun G => L2NL.to_global (proj1_sig G))
                    @@@ nl_to_cl main_node
                    @@ print print_Clight
                    @@ add_builtins
                    @@@ transf_clight2_program.

Section WtStream.

  Variable G: global.
  Variable main: ident.
  Variable ins: stream (list val).
  Variable outs: stream (list val).

  Definition wt_ins :=
    forall n node,
      find_node main G = Some node ->
      wt_vals (ins n) (idty node.(n_in)).

  Definition wt_outs :=
    forall n node,
      find_node main G = Some node ->
      wt_vals (outs n) (idty node.(n_out)).

End WtStream.

Section Bisim.

  Variable G: global.
  Variable main: ident.
  Variable ins: stream (list val).
  Variable outs: stream (list val).

  Inductive eventval_match: eventval -> AST.typ -> Values.val -> Prop :=
  | ev_match_int: forall i,
      eventval_match (EVint i) AST.Tint (Values.Vint i)
  | ev_match_long: forall i,
      eventval_match (EVlong i) AST.Tlong (Values.Vlong i)
  | ev_match_float: forall f,
      eventval_match (EVfloat f) AST.Tfloat (Values.Vfloat f)
  | ev_match_single: forall f,
      eventval_match (EVsingle f) AST.Tsingle (Values.Vsingle f).

  Lemma eventval_match_of_val:
    (** All well-typed, dataflow values can be turned into event values. *)
    forall v t,
      wt_val v t ->
      eventval_match (eventval_of_val v)
                     (AST.type_of_chunk (type_chunk t))
                     v.
  Proof.
    intros v t Hwt.
    inversion Hwt; try constructor.
    destruct sz; destruct sg; try constructor.
  Qed.

  Remark eventval_match_compat:
    (** [eventval_match] is a stripped-down version of CompCert's [Events.eventval_match] *)
    forall ge ev t v,
      eventval_match ev t v -> Events.eventval_match ge ev t v.
  Proof. inversion 1; constructor. Qed.


  Inductive mask (f: eventval -> ident * type -> event):
    list Values.val -> list (ident * type) -> trace -> Prop :=
  | MaskNil:
      mask f [] [] []
  | MaskCons:
      forall v vs x t xts ev evtval T,
        eventval_match evtval (AST.type_of_chunk (type_chunk t)) v ->
        f evtval (x, t) = ev ->
        mask f vs xts T ->
        mask f (v :: vs) ((x, t) :: xts) (ev :: T).

  Definition mask_load :=
    (** Match a list of events loading values from the suitable, global
  volatile variables *)
    mask (fun ev xt => Event_vload (type_chunk (snd xt))
                                (glob_id (fst xt))
                                Ptrofs.zero ev).

  Definition mask_store :=
    (** Match a list of events storing values to the suitable, global
  volatile variables *)
    mask (fun ev xt => Event_vstore (type_chunk (snd xt))
                                 (glob_id (fst xt))
                                 Ptrofs.zero ev).

  Lemma mk_event_spec:
    (** The trace generated by [mk_event] is characterized by [mask] *)
    forall (f: eventval -> ident * type -> event) vs xts,
      wt_vals vs xts ->
      mask f vs xts (mk_event (fun v => f (eventval_of_val v)) vs xts).
  Proof.
    intros * Hwt. generalize dependent xts.
    induction vs as [|v vs IHvs];
      intros xts Hwt; destruct xts as [|[x t] xts];
        inv Hwt; try constructor.
    rewrite Traces.mk_event_cons.
    apply MaskCons with (evtval := eventval_of_val v);
      eauto using eventval_match_of_val.
  Qed.


  (** The trace of events induced by the execution of the Clight program
corresponds to an infinite stream that alternates between loads and
stores of the values passed and, respectively, retrieved from the
dataflow node at each instant. *)

  CoInductive bisim_io': nat -> traceinf -> Prop :=
    Step:
      forall n node t t' T,
        find_node main G = Some node ->
        mask_load (ins n) (idty node.(n_in)) t ->
        mask_store (outs n) (idty node.(n_out)) t' ->
        bisim_io' (S n) T ->
        bisim_io' n (t *** t' *** T).

  Definition bisim_io := bisim_io' 0.

End Bisim.

Hint Resolve
     Obc.Fus.fuse_wt_program
     Obc.Fus.fuse_call
     Obc.Fus.fuse_wt_mem
     Obc.Fus.fuse_loop_call
(*      NL2SBTyping.translate_wt *)
(*      Scheduler.scheduler_wt_program *)
     (*      SB2ObcTyping.translate_wt *)
     wt_add_defaults_class
     wt_mem_add_defaults
     stmt_call_eval_add_defaults
     loop_call_add_defaults
     ClassFusible_translate
     Scheduler.scheduler_wc_program
     NL2SBClocking.translate_wc
     No_Naked_Vars_add_defaults_class
     stmt_call_eval_add_defaults
     Obc.Fus.fuse_No_Overwrites
     translate_No_Overwrites
     Obc.Fus.fuse_cannot_write_inputs
     translate_cannot_write_inputs
.

Lemma find_node_trace_spec:
  forall G f node ins outs m
    (Step_in_spec : m_in m <> [])
    (Step_out_spec : m_out m <> [])
    (Hwt_in : forall n, wt_vals (ins n) (m_in m))
    (Hwt_out : forall n, wt_vals (outs n) (m_out m)),
    find_node f G = Some node ->
    m_in m = idty (n_in node) ->
    m_out m = idty (n_out node) ->
    bisim_io G f ins outs
             (traceinf_of_traceinf'
                (transl_trace m Step_in_spec Step_out_spec ins outs Hwt_in Hwt_out 0)).
Proof.
  intros ??????????? Hstep_in Hstep_out.
  unfold bisim_io.
  generalize 0%nat.
  cofix COINDHYP; intro.
  unfold transl_trace, Traces.trace_step.
  rewrite Traces.unfold_mk_trace.
  rewrite E0_left, E0_left_inf.
  rewrite Eappinf_assoc.
  econstructor; eauto;
    rewrite Hstep_in || rewrite Hstep_out;
    apply mk_event_spec;
    rewrite <-Hstep_in || rewrite <-Hstep_out; auto.
Qed.

Definition pstr (xss: stream (list val)) : stream (list value) :=
  fun n => map present (xss n).

Lemma value_to_option_pstr:
  forall xs,
    (fun n => map SB2ObcCorr.value_to_option (pstr xs n)) ≈ (fun n => map Some (xs n)).
Proof.
  intros; unfold SB2ObcCorr.value_to_option, pstr; intro.
  rewrite map_map; auto.
Qed.

Lemma behavior_clight:
  forall G P main ins outs,
    wc_global G ->
    wt_global G ->
    wt_ins G main ins ->
    wt_outs G main outs ->
    normal_args G ->
    sem_node G main (pstr ins) (pstr outs) ->
    nl_to_cl main G = OK P ->
    exists T, program_behaves (semantics2 P) (Reacts T)
         /\ bisim_io G main ins outs T.
Proof.
  intros * Hwc Hwt Hwti Hwto Hnorm Hsem COMP.
  unfold nl_to_cl in COMP.
  simpl in COMP; repeat rewrite print_identity in COMP.
  destruct (schedule_program (NL2SB.translate G)) eqn: Sch;
    simpl in COMP; try discriminate.
  unfold schedule_program, is_well_sch in Sch; simpl in Sch.
  destruct (fold_left is_well_sch_block (Scheduler.schedule (NL2SB.translate G))
                      (OK tt)) eqn: Wsch; simpl in *; try discriminate; destruct u.
  inv Sch.
  apply is_well_sch_program in Wsch.
  repeat rewrite print_identity in COMP.
  pose proof COMP as COMP'.
  assert (exists n, find_node main G = Some n) as (main_node & Find)
      by (inv Hsem; eauto).
  pose proof Find as Find_node.
  apply NL2SB.find_node_translate in Find as (bl & P' & Find& ?); subst.
  apply Scheduler.scheduler_find_block in Find.
  apply SB2Obc.find_block_translate in Find as (c_main &?& Find &?&?); subst.
  assert (Ordered_nodes G) by (eapply wt_global_Ordered_nodes; eauto).
  assert (forall n, 0 < length (ins n)) as Length.
  { inversion_clear Hsem as [???????? Ins].
    intro k; specialize (Ins k); apply Forall2_length in Ins.
    unfold pstr in Ins; rewrite 2 map_length in Ins.
    rewrite <-Ins.
    apply n_ingt0.
  }
  apply sem_msem_node in Hsem as (M & M' & Hsem); auto.
  assert (SB.Wdef.Well_defined (Scheduler.schedule (NL2SB.translate G))).
  { split; [|split]; auto.
    - apply Scheduler.scheduler_ordered, NL2SBCorr.Ordered_nodes_blocks; auto.
    - apply Scheduler.scheduler_normal_args, NL2SBNormalArgs.translate_normal_args; auto.
  }
  apply NL2SBCorr.correctness_loop, Scheduler.scheduler_loop in Hsem; auto.
  assert (forall n, Forall2 SB2ObcCorr.eq_if_present (pstr ins n) (map Some (ins n)))
    by (unfold pstr; intros; clear; induction (ins n); constructor; simpl; auto).
  assert (forall n, Exists (fun v => v <> absent) (pstr ins n))
         by (unfold pstr; intros; specialize (Length n);
             destruct (ins n); simpl in *; try omega;
             constructor; discriminate).
  apply SB2ObcCorr.correctness_loop_call with (ins := fun n => map Some (ins n))
    in Hsem as (me0 & Rst & Hsem &?); auto.
  setoid_rewrite value_to_option_pstr in Hsem.
  set (tr_G := NL2SB.translate G) in *;
    set (sch_tr_G := Scheduler.schedule tr_G) in *;
    set (tr_sch_tr_G := SB2Obc.translate sch_tr_G) in *;
    set (tr_main_node := NL2SB.translate_node main_node) in *;
    set (sch_tr_main_node := Scheduler.schedule_block tr_main_node) in *.
  pose proof (SB2Obc.exists_reset_method sch_tr_main_node) as Find_reset.
  pose proof (SB2Obc.exists_step_method sch_tr_main_node) as Find_step.
  set (m_step := SB2Obc.step_method sch_tr_main_node) in *;
    set (m_reset := SB2Obc.reset_method sch_tr_main_node) in *.
  assert (wt_program tr_sch_tr_G)
    by (apply SB2ObcTyping.translate_wt, Scheduler.scheduler_wt_program,
        NL2SBTyping.translate_wt; auto).
  assert (wt_mem me0 (SB2Obc.translate (Scheduler.schedule P'))
                 (SB2Obc.translate_block sch_tr_main_node))
    by (eapply pres_sem_stmt_call with (f := reset) in Find as (? & ?);
        eauto; simpl; constructor).
  assert (m_in m_step <> nil) as Step_in_spec.
  { apply SB2Obc.find_method_stepm_in in Find_step.
    rewrite Find_step; simpl.
    pose proof (n_ingt0 main_node) as Hin.
    intro E; rewrite <-length_idty, E in Hin; simpl in Hin; omega.
  }
  assert (m_out m_step <> nil) as Step_out_spec.
  { apply SB2Obc.find_method_stepm_out in Find_step.
    rewrite Find_step; simpl.
    pose proof (n_outgt0 main_node) as Hout.
    intro E; rewrite <-length_idty, E in Hout; simpl in Hout; omega.
  }
  assert (forall n, wt_vals (ins n) (m_in m_step)) as Hwt_in
      by (erewrite SB2Obc.find_method_stepm_in; eauto; simpl; eauto).
  assert (forall n, wt_vals (outs n) (m_out m_step)) as Hwt_out
      by (erewrite SB2Obc.find_method_stepm_out; eauto; simpl; eauto).
  pose proof (find_method_name _ _ _ Find_step) as Eq';
    pose proof (find_method_name _ _ _ Find_reset) as Eq'';
    rewrite <-Eq'' in Rst.
  unfold Generation.translate in COMP.
  unfold total_if in *.
  destruct (do_fusion tt).
  - pose proof Find as Find';
      pose proof Find_step as Find_step';
      pose proof Find_reset as Find_reset'.
    apply Obc.Fus.fuse_find_class in Find;
      apply Obc.Fus.fuse_find_method' in Find_step;
      apply Obc.Fus.fuse_find_method' in Find_reset.
    apply find_class_add_defaults_class in Find.
    apply find_method_add_defaults_method in Find_step;
      apply find_method_add_defaults_method in Find_reset;
      rewrite find_method_map_add_defaults_method in Find_step, Find_reset.
    rewrite Find, Find_step, Find_reset in *.
    pose proof (find_class_name _ _ _ _ Find) as Eq;
      rewrite <-Eq in Rst, Hsem.
    rewrite <-Obc.Fus.fuse_method_in in Step_in_spec, Hwt_in;
      rewrite <-Obc.Fus.fuse_method_out in Step_out_spec, Hwt_out.
    assert (Forall_methods (fun m => Obc.Inv.No_Overwrites (m_body m)) (map Obc.Fus.fuse_class tr_sch_tr_G))
           by (apply Obc.Fus.fuse_No_Overwrites, translate_No_Overwrites; auto).
    assert (Forall_methods
              (fun m => Forall (fun x => ~ Obc.Inv.Can_write_in x (m_body m)) (map fst (m_in m)))
              (map Obc.Fus.fuse_class tr_sch_tr_G))
      by (apply Obc.Fus.fuse_cannot_write_inputs, translate_cannot_write_inputs).
    econstructor; split; eauto.
    + assert (Forall Obc.Fus.ClassFusible tr_sch_tr_G)
        by (apply ClassFusible_translate; auto;
            apply Scheduler.scheduler_wc_program; eauto;
            apply NL2SBClocking.translate_wc; auto).
      eapply reacts'
        with (1:=COMP') (8:=Find) (9:=Find_reset) (10:=Find_step) (me0:=me0)
             (Step_in_spec:=Step_in_spec) (Step_out_spec:=Step_out_spec)
             (Hwt_in:=Hwt_in) (Hwt_out:=Hwt_out); eauto.
      * intros ??????? Call; eapply stmt_call_eval_add_defaults_class_not_None with (3 := Call); eauto.
      * change [] with (map Some (@nil val)); eauto.
    + eapply find_node_trace_spec; eauto.
  - apply find_class_add_defaults_class in Find.
    apply find_method_add_defaults_method in Find_step;
      apply find_method_add_defaults_method in Find_reset;
      rewrite find_method_map_add_defaults_method in Find_step, Find_reset.
    rewrite Find, Find_step, Find_reset in *.
    pose proof (find_class_name _ _ _ _ Find) as Eq;
      rewrite <-Eq in Rst, Hsem.
    assert (Forall_methods (fun m => Obc.Inv.No_Overwrites (m_body m)) tr_sch_tr_G)
      by (apply translate_No_Overwrites; auto).
    assert (Forall_methods
              (fun m => Forall (fun x => ~ Obc.Inv.Can_write_in x (m_body m)) (map fst (m_in m)))
              tr_sch_tr_G)
           by (apply translate_cannot_write_inputs).
    econstructor; split.
    + eapply reacts'
        with (1:=COMP') (8:=Find) (10:=Find_step) (me0:=me0)
             (Step_in_spec:=Step_in_spec) (Step_out_spec:=Step_out_spec)
             (Hwt_in:=Hwt_in) (Hwt_out:=Hwt_out);
        eauto.
      * intros ??????? Call; eapply stmt_call_eval_add_defaults_class_not_None with (3 := Call); eauto.
      * change [] with (map Some (@nil val)); eauto.
    + eapply find_node_trace_spec; eauto.
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

(* Theorem behavior_asm: *)
(*   forall D G Gp P main ins outs, *)
(*     elab_declarations D = OK (exist _ G Gp) -> *)
(*     wt_ins G main ins -> *)
(*     wt_outs G main outs -> *)
(*     sem_node G main (pstr ins) (pstr outs) -> *)
(*     compile D main = OK P -> *)
(*     exists T, program_behaves (Asm.semantics P) (Reacts T) *)
(*          /\ bisim_io G main ins outs T. *)
(* Proof. *)
(*   intros D G (WT & WC) P main ins outs Elab ** Comp. *)
(*   simpl in *. unfold compile, print in Comp. *)
(*   rewrite Elab in Comp; simpl in Comp. *)
(*   destruct (nl_to_cl main G) as [p|] eqn: Comp'; simpl in Comp; try discriminate. *)
(*   assert (normal_args G) by admit. *)
(*   edestruct behavior_clight as (T & Beh & Bisim); eauto. *)
(*   eapply reacts_trace_preservation in Comp; eauto. *)
(*   apply add_builtins_spec; auto. *)
(*   intros ? ?; discriminate. *)
(* Qed. *)