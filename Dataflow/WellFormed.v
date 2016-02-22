Require Import Rustre.Common.
Require Import Rustre.Dataflow.Syntax.
Require Import Rustre.Dataflow.IsFree.
Require Import Rustre.Dataflow.IsVariable.
Require Import Rustre.Dataflow.IsDefined.
Require Import Rustre.Dataflow.Memories.
Require Import Rustre.Dataflow.Ordered.
Require Import Rustre.Dataflow.NoDup.


(* ** Definitions on imperative statements *)

(* Require Import PArith. *)
(* Require Import Rustre.DataflowNatSemantics. *)
(* Require Import Rustre.SynchronousNat. *)

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

(* TODO:
   - Assume we are given a list of dataflow equations eqs satisfying
        sch_eqs (memories eqs) PS.empty (defined eqs) eqs
   - Show that the step function generated by translate_eqs is correct,
     i.e., that its semantics correspond to the 'held semantics' of the
     original dataflow equations.
   - The 'held semantics' use holdR rather than fbyR for defining 'fby'.
   - Basic invariant for a single pass (to show by induction along the list
     of dataflow equations/sequence of conditional assignments):
        forall x,
             (PS.In x (PS.inter memories written) -> M x = H x (S n))
          /\ (PS.In x (PS.diff memories written) -> M x = H x n)
          /\ (PS.In x (PS.diff written memories) ->
              H x n = present c -> p x = c)

   - Afterward, this must be extended to run (i.e., forall n from 0).
   - and we must switch back to the standard fby semantics for instants
     where a clock is active.
 *)

(** ** Predicates *)

Section IsWellSch.

Variable memories : PS.t.
Variable arg: Nelist.nelist ident.

(**
   The list of equations should be in reverse order: the first
   equation to execute should be the last in the list.
*)
(* =Is_well_sch= *)
Inductive Is_well_sch : list equation -> Prop :=
| WSchNil: Is_well_sch nil
| WSchEq: forall x eq eqs,
    Is_well_sch eqs ->
    (forall i, Is_free_in_eq i eq ->
                  (PS.In i memories -> ~Is_defined_in_eqs i eqs)
               /\ (~PS.In i memories -> Is_variable_in_eqs i eqs \/ Nelist.In i arg)) ->
    (~Is_defined_in_eqs x eqs) ->
    Is_well_sch (eq :: eqs).
(* =end= *)

(*
  WSchEqApp:
    forall x ck f e eqs,
      Is_well_sch eqs ->
      (forall i, Is_free_in_laexps i ck e ->
                    (PS.In i memories -> ~Is_defined_in_eqs i eqs)
                    /\ (~PS.In i memories -> Is_variable_in_eqs i eqs
                                      \/ Nelist.In i arg)) ->
      (~Is_defined_in_eqs x eqs) ->
      Is_well_sch (EqApp x ck f e :: eqs)
| WSchEqFby:
    forall x ck v e eqs,
      Is_well_sch eqs ->
(*      PS.In x memories -> (* TODO: delete -> done !*) *)
      (forall i, Is_free_in_laexp i ck e ->
                    (PS.In i memories -> ~Is_defined_in_eqs i eqs)
                 /\ (~PS.In i memories -> Is_variable_in_eqs i eqs
                                   \/ Nelist.In i arg)) ->
      (~Is_defined_in_eqs x eqs) ->
      Is_well_sch (EqFby x ck v e :: eqs).
*)
End IsWellSch.

Hint Constructors Is_well_sch.

Lemma Is_well_sch_NoDup_defs:
  forall mems argIn eqs,
    Is_well_sch mems argIn eqs
    -> NoDup_defs eqs.
Proof.
  induction eqs as [|eq eqs IH]; [now constructor|].
  inversion_clear 1; constructor; try apply IH; assumption.
Qed.

Lemma Is_well_sch_cons:
  forall m argIn eq eqs, Is_well_sch m argIn (eq :: eqs) -> Is_well_sch m argIn eqs.
Proof. inversion 1; auto. Qed.

Lemma Is_well_sch_free_variable:
  forall argIn x eq eqs mems,
    Is_well_sch mems argIn (eq :: eqs)
    -> Is_free_in_eq x eq
    -> ~ PS.In x mems
    -> Is_variable_in_eqs x eqs \/ Nelist.In x argIn.
Proof.
  intros argIn x eq eqs mems Hwsch Hfree Hnim.
  destruct eq;
    inversion Hwsch as [|? ? ? ? ? Hp | ? ? ? ? ? ? Hp | ? ? ? ? ? ? (*?*) Hp];
    inversion_clear Hfree as [? ? ? ? Hc | ? ? ? ? ? Hc | ? ? ? ? ? Hc]; subst; intuition;
    eapply Hp in Hc;
    intuition.
Qed.

Lemma Is_well_sch_free_variable_in_mems:
  forall argIn y eq eqs mems,
    Is_well_sch mems argIn (eq :: eqs)
    -> Is_free_in_eq y eq
    -> PS.In y mems
    -> ~Is_defined_in_eqs y eqs.
Proof.
  intros argIn x eq eqs mems Hwsch Hfree Hnim.
  destruct eq;
    inversion_clear Hwsch as [|? ? ? ? ? Hp | ? ? ? ? ? ? Hp | ? ? ? ? ? ? Hp];
    inversion_clear Hfree as [? ? ? ? Hc | ? ? ? ? ? Hc | ? ? ? ? ? Hc];
    eapply Hp in Hc;
    destruct Hc as [Hc0 Hc1];
    apply Hc0 in Hnim;
    apply Hnim.
Qed.

Lemma Is_wsch_is_defined_in:
  forall x eq eqs mems argIn,
    Is_well_sch mems argIn (eq :: eqs) ->
    Is_defined_in_eqs x (eq :: eqs) ->
    Is_defined_in_eq x eq
    \/ (~Is_defined_in_eq x eq /\ Is_defined_in_eqs x eqs).
Proof.
  intros x eq eqs mems argIn Hwsch Hdef.
  apply List.Exists_cons in Hdef.
  destruct (Is_defined_in_eq_dec x eq); intuition.
Qed.

Inductive Welldef_global : list node -> Prop :=
| WGnil:
    Welldef_global []
| WGcons:
    forall nd nds,
      Welldef_global nds ->
      let eqs := nd.(n_eqs) in
      let ni := nd.(n_input) in
      let no := nd.(n_output) in
        NoDup (Nelist.nelist2list ni)
      -> Is_well_sch (memories eqs) ni eqs
      -> ~ List.Exists (fun ni => Is_defined_in_eqs ni eqs) (Nelist.nelist2list ni)
      -> Is_variable_in_eqs no eqs
      -> ~Is_node_in nd.(n_name) eqs
      -> (forall f, Is_node_in f eqs -> find_node f nds <> None)
      -> List.Forall (fun nd'=> nd.(n_name) <> nd'.(n_name)) nds
      -> Welldef_global (nd::nds).

Lemma Welldef_global_cons:
  forall node G,
    Welldef_global (node::G) -> Welldef_global G.
Proof.
  inversion 1; assumption.
Qed.

(* TODO: Write a function 'welldef_global' to decide this. *)

Lemma Welldef_global_Ordered_nodes:
  forall G, Welldef_global G -> Ordered_nodes G.
Proof.
  induction G as [|node G IH]; [constructor|].
  intro Hwdef.
  constructor.
  - apply IH; apply Welldef_global_cons with (1:=Hwdef).
  - intros f Hini.
    inversion Hwdef.
    split; [ intro; subst | ];
    repeat match goal with
           | eqs:=n_eqs node |- _ => unfold eqs in *; clear eqs
           | H1:~Is_node_in _ _, H2:Is_node_in _ _ |- False => contradiction
           | H1: Is_node_in _ _,
             H2: context[Is_node_in _ _ -> find_node _ _ <> None] |- _ =>
             apply H2 in H1; apply find_node_Exists in H1; exact H1
           end.
  - inversion Hwdef; assumption.
Qed.

Lemma Welldef_global_app:
  forall G G', Welldef_global (G ++ G') -> Welldef_global G'.
Proof.
  intros G G' Hwdef.
  induction G as [|g G IH]; [now apply Hwdef|].
  rewrite <- List.app_comm_cons in Hwdef.
  apply Welldef_global_cons in Hwdef.
  apply IH.
  apply Hwdef.
Qed.

Lemma Welldef_global_input_not_Is_defined_in:
  forall f G fnode,
    Welldef_global G
    -> find_node f G = Some fnode
    -> ~ Nelist.Exists (fun ni => Is_defined_in_eqs ni fnode.(n_eqs)) fnode.(n_input).
Proof.
  induction G as [|node G IH]; [inversion_clear 2|].
  intros fnode HWdef Hfnode.
  apply find_node_split in Hfnode.
  destruct Hfnode as [bG [aG HnG]].
  rewrite HnG in HWdef; clear HnG.
  apply Welldef_global_app in HWdef.
  inversion_clear HWdef.
  now rewrite <- Nelist.nelist2list_Exists.
Qed.

Lemma Welldef_global_output_Is_variable_in:
  forall f G fnode,
    Welldef_global G
    -> find_node f G = Some fnode
    -> Is_variable_in_eqs fnode.(n_output) fnode.(n_eqs).
Proof.
  induction G as [|node G IH]; [inversion_clear 2|].
  intros fnode HWdef Hfnode.
  apply find_node_split in Hfnode.
  destruct Hfnode as [bG [aG HnG]].
  rewrite HnG in HWdef; clear HnG.
  apply Welldef_global_app in HWdef.
  inversion_clear HWdef.
  assumption.
Qed.

(* TODO: implement a function to decide Welldef_global. *)

