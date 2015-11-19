
Require Import Rustre.Common.
Require Import Rustre.Dataflow.Syntax.
Require Import Rustre.Dataflow.IsFree.
Require Import Rustre.Dataflow.IsFree.Decide.

(* ** Definitions on imperative statements *)

(* Require Import PArith. *)
(* Require Import Rustre.DataflowNatSemantics. *)
(* Require Import Rustre.SynchronousNat. *)

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

(**
   The list of equations should be in reverse order: the first
   equation to execute should be the last in the list.

   The set 'mems' should include any input variables. The relevant
   clause is written:
          (PS.In i mems -> ~Is_defined_in i eqs)

   rather than:
          (PS.In i mems -> ~Is_memory_in i eqs)

   To require that such input variables are not redefined in eqs.
*)
Inductive Is_well_sch (mems: PS.t) : list equation -> Prop :=
| WSchNil: Is_well_sch mems nil
| WSchEqDef:
    forall x e eqs,
      Is_well_sch mems eqs ->
      (forall i, Is_free_in_caexp i e ->
                    (PS.In i mems -> ~Is_defined_in i eqs)
                 /\ (~PS.In i mems -> Is_variable_in i eqs)) ->
      (~Is_defined_in x eqs) ->
      Is_well_sch mems (EqDef x e :: eqs)
| WSchEqApp:
    forall x f e eqs,
      Is_well_sch mems eqs ->
      (forall i, Is_free_in_laexp i e ->
                    (PS.In i mems -> ~Is_defined_in i eqs)
                    /\ (~PS.In i mems -> Is_variable_in i eqs)) ->
      (~Is_defined_in x eqs) ->
      Is_well_sch mems (EqApp x f e :: eqs)
| WSchEqFby:
    forall x v e eqs,
      Is_well_sch mems eqs ->
      PS.In x mems ->
      (forall i, Is_free_in_laexp i e ->
                    (PS.In i mems -> ~Is_defined_in i eqs)
                 /\ (~PS.In i mems -> Is_variable_in i eqs)) ->
      (~Is_defined_in x eqs) ->
      Is_well_sch mems (EqFby x v e :: eqs).

Lemma Is_well_sch_NoDup_defs:
  forall mems eqs,
    Is_well_sch mems eqs
    -> NoDup_defs eqs.
Proof.
  induction eqs as [|eq eqs IH]; [now constructor|].
  inversion_clear 1; constructor; try apply IH; assumption.
Qed.

Section Well_sch.

  Variable mems : PS.t.

  (* TODO: rewrite using a strong specification?  *)

  Open Scope bool_scope.

  Definition check_var (defined: PS.t) (variables: PS.t) (x: ident) : bool :=
    if PS.mem x mems
    then negb (PS.mem x defined)
    else PS.mem x variables.

  Lemma check_var_spec:
    forall defined variables x,
      check_var defined variables x = true
      <->
      (PS.In x mems -> ~PS.In x defined)
      /\ (~PS.In x mems -> PS.In x variables).
  Proof.
    (* TODO: how to automate all of this? *)
    intros defined variables x.
    unfold check_var.
    split.
    - intro Hif.
      split; intro Hin.
      + apply PS.mem_spec in Hin.
        rewrite Hin, Bool.negb_true_iff in Hif.
        apply mem_spec_false in Hif. exact Hif.
      + apply mem_spec_false in Hin.
        rewrite Hin, PS.mem_spec in Hif. exact Hif.
    - destruct 1 as [Hin Hnin].
      destruct In_dec with x mems as [H|H].
      + assert (PS.mem x mems = true) as H' by auto.
        rewrite H', Bool.negb_true_iff, mem_spec_false.
        now apply Hin with (1:=H).
      + assert (PS.mem x mems = false) as H' by now apply mem_spec_false.
        rewrite H', PS.mem_spec.
        now apply Hnin with (1:=H).
  Qed.

  Definition check_eq (eq: equation) (acc: bool*PS.t*PS.t)
                  : bool*PS.t*PS.t :=
    match acc with
      | (true, defined, variables) =>
        match eq with
          | EqDef x e =>
            ((PS.for_all (check_var defined variables)
                         (free_in_caexp e PS.empty))
               && (negb (PS.mem x defined)),
             PS.add x defined, PS.add x variables)
          | EqApp x f e =>
            ((PS.for_all (check_var defined variables)
                         (free_in_laexp e PS.empty))
               && (negb (PS.mem x defined)),
             PS.add x defined, PS.add x variables)
          | EqFby x v e =>
            ((PS.mem x mems && PS.for_all (check_var defined variables)
                     (free_in_laexp e PS.empty))
               && (negb (PS.mem x defined)),
             PS.add x defined, variables)
        end
      | (false, _, _) => (false, PS.empty, PS.empty)
    end.

  Definition well_sch (eqs: list equation) : bool :=
    fst (fst (List.fold_right check_eq (true, PS.empty, PS.empty) eqs)).

  Lemma not_for_all_spec:
    forall (s : PS.t) (f : BinNums.positive -> bool),
      SetoidList.compat_bool PS.E.eq f ->
      (PS.for_all f s = false <-> ~(PS.For_all (fun x : PS.elt => f x = true) s)).
  Proof.
    intros s f HSL.
    split.
    - intros Hfa HFa.
      apply (PS.for_all_spec _ HSL) in HFa.
      rewrite Hfa in HFa.
      discriminate.
    - intro HFa.
      apply Bool.not_true_iff_false.
      intro Hfa; apply HFa.
      apply (PS.for_all_spec _ HSL).
      assumption.
  Qed.

  Lemma check_var_compat:
    forall defined variables,
      SetoidList.compat_bool PS.E.eq (check_var defined variables).
  Proof.
    intros defined variables x y Heq.
    unfold PS.E.eq in Heq.
    rewrite Heq.
    reflexivity.
  Qed.

  Lemma well_sch_pre_spec:
    forall eqs good defined variables,
      (good, defined, variables)
          = List.fold_right check_eq (true, PS.empty, PS.empty) eqs
      ->
      (good = true
       -> (Is_well_sch mems eqs
           /\ (forall x, PS.In x defined <-> Is_defined_in x eqs)
           /\ (forall x, PS.In x variables <-> Is_variable_in x eqs)))
      /\ (good = false -> ~Is_well_sch mems eqs).
  Proof.
    Hint Constructors Is_well_sch.
    induction eqs as [|eq].
    - simpl; injection 1; intros HRv HRm; subst.
      intuition;
        repeat match goal with
                 | H: PS.In _ PS.empty |- _ => apply PS.empty_spec in H;
                                               contradiction
                 | H: Is_defined_in _ nil |- _ => now inversion H
                 | H: Is_variable_in _ nil |- _ => now inversion H
                 | H1:good=true, H2:good=false |- _ =>
                      rewrite H1 in H2; discriminate
               end.
    - intros good defined variables HH.
      simpl in HH.
      destruct (List.fold_right check_eq (true, PS.empty, PS.empty) eqs)
        as [[good' defined'] variables'].
      specialize IHeqs with good' defined' variables'.
      pose proof (IHeqs (eq_refl (good', defined', variables'))) as IH;
        clear IHeqs.
      destruct IH as [IHt IHf].
      split; intro Hg; rewrite Hg in *; clear Hg.
      + destruct eq; (* the horror... *)
        (simpl in HH;
         assert (good' = true) as IH
             by (apply Bool.not_false_iff_true;
                 intro Hgf; rewrite Hgf in HH;
                 discriminate);
         rewrite IH in HH;
         apply IHt in IH; clear IHt IHf;
         destruct IH as [Hwsch [Hidi Hivi]];
         symmetry in HH;
         injection HH;
         intros HRv HRd; rewrite <-HRv,<-HRd in *; clear HRv HRd HH;
         intro Hcv; apply Bool.andb_true_iff in Hcv;
           destruct Hcv as [Hcv Hnin];
           try (apply Bool.andb_true_iff in Hcv;
                 destruct Hcv as [Him Hcv]);
           rewrite Bool.negb_true_iff,
           <-PSF.not_mem_iff in Hnin;
         rewrite PS.for_all_spec in Hcv;
           [ |now apply check_var_compat];
         try rewrite PS.mem_spec in Him;
         split;
         [constructor;
           try (exact Hwsch
                || assumption
                || (intro HH; apply Hidi in HH; contradiction));
          intros y Hy;
            apply free_in_caexp_spec' in Hy
            || apply free_in_laexp_spec' in Hy;
            apply Hcv in Hy;
            apply check_var_spec in Hy;
            repeat progress match goal with
            | H:_ /\ _ |- _ => destruct H
            | |- _ /\ _ => split; intros
            | H1:PS.In ?y ?mems -> _, H2:PS.In ?y ?mems |- _ => apply H1 in H2
            | |- ~Is_defined_in ?x _ => intro
            | H1:~PS.In ?x defined',
              H2:Is_defined_in ?x eqs |- _ => apply Hidi in H2; contradiction
            | |- Is_variable_in ?x eqs => apply Hivi
            | _ => now intuition
                            end |];
        split; intro x; split; intro HH;
           (apply PS.add_spec in HH;
             destruct HH as [HH|HH];
             [rewrite HH; now repeat constructor
             |apply Hidi in HH || apply Hivi in HH; constructor 2; exact HH])
           || (apply Is_defined_in_cons in HH || apply Is_variable_in_cons in HH;
                apply PS.add_spec;
                destruct HH as [HH|HH]; inversion_clear HH;
                [left; reflexivity|right; apply Hidi || apply Hivi; assumption])
           || (apply Hivi in HH; constructor 2; apply HH)
           || (apply Is_variable_in_cons in HH;
               destruct HH as [HH|HH];
               [now inversion HH
               |destruct HH as [HH0 HH1]; now apply Hivi with (1:=HH1)])).
      + destruct good'; [clear IHf| inversion 1; apply IHf; auto ].
        pose proof (IHt (eq_refl true)) as IH; clear IHt.
        destruct IH as [Hwsch [Hidi Hivi]].
        destruct eq;
          (simpl in HH;
            injection HH;
            intros HRd HRv Hcv;
            rewrite HRd,HRv in *;
            clear HRd HRv HH;
            symmetry in Hcv;
            repeat progress match goal with
            | Hcv:PS.mem _ _ && _ = false |- _ =>
              apply Bool.andb_false_iff in Hcv;
                destruct Hcv as [Hcv|Hcv];
                [ inversion 1;
                  apply mem_spec_false in Hcv;
                  contradiction
                | rewrite not_for_all_spec in Hcv;
                  [ |now apply check_var_compat] ]
            | H:_ && negb _ = false |- _ =>
              apply Bool.andb_false_iff in Hcv;
                destruct Hcv as [Hcv|Hcv];
                [rewrite not_for_all_spec in Hcv;
                  [ |now apply check_var_compat]
                | rewrite Bool.negb_false_iff in Hcv;
                  rewrite PS.mem_spec in Hcv;
                  apply Hidi in Hcv;
                  inversion 1;
                  contradiction ]
            | Hcv:PS.mem _ _ && _ && _ = false |- _ =>
              apply Bool.andb_false_iff in Hcv;
                destruct Hcv as [Hcv|Hcv];
                [|rewrite Bool.negb_false_iff in Hcv;
                   rewrite PS.mem_spec in Hcv;
                   apply Hidi in Hcv;
                   inversion 1;
                   contradiction]
            | H:PS.for_all _ _ = false |- _ =>
              apply not_for_all_spec in Hcv; [|apply check_var_compat]
            | _ => idtac
            end;
            intro Hwsch';
            apply Hcv;
            inversion_clear Hwsch' as [|? ? ? Hwsch0 HH
                                          |? ? ? ? Hwsch0 HH
                                          |? ? ? ? Hwsch0 Hi HH];
            intros x Hx;
            apply free_in_caexp_spec in Hx || apply free_in_laexp_spec in Hx;
            destruct Hx as [Hx|Hx]; [ | apply not_In_empty in Hx; contradiction ];
            intros;
            repeat progress
                   match goal with
                   | |- _ /\ _ => split; intros
                   | H: _ /\ _ |- _ => destruct H
                   | H: Is_free_in_caexp _ _ |- _ => apply HH in H
                   | H: Is_free_in_laexp _ _ |- _ => apply HH in H
                   | |- check_var defined' variables' x = true
                     => apply check_var_spec
                   | H1:~PS.In ?x ?mems -> Is_variable_in ?x ?eqs,
                     H2:~PS.In ?x ?mems |- PS.In ?x variables'
                     => apply H1 in H2; apply Hivi in H2; assumption
                   | H1:PS.In ?x ?mems -> ~Is_defined_in ?x ?eqs,
                        H2:PS.In ?x ?mems |- _ => apply H1 in H2
                   | H:~Is_defined_in ?x ?eqs |- ~PS.In ?x defined'
                     => intro HN; apply Hidi in HN; contradiction
                   end).
  Qed.

  Lemma well_sch_spec:
    forall eqns,
      if well_sch eqns
      then Is_well_sch mems eqns
      else ~Is_well_sch mems eqns.
  Proof.
    intro eqns.
    pose proof (well_sch_pre_spec eqns).
    unfold well_sch.
    destruct (List.fold_right check_eq (true, PS.empty, PS.empty) eqns)
      as [[good defined] variables].
    simpl.
    specialize H with good defined variables.
    pose proof (H (eq_refl _)) as H'; clear H.
    destruct H' as [Ht Hf].
    destruct good;
    intuition.
  Qed.

End Well_sch.

Lemma Is_well_sch_cons:
  forall m eq eqs, Is_well_sch m (eq :: eqs) -> Is_well_sch m eqs.
Proof. inversion 1; auto. Qed.

Lemma Is_well_sch_free_variable:
  forall x eq eqs mems,
    Is_well_sch mems (eq :: eqs)
    -> Is_free_in_equation x eq
    -> ~ PS.In x mems
    -> Is_variable_in x eqs.
Proof.
  intros x eq eqs mems Hwsch Hfree Hnim.
  destruct eq;
    inversion_clear Hwsch as [|? ? ? ? Hp|? ? ? ? ? Hp|? ? ? ? ? ? Hp];
    inversion_clear Hfree as [? ? ? Hc|? ? ? ? Hc|? ? ? ? Hc];
    apply Hp in Hc;
    intuition.
Qed.

Lemma Is_well_sch_free_variable_in_mems:
  forall y eq eqs mems,
    Is_well_sch mems (eq :: eqs)
    -> Is_free_in_equation y eq
    -> PS.In y mems
    -> ~Is_defined_in y eqs.
Proof.
  intros x eq eqs mems Hwsch Hfree Hnim.
  destruct eq;
    inversion_clear Hwsch as [|? ? ? ? Hp|? ? ? ? ? Hp|? ? ? ? ? ? Hp];
    inversion_clear Hfree as [? ? ? Hc|? ? ? ? Hc|? ? ? ? Hc];
    apply Hp in Hc;
    destruct Hc as [Hc0 Hc1];
    apply Hc0 in Hnim;
    apply Hnim.
Qed.

Lemma Is_wsch_is_defined_in:
  forall x eq eqs mems,
    Is_well_sch mems (eq :: eqs) ->
    Is_defined_in x (eq :: eqs) ->
    Is_defined_in_eq x eq
    \/ (~Is_defined_in_eq x eq /\ Is_defined_in x eqs).
Proof.
  intros x eq eqs mems Hwsch Hdef.
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
      Is_well_sch (PS.add ni (memories eqs)) eqs
      -> ~Is_defined_in ni eqs
      -> Is_variable_in no eqs
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
    -> ~Is_defined_in fnode.(n_input) fnode.(n_eqs).
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

Lemma Welldef_global_output_Is_variable_in:
  forall f G fnode,
    Welldef_global G
    -> find_node f G = Some fnode
    -> Is_variable_in fnode.(n_output) fnode.(n_eqs).
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

