Require Import PArith.
Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Require Import Rustre.Common.
Require Import Rustre.Dataflow.Syntax.
Require Import Rustre.Dataflow.IsVariable.
Require Import Rustre.Dataflow.IsDefined.

(**

  The [NoDup_def] predicate states that variables are only defined
  once. This is asking for some sort of SSA.

*)

(* TODO: the dispatch on all constructors seems rather unnecessary,
this generically amounts to:

<<
  forall x, Is_defined_in_eq x eq -> ~Is_defined_in x eqs
>>
*)


Inductive NoDup_defs : list equation -> Prop :=
| NDDNil: NoDup_defs nil
| NDDEqDef:
    forall x e eqs,
      NoDup_defs eqs ->
      ~Is_defined_in x eqs ->
      NoDup_defs (EqDef x e :: eqs)
| NDDEqApp:
    forall x f e eqs,
      NoDup_defs eqs ->
      ~Is_defined_in x eqs ->
      NoDup_defs (EqApp x f e :: eqs)
| NDDEqFby:
    forall x v e eqs,
      NoDup_defs eqs ->
      ~Is_defined_in x eqs ->
      NoDup_defs (EqFby x v e :: eqs).




Lemma NoDup_defs_cons:
  forall eq eqs,
    NoDup_defs (eq :: eqs) -> NoDup_defs eqs.
Proof.
  intros eq eqs Hndd.
  destruct eq; inversion_clear Hndd; assumption.
Qed.

Lemma not_Is_variable_in_memories:
  forall x eqs,
    PS.In x (memories eqs)
    -> NoDup_defs eqs
    -> ~Is_variable_in x eqs.
Proof.
  (* TODO: Too complicated! Find a simpler proof. *)
  intros x eqs Hinm Hndd.
  pose proof (Is_defined_in_memories _ _ Hinm) as Hdin.
  unfold memories, Is_variable_in in *.
  induction eqs as [eq|eq eqs IH].
  - simpl in *; intro; not_In_empty.
  - apply Is_defined_in_cons in Hdin.
    inversion Hndd
      as [|y e ? Hndds Hndi|y f e ? Hndds Hndi|y v0 e ? Hndds Hndi];
      subst; clear Hndd.
    + destruct Hdin as [Hdin|[Hndin Hdins]].
      simpl in Hinm.
      intro He; apply List.Exists_cons in He; destruct He as [He|He].
      apply Is_defined_in_memories in Hinm.
      inversion He; subst; clear He.
      contradiction.

      inversion Hdin; subst; clear Hdin.
      apply Is_variable_in_Is_defined_in in He.
      contradiction.

      simpl in Hinm.
      apply IH with (2:=Hndds) (3:=Hdins) in Hinm.
      intro He; apply List.Exists_cons in He; destruct He as [He|He].
      inversion He; subst; clear He.
      apply Hndin; now constructor.
      contradiction.
    + destruct Hdin as [Hdin|[Hndin Hdins]].
      simpl in Hinm.
      intro He; apply List.Exists_cons in He; destruct He as [He|He].
      apply Is_defined_in_memories in Hinm.
      inversion He; subst; clear He.
      contradiction.

      inversion Hdin; subst; clear Hdin.
      apply Is_variable_in_Is_defined_in in He.
      contradiction.

      simpl in Hinm.
      apply IH with (2:=Hndds) (3:=Hdins) in Hinm.
      intro He; apply List.Exists_cons in He; destruct He as [He|He].
      inversion He; subst; clear He.
      apply Hndin; now constructor.
      contradiction.
    + destruct Hdin as [Hdin|[Hndin Hdins]].
      simpl in Hinm.
      intro He; apply List.Exists_cons in He; destruct He as [He|He].
      inversion He; subst; clear He.
      inversion Hdin; subst; clear Hdin.

      apply Is_variable_in_Is_defined_in in He.
      contradiction.

      simpl in Hinm.
      apply In_fold_left_memory_eq in Hinm.
      destruct Hinm as [Hinm|Hinm].
      apply IH with (2:=Hndds) (3:=Hdins) in Hinm.
      intro He; apply List.Exists_cons in He; destruct He as [He|He].

      inversion He; subst; clear He.
      contradiction.

      apply PS.add_spec in Hinm.
      destruct Hinm as [Hinm|Hinm]; [|now not_In_empty].
      rewrite Hinm in *.
      exfalso; apply Hndin; now constructor.
Qed.
