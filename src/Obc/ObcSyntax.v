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
From Velus Require Import Operators.

Open Scope bool_scope.
From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

(** * Obc syntax *)

(**
  Obc is a minimal object-oriented programming language.
 *)

Module Type OBCSYNTAX
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op).

  (* We do not want the too weak Coq generated induction principles *)
  Unset Elimination Schemes.

  Inductive exp : Type :=
  | Var   : ident -> type -> exp                 (* variable  *)
  | State : ident -> type -> exp                 (* state variable  *)
  | Const : const -> exp                         (* constant *)
  | Op    : operator -> list exp -> type -> exp  (* operators: unary, binary, and more *)
  | Valid : ident -> type -> exp.                (* valid value assertion *)

  (* Back to normal *)
  Set Elimination Schemes.

  (* Let us define our own induction and recursion principles.
     For that, we need an informative version of [List.Forall]. *)

  Inductive Forall_t {A : Type} (P : A -> Type) : list A -> Type :=
      Forall_t_nil : Forall_t P []
    | Forall_t_cons : forall (x : A) (l : list A), P x -> Forall_t P l -> Forall_t P (x :: l).

  Definition exp_rect := fun (P : exp -> Type)
    (f_var   : forall id ty, P (Var id ty))
    (f_state : forall id ty, P (State id ty))
    (f_const : forall c,     P (Const c))
    (f_op    : forall op el, Forall_t P el -> forall ty, P (Op op el ty))
    (f_valid : forall id ty, P (Valid id ty)) =>
  fix F (e : exp) : P e :=
    match e as e return (P e) with
    | Var   id ty => f_var   id ty
    | State id ty => f_state id ty
    | Const c     => f_const c
    | Op op el ty => f_op op el (list_rect (Forall_t P) (Forall_t_nil P)
                                  (fun e el IHel => Forall_t_cons P e el (F e) IHel) el) ty
    | Valid id ty => f_valid id ty
    end.

  Definition exp_ind := fun (P : exp -> Prop)
    (f_var   : forall id ty, P (Var id ty))
    (f_state : forall id ty, P (State id ty))
    (f_const : forall c,     P (Const c))
    (f_op    : forall op el, Forall P el -> forall ty, P (Op op el ty))
    (f_valid : forall id ty, P (Valid id ty)) =>
  fix F (e : exp) : P e :=
    match e as e return (P e) with
    | Var   id ty => f_var   id ty
    | State id ty => f_state id ty
    | Const c     => f_const c
    | Op op el ty => f_op op el (list_ind (List.Forall P) (List.Forall_nil P)
                                  (fun e el IHel => List.Forall_cons e (F e) IHel) el) ty
    | Valid id ty => f_valid id ty
    end.

  Fixpoint typeof (e: exp): type :=
    match e with
    | Const c => type_const c
    | Var _ ty
    | State _ ty
    | Op _ _ ty
    | Valid _ ty => ty
    end.

  Inductive stmt : Type :=
  | Assign : ident -> exp -> stmt                    (* x = e *)
  | AssignSt : ident -> exp -> stmt                  (* self.x = e *)
  | Ifte : exp -> stmt -> stmt -> stmt               (* if e then s1 else s2 *)
  | Comp : stmt -> stmt -> stmt                      (* s1; s2 *)
  | Call : list ident -> ident -> ident -> ident -> list exp -> stmt
  (* y1, ..., yn := class instance method (e1, ..., em) *)
  | Skip.

  Record method : Type :=
    mk_method {
        m_name : ident;
        m_in   : list (ident * type);
        m_vars : list (ident * type);
        m_out  : list (ident * type);
        m_body : stmt;

        m_nodupvars : NoDupMembers (m_in ++ m_vars ++ m_out);
        m_good      : Forall ValidId (m_in ++ m_vars ++ m_out)
      }.

  Definition meth_vars m := m.(m_in) ++ m.(m_vars) ++ m.(m_out).
  Hint Resolve m_nodupvars : core.

  Lemma m_nodupout:
    forall f, NoDupMembers (m_out f).
  Proof.
    intro; pose proof (m_nodupvars f) as Nodup;
    now repeat apply NoDupMembers_app_r in Nodup.
  Qed.

  Lemma m_nodupin:
    forall f, NoDupMembers (m_in f).
  Proof.
    intro; pose proof (m_nodupvars f) as Nodup;
    now apply NoDupMembers_app_l in Nodup.
  Qed.

  Lemma m_nodupvars':
    forall f, NoDupMembers (m_vars f).
  Proof.
    intro; pose proof (m_nodupvars f) as Nodup;
    now apply NoDupMembers_app_r, NoDupMembers_app_l in Nodup.
  Qed.

  Remark In_meth_vars_out:
    forall f x ty,
      InMembers x f.(m_out) ->
      In (x, ty) (meth_vars f) ->
      In (x, ty) f.(m_out).
  Proof.
    intros * E ?.
    pose proof (m_nodupvars f) as Nodup.
    apply InMembers_In in E as (ty' &?).
    assert (In (x, ty') (meth_vars f))
      by (now apply in_or_app; right; apply in_or_app; right).
    now app_NoDupMembers_det.
  Qed.

  Lemma m_notreserved:
    forall x m,
      In x reserved ->
      ~InMembers x (meth_vars m).
  Proof.
    intros * Hin Hinm.
    pose proof m.(m_good) as Good.
    unfold meth_vars in Hinm.
    induction (m.(m_in) ++ m.(m_vars) ++ m.(m_out)) as [|(x', t)];
      inv Hinm; inversion_clear Good as [|? ? Valid'].
    - inv Valid'. contradiction.
    - now apply IHl.
  Qed.

  Lemma m_good_out:
    forall m x,
      In x m.(m_out) ->
      ValidId x.
  Proof.
    intros.
    pose proof (m_good m) as G.
    eapply Forall_forall; eauto.
    apply in_app; right; apply in_app; now right.
  Qed.

  Lemma m_good_in:
    forall m x,
      In x m.(m_in) ->
      ValidId x.
  Proof.
    intros.
    pose proof (m_good m) as G.
    eapply Forall_forall; eauto.
    apply in_app; now left.
  Qed.

  Lemma m_notprefixed:
    forall x m,
      prefixed x ->
      ~InMembers x (meth_vars m).
  Proof.
    intros * Hin Hinm.
    pose proof m.(m_good) as Good.
    unfold meth_vars in Hinm.
    induction (m.(m_in) ++ m.(m_vars) ++ m.(m_out)) as [|(x', t)];
      inv Hinm; inversion_clear Good as [|? ? Valid'].
    - inv Valid'. eapply valid_not_prefixed; eauto.
    - now apply IHl.
  Qed.

  Record class : Type :=
    mk_class {
        c_name    : ident;
        c_mems    : list (ident * type);
        c_objs    : list (ident * ident);   (* (instance, class) *)
        c_methods : list method;

        c_nodup   : NoDup (map fst c_mems ++ map fst c_objs);
        c_nodupm  : NoDup (map m_name c_methods);
        c_good    : Forall (fun xt => valid (fst xt)) c_objs /\ valid c_name
      }.

  Lemma c_nodupmems:
    forall c, NoDupMembers (c_mems c).
  Proof.
    intro.
    pose proof (c_nodup c) as Nodup.
    apply NoDup_app_weaken in Nodup.
    now rewrite fst_NoDupMembers.
  Qed.

  Lemma c_nodupobjs:
    forall c, NoDupMembers (c_objs c).
  Proof.
    intro.
    pose proof (c_nodup c) as Nodup.
    rewrite Permutation.Permutation_app_comm in Nodup.
    apply NoDup_app_weaken in Nodup.
    now rewrite fst_NoDupMembers.
  Qed.

  Definition program : Type := list class.

  Definition find_method (f: ident): list method -> option method :=
    fix find ms := match ms with
                   | [] => None
                   | m :: ms' => if ident_eqb m.(m_name) f
                                then Some m else find ms'
                   end.

  Definition find_class (n: ident) : program -> option (class * list class) :=
    fix find p := match p with
                  | [] => None
                  | c :: p' => if ident_eqb c.(c_name) n
                              then Some (c, p') else find p'
                  end.

  Definition Forall_methods P p :=
    Forall (fun c => Forall P c.(c_methods)) p.

  (** Properties of method lookups *)

  Remark find_method_In:
    forall fid ms f,
      find_method fid ms = Some f ->
      In f ms.
  Proof.
    intros * Hfind.
    induction ms; inversion Hfind as [H].
    destruct (ident_eqb (m_name a) fid) eqn: E.
    - inversion H; subst.
      apply in_eq.
    - auto using in_cons.
  Qed.

  Remark find_method_name:
    forall fid fs f,
      find_method fid fs = Some f ->
      f.(m_name) = fid.
  Proof.
    intros * Hfind.
    induction fs; inversion Hfind as [H].
    destruct (ident_eqb (m_name a) fid) eqn: E.
    - inversion H; subst.
      now apply ident_eqb_eq.
    - now apply IHfs.
  Qed.

  Lemma find_method_map:
    forall f,
      (forall m, (f m).(m_name) = m.(m_name)) ->
      forall n ms,
        find_method n (map f ms) = option_map f (find_method n ms).
  Proof.
    intros f Hfname.
    induction ms as [|m ms IH]; auto. simpl.
    destruct (ident_eqb (f m).(m_name) n) eqn:Heq;
      rewrite Hfname in Heq; rewrite Heq; auto.
  Qed.

  (** Properties of class lookups *)

  Lemma find_class_none:
    forall clsnm cls prog,
      find_class clsnm (cls::prog) = None
      <-> (cls.(c_name) <> clsnm /\ find_class clsnm prog = None).
  Proof.
    intros clsnm cls prog.
    simpl; destruct (ident_eqb (c_name cls) clsnm) eqn: E.
    - split; intro HH; try discriminate.
      destruct HH.
      apply ident_eqb_eq in E; contradiction.
    - apply ident_eqb_neq in E; split; intro HH; tauto.
  Qed.

  Remark find_class_app:
    forall id cls c cls',
      find_class id cls = Some (c, cls') ->
      exists cls'',
        cls = cls'' ++ c :: cls'
        /\ find_class id cls'' = None.
  Proof.
    intros * Hfind.
    induction cls; inversion Hfind as [H].
    destruct (ident_eqb (c_name a) id) eqn: E.
    - inversion H; subst.
      exists nil; auto.
    - specialize (IHcls H).
      destruct IHcls as (cls'' & Hcls'' & Hnone).
      rewrite Hcls''.
      exists (a :: cls''); split; auto.
      simpl; rewrite E; auto.
  Qed.

  Remark find_class_name:
    forall id cls c cls',
      find_class id cls = Some (c, cls') ->
      c.(c_name) = id.
  Proof.
    intros * Hfind.
    induction cls; inversion Hfind as [H].
    destruct (ident_eqb (c_name a) id) eqn: E.
    - inversion H; subst.
      now apply ident_eqb_eq.
    - now apply IHcls.
  Qed.

  Remark find_class_In:
    forall id cls c cls',
      find_class id cls = Some (c, cls') ->
      In c cls.
  Proof.
    intros * Hfind.
    induction cls; inversion Hfind as [H].
    destruct (ident_eqb (c_name a) id) eqn: E.
    - inversion H; subst.
      apply in_eq.
    - apply in_cons; auto.
  Qed.

  Lemma find_class_app':
    forall n xs ys,
      find_class n (xs ++ ys) = match find_class n xs with
                                 | None => find_class n ys
                                 | Some (c, prog) => Some (c, prog ++ ys)
                                 end.
  Proof.
    induction xs as [|c xs IH]; simpl; auto.
    intro ys.
    destruct (ident_eqb c.(c_name) n); auto.
  Qed.

  Lemma not_In_find_class:
    forall n prog,
      ~In n (map c_name prog) ->
      find_class n prog = None.
  Proof.
    induction prog as [|c prog IH]; auto.
    simpl; intro Hnin.
    apply Decidable.not_or in Hnin.
    destruct Hnin as (Hnin1 & Hnin2).
    rewrite (IH Hnin2).
    apply ident_eqb_neq in Hnin1.
    now rewrite Hnin1.
  Qed.

  Lemma find_class_ltsuffix:
    forall n prog c prog',
      find_class n prog = Some (c, prog') ->
      ltsuffix prog' prog.
  Proof.
    induction prog as [|c prog IH]. now inversion 1.
    red; simpl. intros c' prog' Hfind.
    destruct (ident_eqb c.(c_name) n).
    - inv Hfind.
      exists [c']. simpl; split; auto; discriminate.
    - destruct (IH _ _ Hfind) as (xs & Hprog & Hxs). subst.
      exists (c::xs); simpl; split; auto; discriminate.
  Qed.

  Lemma find_class_ltsuffix2:
    forall n prog1 prog2 c1 c2 prog1' prog2',
      find_class n prog1 = Some (c1, prog1') ->
      find_class n prog2 = Some (c2, prog2') ->
      ltsuffix2 (prog1', prog2') (prog1, prog2).
  Proof.
    split; eauto using find_class_ltsuffix.
  Qed.

  Lemma Forall_methods_find:
    forall prog P cid c prog' fid f,
      Forall_methods P prog ->
      find_class cid prog = Some (c, prog') ->
      find_method fid c.(c_methods) = Some f ->
      P f.
  Proof.
    unfold Forall_methods; intros * Spec Findc Findf.
    apply find_class_In in Findc.
    apply find_method_In in Findf.
    do 2 eapply Forall_forall in Spec; eauto.
  Qed.

  (** Syntactic predicates *)

  Inductive Is_free_in_exp : ident -> exp -> Prop :=
  | FreeVar: forall i ty,
      Is_free_in_exp i (Var i ty)
  | FreeState: forall i ty,
      Is_free_in_exp i (State i ty)
  | FreeOp: forall i op e ty,
      List.Exists (Is_free_in_exp i) e ->
      Is_free_in_exp i (Op op e ty)
  | FreeValid: forall i t,
      Is_free_in_exp i (Valid i t).

  Lemma not_free_aux : forall i op el ty,
      ~Is_free_in_exp i (Op op el ty) ->
      List.Forall (fun e => ~Is_free_in_exp i e) el.
  Proof. intros. rewrite Forall_Exists_neg. auto using Is_free_in_exp. Qed.

  Ltac not_free :=
    lazymatch goal with
    | H : ~Is_free_in_exp ?x (Var ?i ?ty) |- _ =>
        let HH := fresh in
        assert (HH : i <> x) by (intro; subst; apply H; constructor);
        clear H; rename HH into H
    | H : ~Is_free_in_exp ?x (State ?i ?ty) |- _ =>
        let HH := fresh in
        assert (HH : i <> x) by (intro; subst; apply H; constructor);
        clear H; rename HH into H
    | H : ~Is_free_in_exp ?x (Valid ?i ?ty) |- _ =>
        let HH := fresh in
        assert (HH : i <> x) by (intro; subst; apply H; constructor);
        clear H; rename HH into H
    | H : ~Is_free_in_exp ?x (Op ?op ?e ?ty) |- _ =>
        apply not_free_aux in H
    end.

  (** Misc. properties *)

  Lemma exp_list_dec : forall el1 el2 : list exp,
    Forall_t (fun e => forall e2 : exp, {e = e2} + {e <> e2}) el1 ->
    {el1 = el2} + {el1 <> el2}.
  Proof.
  intros el1. induction el1 as [| e1 el1]; intros el2 Hel1.
  * destruct el2; now left + right.
  * destruct el2 as [| e2 el2]; try (now right); [].
    inversion_clear Hel1 as [| ? ? He Hel1_rec].
    destruct (He e2).
    + destruct (IHel1 el2 Hel1_rec).
      - now left; f_equal.
      - now right; intro H; inv H.
    + now right; intro H; inv H.
  Qed.

  Lemma exp_dec : forall e1 e2 : exp, {e1 = e2} + {e1 <> e2}.
  Proof.
  induction e1 as [id1 ty1 | id1 ty1 | c1 | op1 el1 IHel1 ty1 | id1 ty1];
  intros [id2 ty2 | id2 ty2 | c2 | op2 el2 ty2 | id2 ty2]; try (now right);
  try (solve [ destruct (equiv_dec c1 c2); compute in *; subst; auto; right; intro H; now inv H
             | destruct (equiv_dec id1 id2); [ destruct (equiv_dec ty1 ty2) |];
               compute in *; subst; auto; right; intro H; now inv H ]); [].
  destruct (equiv_dec op1 op2); [ destruct (equiv_dec ty1 ty2);
  [ destruct (exp_list_dec el1 el2 IHel1) |] |];
  (now left; f_equal) || right; intro H; inv H; unfold complement in *; intuition.
  Qed.

  Instance: EqDec exp eq := { equiv_dec := exp_dec }.

(*
  (** Simple Static Analysis of Obc statements *)

  Definition naked_var (e: exp) : option ident :=
    match e with
    | Var x _ => Some x
    | _ => None
    end.

  Inductive Is_naked_arg_in (x: ident) : stmt -> Prop :=
  | NACall: forall xs c i m es,
        Exists (fun e=> naked_var e = Some x) es ->
        Is_naked_arg_in x (Call xs c i m es)
  | NAIfte1: forall e s1 s2,
        Is_naked_arg_in x s1 ->
        Is_naked_arg_in x (Ifte e s1 s2)
  | NAIfte2: forall e s1 s2,
        Is_naked_arg_in x s2 ->
        Is_naked_arg_in x (Ifte e s1 s2)
  | NAComp1: forall s1 s2,
        Is_naked_arg_in x s1 ->
        Is_naked_arg_in x (Comp s1 s2)
  | NAComp2: forall s1 s2,
        Is_naked_arg_in x s2 ->
        Is_naked_arg_in x (Comp s1 s2).

  Inductive Must_write_in (x: ident) : stmt -> Prop :=
  | MWIAssign: forall e,
      Must_write_in x (Assign x e)
  | MWIAssignSg: forall e,
      Must_write_in x (AssignSt x e)
  | MWIIfte: forall e s1 s2,
      Must_write_in x s1 ->
      Must_write_in x s2 ->
      Must_write_in x (Ifte e s1 s2)
  | MWIComp1: forall s1 s2,
      Must_write_in x s1 ->
      Must_write_in x (Comp s1 s2)
  | MWIComp2: forall s1 s2,
      Must_write_in x s2 ->
      Must_write_in x (Comp s1 s2)
  | MWICall: forall xs cl o m es,
      In x xs ->
      Must_write_in x (Call xs cl o m es).

  Function analyze_obc' (na : PS.t) (mw: PS.t) (s: stmt) : PS.t * PS.t :=
    match s with
    | Assign x e => (na, PS.add x mw)
    | AssignSt x e => (na, PS.add x mw)
    | Ifte e s1 s2 =>
      let (na1, mw1) := analyze_obc' na mw s1 in
      let (na2, mw2) := analyze_obc' na1 mw s2 in
      (na2, PS.inter mw1 mw2)
    | Comp s1 s2 =>
      let (na1, mw1) := analyze_obc' na mw s1 in
      analyze_obc' na1 mw1 s2
    | Call xs cl i m es =>
      (ps_from_fo_list' naked_var es na, ps_from_list' xs mw)
    | Skip => (na, mw)
    end.

  Definition analyze_obc : stmt -> PS.t * PS.t :=
    analyze_obc' PS.empty PS.empty.

  Lemma analyze_obc'_spec_na:
    forall s na mw na' mw' x,
      analyze_obc' na mw s = (na', mw') ->
      PS.In x na' ->
      PS.In x na \/ Is_naked_arg_in x s.
  Proof.
    induction s; simpl; intros na mw na' mw' x Hao Hin.
    - inv Hao; auto.
    - inv Hao; auto.
    - destruct (analyze_obc' na mw s1) as (na1, mw1) eqn:Hao1.
      destruct (analyze_obc' na1 mw s2) as (na2, mw2) eqn:Hao2.
      inversion Hao; subst; clear Hao.
      eapply IHs2 in Hao2; eauto.
      destruct Hao2; auto using Is_naked_arg_in.
      eapply IHs1 in Hao1; eauto.
      destruct Hao1; auto using Is_naked_arg_in.
    - destruct (analyze_obc' na mw s1) as (na1, mw1) eqn:Hao1.
      eapply IHs2 in Hao; eauto.
      destruct Hao; auto using Is_naked_arg_in.
      eapply IHs1 in Hao1; eauto.
      destruct Hao1; auto using Is_naked_arg_in.
    - inv Hao. apply In_ps_from_fo_list' in Hin.
      destruct Hin as [|Hin]; auto. right.
      constructor. apply Exists_exists.
      induction l as [|e es IH]. now inversion Hin.
      inversion Hin as [Hna|Hin']; eauto with datatypes.
      apply IH in Hin' as (e' & Ha & Hb); eauto with datatypes.
    - inv Hao; auto.
  Qed.

  Lemma analyze_obc'_spec_mw:
    forall s na mw na' mw' x,
      analyze_obc' na mw s = (na', mw') ->
      PS.In x mw' ->
      PS.In x mw \/ Must_write_in x s.
  Proof.
    induction s; simpl; intros na mw na' mw' x Hao Hin.
    - inv Hao. apply PS.add_spec in Hin as [Hin|Hin]; subst;
                 auto using Must_write_in.
    - inv Hao. apply PS.add_spec in Hin as [Hin|Hin]; subst;
                 auto using Must_write_in.
    - destruct (analyze_obc' na mw s1) as (na1, mw1) eqn:Hao1.
      destruct (analyze_obc' na1 mw s2) as (na2, mw2) eqn:Hao2.
      inversion Hao; subst; clear Hao.
      apply PS.inter_spec in Hin as (Hin1 & Hin2).
      eapply IHs2 in Hao2; eauto.
      destruct Hao2; auto using Must_write_in.
      eapply IHs1 in Hao1; eauto.
      destruct Hao1; auto using Must_write_in.
    - destruct (analyze_obc' na mw s1) as (na1, mw1) eqn:Hao1.
      eapply IHs2 in Hao; eauto.
      destruct Hao; auto using Must_write_in.
      eapply IHs1 in Hao1; eauto.
      destruct Hao1; auto using Must_write_in.
    - inv Hao. apply In_ps_from_list' in Hin.
      destruct Hin; auto using Must_write_in.
    - inv Hao; auto.
  Qed.

  Lemma analyze_obc_spec_na:
    forall s na mw,
      analyze_obc s = (na, mw) ->
      forall x, PS.In x na -> Is_naked_arg_in x s.
  Proof.
    intros * Ha x Hin.
    eapply analyze_obc'_spec_na in Ha; eauto.
    destruct Ha as [Ha|]; auto.
    now apply not_In_empty in Ha.
  Qed.

  Lemma analyze_obc_spec_mw:
    forall s na mw,
      analyze_obc s = (na, mw) ->
      forall x, PS.In x mw -> Must_write_in x s.
  Proof.
    intros * Ha x Hin.
    eapply analyze_obc'_spec_mw in Ha; eauto.
    destruct Ha as [Ha|]; auto.
    now apply not_In_empty in Ha.
  Qed.
*)
End OBCSYNTAX.

Module ObcSyntaxFun
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op) <: OBCSYNTAX Ids Op OpAux.
  Include OBCSYNTAX Ids Op OpAux.
End ObcSyntaxFun.
