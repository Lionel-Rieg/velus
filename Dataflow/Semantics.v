Require Import List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Coq.Sorting.Permutation.

Require Import Coq.FSets.FMapPositive.
Require Import Rustre.Common.
Require Import Rustre.Dataflow.Syntax.
Require Import Rustre.Dataflow.Ordered.
Require Import Rustre.Dataflow.Stream.

(** * The CoreDF semantics *)

(**

  We provide a "standard" dataflow semantics relating an environment
  of streams to a stream of outputs.

 *)

Module Type SEMANTICS
       (Import Ids : IDS)
       (Import Op  : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Syn : SYNTAX Ids Op)
       (Import Str : STREAM Op)
       (Import Ord : ORDERED Ids Op Syn).

  (** ** Environment and history *)

  (**

An history maps variables to streams of values (the variables'
histories). Taking a snapshot of the history at a given time yields an
environment.

   *)

  (* XXX: naming the environment type *and* its inhabitant [R] is
        probably not a good idea *)
  Definition R := PM.t value.
  Definition history := PM.t (stream value).

  Implicit Type R: R.
  Implicit Type H: history.

  (** ** Instantaneous semantics *)

  Section InstantSemantics.

    Variable base : bool.
    Variable R: R.

    Inductive sem_var_instant (x: ident) v: Prop :=
    | Sv:
        PM.find x R = Some v ->
        sem_var_instant x v.

    Inductive sem_clock_instant: clock -> bool -> Prop :=
    | Sbase:
        sem_clock_instant Cbase base
    | Son:
        forall ck x c b,
          sem_clock_instant ck true ->
          sem_var_instant x (present c) ->
          val_to_bool c = Some b ->
          sem_clock_instant (Con ck x b) true
    | Son_abs1:
        forall ck x c,
          sem_clock_instant ck false ->
          sem_clock_instant (Con ck x c) false
    | Son_abs2:
        forall ck x c b,
          sem_clock_instant ck true ->
          sem_var_instant x (present c) ->
          val_to_bool c = Some b ->
          sem_clock_instant (Con ck x (negb b)) false.

    Inductive sem_lexp_instant: lexp -> value -> Prop:=
    | Sconst:
        forall c v,
          v = (if base then present (sem_const c) else absent) ->
          sem_lexp_instant (Econst c) v
    | Svar:
        forall x v ty,
          sem_var_instant x v ->
          sem_lexp_instant (Evar x ty) v
    | Swhen_eq:
        forall s x c b v,
          sem_var_instant x (present c) ->
          sem_lexp_instant s v ->
          val_to_bool c = Some b ->
          sem_lexp_instant (Ewhen s x b) v
    | Swhen_abs1:
        forall s x c b,
          sem_var_instant x (present c) ->
          val_to_bool c = Some b ->
          sem_lexp_instant s absent ->
          sem_lexp_instant (Ewhen s x (negb b)) absent
    | Swhen_abs:
        forall s x b,
          sem_var_instant x absent ->
          sem_lexp_instant s absent ->
          sem_lexp_instant (Ewhen s x b) absent
    | Sunop_eq:
        forall le op c c' ty,
          sem_lexp_instant le (present c) ->
          sem_unary op c (typeof le) = Some c' ->
          sem_lexp_instant (Eunop op le ty) (present c')
    | Sunop_abs:
        forall le op ty,
          sem_lexp_instant le absent ->
          sem_lexp_instant (Eunop op le ty) absent
    | Sbinop_eq:
        forall le1 le2 op c1 c2 c' ty,
          sem_lexp_instant le1 (present c1) ->
          sem_lexp_instant le2 (present c2) ->
          sem_binary op c1 (typeof le1) c2 (typeof le2) = Some c' ->
          sem_lexp_instant (Ebinop op le1 le2 ty) (present c')
    | Sbinop_abs:
        forall le1 le2 op ty,
          sem_lexp_instant le1 absent ->
          sem_lexp_instant le2 absent ->
          sem_lexp_instant (Ebinop op le1 le2 ty) absent.

    Definition sem_lexps_instant (les: list lexp)(vs: list value) :=
      Forall2 sem_lexp_instant les vs.

    Inductive sem_laexp_instant: clock -> lexp -> value -> Prop:=
    | SLtick:
        forall ck ce c,
          sem_lexp_instant ce (present c) ->
          sem_clock_instant ck true ->
          sem_laexp_instant ck ce (present c)
    | SLabs:
        forall ck ce,
          sem_clock_instant ck false ->
          sem_laexp_instant ck ce absent.

    Inductive sem_laexps_instant: clock -> lexps -> list value -> Prop:=
    | SLticks:
        forall ck ces cs vs,
          vs = map present cs ->
          sem_lexps_instant ces vs ->
          sem_clock_instant ck true ->
          sem_laexps_instant ck ces vs
    | SLabss:
        forall ck ces vs,
          vs = map (fun _ => absent) ces ->
          sem_clock_instant ck false ->
          sem_laexps_instant ck ces vs.

    Inductive sem_cexp_instant: cexp -> value -> Prop :=
    | Smerge_true:
        forall x t f v ty,
          sem_var_instant x (present true_val) ->
          sem_cexp_instant t v ->
          sem_cexp_instant f absent ->
          sem_cexp_instant (Emerge x ty t f) v
    | Smerge_false:
        forall x t f v ty,
          sem_var_instant x (present false_val) ->
          sem_cexp_instant t absent ->
          sem_cexp_instant f v ->
          sem_cexp_instant (Emerge x ty t f) v
    | Smerge_abs:
        forall x t f ty,
          sem_var_instant x absent ->
          sem_cexp_instant t absent ->
          sem_cexp_instant f absent ->
          sem_cexp_instant (Emerge x ty t f) absent
    | Site_eq:
        forall x t f c b ct cf,
          sem_lexp_instant x (present c) ->
          sem_cexp_instant t (present ct) ->
          sem_cexp_instant f (present cf) ->
          val_to_bool c = Some b ->
          sem_cexp_instant (Eite x t f) (if b then present ct else present cf)
    | Site_abs:
        forall b t f,
          sem_lexp_instant b absent ->
          sem_cexp_instant t absent ->
          sem_cexp_instant f absent ->
          sem_cexp_instant (Eite b t f) absent
    | Sexp:
        forall e v,
          sem_lexp_instant e v ->
          sem_cexp_instant (Eexp e) v.

    Inductive sem_caexp_instant: clock -> cexp -> value -> Prop :=
    | SCtick:
        forall ck ce c,
          sem_cexp_instant ce (present c) ->
          sem_clock_instant ck true ->
          sem_caexp_instant ck ce (present c)
    | SCabs:
        forall ck ce,
          sem_clock_instant ck false ->
          sem_caexp_instant ck ce absent.

    Inductive rhs_absent_instant: equation -> Prop :=
    | AEqDef:
        forall x ck cae,
          sem_caexp_instant ck cae absent ->
          rhs_absent_instant (EqDef x ck cae)
    | AEqApp:
        forall x f ck laes vs ty,
          sem_laexps_instant ck laes vs ->
          Forall (fun c => c = absent) vs ->
          rhs_absent_instant (EqApp x ck f laes ty)
    | AEqFby:
        forall x ck v0 lae,
          sem_laexp_instant ck lae absent ->
          rhs_absent_instant (EqFby x ck v0 lae).

  End InstantSemantics.

  (** ** Liftings of instantaneous semantics *)

  Section LiftSemantics.

    Variable bk : stream bool.

    Definition restr H (n: nat): R :=
      PM.map (fun xs => xs n) H.
    Hint Unfold restr.

    Definition lift1 {A B} (f : A -> B) (s : stream A) : stream B
        := fun n => f (s n).
    Hint Unfold lift1.

    Definition lift {A B}
        (sem: bool -> R -> A -> B -> Prop) H x (ys: stream B): Prop :=
      forall n, sem (bk n) (restr H n) x (ys n).
    Hint Unfold lift.

    Definition sem_clock H (ck: clock)(xs: stream bool): Prop :=
      lift sem_clock_instant H ck xs.

    Definition sem_var H (x: ident)(xs: stream value): Prop :=
      lift (fun base => sem_var_instant) H x xs.

    Definition sem_vars H (x: list ident)(xs: stream (list value)): Prop :=
      lift (fun base R => Forall2 (sem_var_instant R)) H x xs.

    Definition sem_laexp H ck (e: lexp)(xs: stream value): Prop :=
      lift (fun base R => sem_laexp_instant base R ck) H e xs.

    Definition sem_laexps
        H (ck: clock)(e: lexps)(xs: stream (list value)): Prop :=
      lift (fun base R => sem_laexps_instant base R ck) H e xs.

    Definition sem_lexp H (e: lexp)(xs: stream value): Prop :=
      lift sem_lexp_instant H e xs.

    Definition sem_lexps H (e: lexps)(xs: stream (list value)): Prop :=
      lift sem_lexps_instant H e xs.

    Definition sem_caexp H ck (c: cexp)(xs: stream value): Prop :=
      lift (fun base R => sem_caexp_instant base R ck) H c xs.

    Definition sem_cexp H (c: cexp)(xs: stream value): Prop :=
      lift sem_cexp_instant H c xs.

  End LiftSemantics.

  (** ** Time-dependent semantics *)

  Definition absent_list (xss: stream (list value))(n: nat): Prop :=
    xss n = map (fun _ => absent) (xss n).

  Definition present_list
      (xss: stream (list value))(n: nat)(vs: list val): Prop :=
    xss n = map present vs.

  Definition clock_of (xss: stream (list value))(bs: stream bool): Prop :=
    forall n,
      (exists vs, present_list xss n vs) <-> bs n = true.

  Inductive sem_equation G : stream bool -> history -> equation -> Prop :=
  | SEqDef:
      forall bk H x xs ck ce,
        sem_var bk H x xs ->
        sem_caexp bk H ck ce xs ->
        sem_equation G bk H (EqDef x ck ce)
  | SEqApp:
      forall bk H x ck f arg ls xs ty,
        sem_laexps bk H ck arg ls ->
        sem_var bk H x xs ->
        sem_node G f ls xs ->
        sem_equation G bk H (EqApp x ck f arg ty)
  | SEqFby:
      forall bk H x ls xs c0 ck le,
        sem_laexp bk H ck le ls ->
        sem_var bk H x xs ->
        xs = fby (sem_const c0) ls ->
        sem_equation G bk H (EqFby x ck c0 le)

  with sem_node G: ident -> stream (list value) -> stream value -> Prop :=
       | SNode:
           forall bk f xss ys i o v eqs ingt0 defd vout decl nodup good,
             clock_of xss bk ->
             find_node f G = Some (mk_node f i o v eqs
                                           ingt0 defd vout decl nodup good) ->
             (exists H,
                 sem_vars bk H (map fst i) xss
                 /\ sem_var bk H (fst o) ys
                 (* XXX: This should be in Welldef_glob: *)
                 (* output clock matches input clock *)
                 /\ (forall n, absent_list xss n <-> ys n = absent)
                 (* XXX: END *)
                 /\ Forall (sem_equation G bk H) eqs) ->
             sem_node G f xss ys.

  Definition sem_nodes (G: global) : Prop :=
    Forall (fun no => exists xs ys, sem_node G no.(n_name) xs ys) G.

  (** ** Induction principle for [sem_node] and [sem_equation] *)

  (** The automagically-generated induction principle is not strong
enough: it does not support the internal fixpoint introduced by
[Forall] *)

  Section sem_node_mult.
    Variable G: global.

    Variable P : forall bk H (eq: equation), sem_equation G bk H eq -> Prop.
    Variable Pn : forall (f: ident) xss ys, sem_node G f xss ys -> Prop.

    Hypothesis EqDef_case :
      forall (bk : stream bool)
             (H    : history)
             (x    : ident)
             (ck   : clock)
             (ce   : cexp)
             (xs   : stream value)
             (Hvar : sem_var bk H x xs)
        (Hexp : sem_caexp bk H ck ce xs),
        P bk H (EqDef x ck ce) (SEqDef G bk H x xs ck ce Hvar Hexp).

    Hypothesis EqApp_case :
      forall (bk: stream bool)
             (H     : history)
             (y     : ident)
             (ck    : clock)
             (f     : ident)
             (les   : lexps)
             (ls    : stream (list value))
             (ys    : stream value)
             (ty    : typ)
             (Hlaes : sem_laexps bk H ck les ls)
             (Hvar  : sem_var bk H y ys)
             (Hnode : sem_node G f ls ys),
        Pn f ls ys Hnode ->
        P bk H (EqApp y ck f les ty)
          (SEqApp G bk H y ck f les ls ys ty Hlaes Hvar Hnode).

    Hypothesis EqFby_case :
      forall (bk: stream bool)
             (H   : history)
             (y   : ident)
             (ls  : stream value)
             (yS  : stream value)
             (c0  : const)
             (ck  : clock)
             (lae : lexp)
             (Hls : sem_laexp bk H ck lae ls)
             (Hys : sem_var bk H y yS)
             (Hfby: yS = fby (sem_const c0) ls),
        P bk H (EqFby y ck c0 lae)
          (SEqFby G bk H y ls yS c0 ck lae Hls Hys Hfby).

    Hypothesis SNode_case :
      forall (bk    : stream bool)
             (f     : ident)
             (xss   : stream (list value))
             (ys    : stream value)
             (i     : list (ident * typ))
             (o     : ident * typ)
             (v     : list (ident * typ))
             (eqs   : list equation)
             (ingt0 : 0 < length i)
             (defd  : Permutation (map var_defined eqs)
                                  (map fst (v ++ [o])))
             (vout  : ~PS.In (fst o) (memories eqs))
             (decl  : Forall (VarsDeclared (i ++ v ++ [o])) eqs)
             (nodup : NoDupMembers (i ++ v ++ [o]))
             (good  : Forall NotReserved (i ++ v ++ [o]))
             (Hck   : clock_of xss bk)
             (Hf    : find_node f G =
                      Some (mk_node f i o v eqs
                                    ingt0 defd vout decl nodup good))
             (Heqs  : exists H,
            sem_vars bk H (map fst i) xss
            /\ sem_var bk H (fst o) ys
            /\ (forall n, absent_list xss n <-> ys n = absent)
            /\ Forall (sem_equation G bk H) eqs),
        (exists H,
            sem_vars bk H (map fst i) xss
            /\ sem_var bk H (fst o) ys
            /\ (forall n, absent_list xss n <-> ys n = absent)
            /\ Forall (fun eq=> exists Hsem, P bk H eq Hsem) eqs)
        -> Pn f xss ys
              (SNode G bk f xss ys i o v eqs ingt0
                     defd vout decl nodup good Hck Hf Heqs).

    Fixpoint sem_equation_mult (bk: stream bool)
             (H  : history)
                         (eq : equation)
                         (Heq : sem_equation G bk H eq) {struct Heq}
      : P bk H eq Heq :=
      match Heq in (sem_equation _ bk H eq) return (P bk H eq Heq) with
      | SEqDef bk H y xs ck ce Hvar Hexp => EqDef_case bk H y ck ce xs Hvar Hexp
      | SEqApp bk H y ck f lae ls ys ty Hlae Hvar Hnode =>
        EqApp_case bk H y ck f lae ls ys ty Hlae Hvar Hnode
                   (sem_node_mult f ls ys Hnode)
      | SEqFby bk H y ls yS ck v0 lae Hls Hys Hfby =>
          EqFby_case bk H y ls yS ck v0 lae Hls Hys Hfby
      end

    with sem_node_mult (f  : ident)
                       (ls : stream (list value))
                       (ys : stream value)
                       (Hn : sem_node G f ls ys) {struct Hn} : Pn f ls ys Hn :=
           match Hn in (sem_node _ f ls ys) return (Pn f ls ys Hn) with
           | SNode bk f ls ys i o v eqs
                   ingt0 defd vout decl nodup good Hck Hf Hnode =>
             SNode_case bk f ls ys i o v eqs
                        ingt0 defd vout decl nodup good Hck Hf Hnode
                        (* Turn: exists H : history,
                        (forall n, sem_var H (v_name i) n (xs n))
                     /\ (forall n, sem_var H (v_name o) n (ys n))
                     /\ (forall n, xs n = absent <-> ys n = absent)
                     /\ Forall (sem_equation G H) eqs
             into: exists H : history,
                        (forall n, sem_var H (v_name i) n (xs n))
                     /\ (forall n, sem_var H (v_name o) n (ys n))
                     /\ (forall n, xs n = absent <-> ys n = absent)
                     /\ Forall (fun eq=>exists Hsem, P H eq Hsem) eqs *)
                        (match Hnode with
                         | ex_intro H (conj Hxs (conj Hys (conj Hout Heqs))) =>
                           ex_intro _ H (conj Hxs (conj Hys (conj Hout
                             (((fix map (eqs : list equation)
                                (Heqs: Forall (sem_equation G bk H) eqs) :=
                                  match Heqs in Forall _ fs
                                        return (Forall
                                                  (fun eq=> exists Hsem,
                                                       P bk H eq Hsem) fs)
                                  with
                                  | Forall_nil => Forall_nil _
                                  | Forall_cons eq eqs Heq Heqs' =>
                                    Forall_cons eq (@ex_intro _ _ Heq
                                                (sem_equation_mult bk H eq Heq))
                                                     (map eqs Heqs')
                                  end) eqs Heqs)))))
                         end)
           end.

  End sem_node_mult.


  (** ** Determinism of the semantics *)

  (** *** Instantaneous semantics *)

  Section InstantDeterminism.

    Variable base: bool.
    Variable R: R.

    Lemma sem_var_instant_det:
      forall x v1 v2,
        sem_var_instant R x v1
        -> sem_var_instant R x v2
        -> v1 = v2.
    Proof.
      intros x v1 v2 H1 H2.
      inversion_clear H1 as [Hf1];
        inversion_clear H2 as [Hf2];
        congruence.
    Qed.

    Lemma sem_clock_instant_det:
      forall ck v1 v2,
        sem_clock_instant base R ck v1
        -> sem_clock_instant base R ck v2
        -> v1 = v2.
    Proof.
      induction ck; repeat inversion 1; subst; intuition;
      try repeat progress match goal with
          | H1: sem_clock_instant ?bk ?R ?ck ?l,
                H2: sem_clock_instant ?bk ?R ?ck ?r |- _ =>
            apply IHck with (1:=H1) in H2; discriminate
          | H1: sem_var_instant ?R ?i (present ?l),
                H2: sem_var_instant ?R ?i (present ?r) |- _ =>
            apply sem_var_instant_det with (1:=H1) in H2;
              injection H2; intro; subst
          | H1: val_to_bool _ = Some ?b, H2: val_to_bool _ = _ |- _ =>
            rewrite H1 in H2; destruct b; discriminate
          end.
    Qed.

    Lemma sem_lexp_instant_det:
      forall e v1 v2,
        sem_lexp_instant base R e v1
        -> sem_lexp_instant base R e v2
        -> v1 = v2.
    Proof.
      induction e (* using lexp_ind2 *);
        try now (do 2 inversion_clear 1);
        match goal with
        | H1:sem_var_instant ?R ?e (present ?b1),
          H2:sem_var_instant ?R ?e (present ?b2),
          H3: ?b1 <> ?b2 |- _ =>
          exfalso; apply H3;
          cut (present (Vbool b1) = present (Vbool b2)); [now injection 1|];
          eapply sem_var_instant_det; eassumption
        | H1:sem_var_instant ?R ?e ?v1,
          H2:sem_var_instant ?R ?e ?v2 |- ?v1 = ?v2 =>
          eapply sem_var_instant_det; eassumption
        | H1:sem_var_instant ?R ?e (present _),
          H2:sem_var_instant ?R ?e absent |- _ =>
          apply (sem_var_instant_det _ _ _ _ H1) in H2;
          discriminate
        | _ => auto
        end.
    - do 2 inversion_clear 1; destruct base; congruence.
    - intros v1 v2 Hsem1 Hsem2.
      inversion Hsem1; inversion Hsem2; subst;
      repeat progress match goal with
      | H1:sem_lexp_instant ?b ?R ?e ?v1,
           H2:sem_lexp_instant ?b ?R ?e ?v2 |- _ =>
        apply IHe with (1:=H1) in H2
      | H1:sem_var_instant ?R ?i ?v1,
           H2:sem_var_instant ?R ?i ?v2 |- _ =>
        apply sem_var_instant_det with (1:=H1) in H2
      | H1:sem_unary _ _ _ = Some ?v1,
           H2:sem_unary _ _ _ = Some ?v2 |- _ =>
        rewrite H1 in H2; injection H2; intro; subst
      | Hp:present _ = present _ |- _ =>
        injection Hp; intro; subst
      | H1:val_to_bool _ = Some _,
        H2:val_to_bool _ = Some (negb _) |- _ =>
        rewrite H2 in H1; exfalso; injection H1;
          now apply Bool.no_fixpoint_negb
      end; subst; try easy.
    - intros v1 v2 Hsem1 Hsem2.
      inversion_clear Hsem1; inversion_clear Hsem2;
      repeat progress match goal with
      | H1:sem_lexp_instant _ _ e1 _, H2:sem_lexp_instant _ _ e1 _ |- _ =>
        apply IHe1 with (1:=H1) in H2
      | H1:sem_lexp_instant _ _ e2 _, H2:sem_lexp_instant _ _ e2 _ |- _ =>
        apply IHe2 with (1:=H1) in H2
      | H1:sem_unary _ _ _ = _, H2:sem_unary _ _ _ = _ |- _ =>
        rewrite H1 in H2; injection H2; intro; subst
      | H1:sem_binary _ _ _ _ _ = Some ?v1,
           H2:sem_binary _ _ _ _ _ = Some ?v2 |- _ =>
        rewrite H1 in H2; injection H2; intro; subst
      | H:present _ = present _ |- _ => injection H; intro; subst
      end; subst; try easy.
    Qed.

    Lemma sem_laexp_instant_det:
      forall ck e v1 v2,
        sem_laexp_instant base R ck e v1
        -> sem_laexp_instant base R ck e v2
        -> v1 = v2.
    Proof.
      intros ck e v1 v2.
      do 2 inversion_clear 1;
        match goal with
        | H1:sem_lexp_instant _ _ _ _, H2:sem_lexp_instant _ _ _ _ |- _ =>
          eapply sem_lexp_instant_det; eassumption
        | H1:sem_clock_instant _ _ _ ?T, H2:sem_clock_instant _ _ _ ?F |- _ =>
          assert (T = F) by (eapply sem_clock_instant_det; eassumption);
            try discriminate
        end; auto.
    Qed.

    Lemma sem_lexps_instant_det:
      forall les cs1 cs2,
        sem_lexps_instant base R les cs1 ->
        sem_lexps_instant base R les cs2 ->
        cs1 = cs2.
    Proof.
      intros les cs1 cs2. apply Forall2_det. apply sem_lexp_instant_det.
    Qed.

    Lemma sem_laexps_instant_det:
      forall ck e v1 v2,
        sem_laexps_instant base R ck e v1
        -> sem_laexps_instant base R ck e v2
        -> v1 = v2.
    Proof.
      intros until v2.
      do 2 inversion_clear 1;
        match goal with
        | H1: sem_lexps_instant _ _ _ _, H2: sem_lexps_instant _ _ _ _ |- _ =>
          eapply sem_lexps_instant_det; eauto
        | H1:sem_clock_instant _ _ _ ?T, H2:sem_clock_instant _ _ _ ?F |- _ =>
          let H := fresh in
          assert (H: T = F) by (eapply sem_clock_instant_det; eassumption);
            try discriminate H
        end; congruence.
    Qed.

    Lemma sem_cexp_instant_det:
      forall e v1 v2,
        sem_cexp_instant base R e v1
        -> sem_cexp_instant base R e v2
        -> v1 = v2.
    Proof.
      induction e;
        do 2 inversion_clear 1;
        try repeat progress match goal with
            | H1: sem_cexp_instant ?bk ?R ?e ?l,
                  H2: sem_cexp_instant ?bk ?R ?e ?r |- _ =>
              apply IHe1 with (1:=H1) in H2
              || apply IHe2 with (1:=H1) in H2;
                injection H2; intro; subst
            | H1: sem_var_instant ?R ?i (present true_val),
                  H2: sem_var_instant ?R ?i (present false_val) |- _ =>
              apply sem_var_instant_det with (1:=H1) in H2;
                exfalso; injection H2; now apply true_not_false_val
            | H1: sem_lexp_instant ?bk ?R ?l ?v1,
                  H2: sem_lexp_instant ?bk ?R ?l ?v2 |- _ =>
              apply sem_lexp_instant_det with (1:=H1) in H2;
                discriminate || injection H2; intro; subst
            | H1: sem_var_instant ?R ?i (present _),
                  H2: sem_var_instant ?R ?i absent |- _ =>
              apply sem_var_instant_det with (1:=H1) in H2; discriminate
            | H1: val_to_bool _ = Some _,
                  H2:val_to_bool _ = Some _ |- _ =>
              rewrite H1 in H2; injection H2; intro; subst
                            end; auto.
      eapply sem_lexp_instant_det; eassumption.
    Qed.

    Lemma sem_caexp_instant_det:
      forall ck e v1 v2,
        sem_caexp_instant base R ck e v1
        -> sem_caexp_instant base R ck e v2
        -> v1 = v2.
    Proof.
      intros until v2.
      do 2 inversion_clear 1;
        match goal with
        | H1: sem_cexp_instant _ _ _ _,
              H2: sem_cexp_instant _ _ _ _ |- _ =>
          eapply sem_cexp_instant_det; eassumption
        | H1:sem_clock_instant _ _ _ ?T,
             H2:sem_clock_instant _ _ _ ?F |- _ =>
          let H := fresh in
          assert (H: T = F) by (eapply sem_clock_instant_det; eassumption);
            try discriminate H
        end; congruence.
    Qed.

  End InstantDeterminism.

  (** *** Lifted semantics *)

  Section LiftDeterminism.

    Variable bk : stream bool.

    Require Import Logic.FunctionalExtensionality.

    Lemma lift_det:
      forall {A B} (P: bool -> R -> A -> B -> Prop) (bk: stream bool)
                   H x (xs1 xs2 : stream B),
        (forall b R v1 v2, P b R x v1 -> P b R x v2 -> v1 = v2) ->
        lift bk P H x xs1 -> lift bk P H x xs2 -> xs1 = xs2.
    Proof.
      intros ** Hpoint H1 H2.
      extensionality n. specialize (H1 n). specialize (H2 n).
      eapply Hpoint; eassumption.
    Qed.

    Ltac apply_lift sem_det :=
      intros; eapply lift_det; try eassumption;
      compute; intros; eapply sem_det; eauto.

    Lemma sem_var_det:
      forall H x xs1 xs2,
        sem_var bk H x xs1 -> sem_var bk H x xs2 -> xs1 = xs2.
    Proof.
      apply_lift sem_var_instant_det.
    Qed.

    Lemma sem_clock_det : forall H ck bs1 bs2,
        sem_clock bk H ck bs1 -> sem_clock bk H ck bs2 -> bs1 = bs2.
    Proof.
      apply_lift sem_clock_instant_det.
    Qed.

    Lemma sem_lexp_det:
      forall H e xs1 xs2,
        sem_lexp bk H e xs1 -> sem_lexp bk H e xs2 -> xs1 = xs2.
    Proof.
      apply_lift sem_lexp_instant_det.
    Qed.

    Lemma sem_lexps_det:
      forall H les cs1 cs2,
        sem_lexps bk H les cs1 ->
        sem_lexps bk H les cs2 ->
        cs1 = cs2.
    Proof.
      apply_lift sem_lexps_instant_det.
    Qed.

    Lemma sem_laexp_det:
      forall H ck e xs1 xs2,
        sem_laexp bk H ck e xs1 -> sem_laexp bk H ck e xs2 -> xs1 = xs2.
    Proof.
      apply_lift sem_laexp_instant_det.
    Qed.

    Lemma sem_laexps_det:
      forall H ck e xs1 xs2,
        sem_laexps bk H ck e xs1 -> sem_laexps bk H ck e xs2 -> xs1 = xs2.
    Proof.
      apply_lift sem_laexps_instant_det.
    Qed.

    Lemma sem_cexp_det:
      forall H c xs1 xs2,
        sem_cexp bk H c xs1 -> sem_cexp bk H c xs2 -> xs1 = xs2.
    Proof.
      apply_lift sem_cexp_instant_det.
    Qed.

    Lemma sem_caexp_det:
      forall H ck c xs1 xs2,
        sem_caexp bk H ck c xs1 -> sem_caexp bk H ck c xs2 -> xs1 = xs2.
    Proof.
      apply_lift sem_caexp_instant_det.
    Qed.

  (* XXX: every semantics definition, including [sem_var] which doesn't
need it, takes a base clock value or base clock stream, except
[sem_var_instant]. For uniformity, we may want to pass a (useless)
clock to [sem_var_instant] too. *)

  End LiftDeterminism.

  Ltac sem_det :=
    match goal with
    | H1: sem_cexp_instant ?bk ?H ?C ?X,
          H2: sem_cexp_instant ?bk ?H ?C ?Y |- ?X = ?Y =>
      eapply sem_cexp_instant_det; eexact H1 || eexact H2
    | H1: sem_cexp ?bk ?H ?C ?X,
          H2: sem_cexp ?bk ?H ?C ?Y |- ?X = ?Y =>
      eapply sem_cexp_det; eexact H1 || eexact H2
    | H1: sem_lexps_instant ?bk ?H ?C ?X,
          H2: sem_lexps_instant ?bk ?H ?C ?Y |- ?X = ?Y =>
      eapply sem_lexps_instant_det; eexact H1 || eexact H2
    | H1: sem_lexps ?bk ?H ?C ?X,
          H2: sem_lexps ?bk ?H ?C ?Y |- ?X = ?Y =>
      eapply sem_lexps_det; eexact H1 || eexact H2
    | H1: sem_laexps_instant ?bk ?H ?ck ?C ?X,
          H2: sem_laexps_instant ?bk ?H ?ck ?C ?Y |- ?X = ?Y =>
      eapply sem_laexps_instant_det; eexact H1 || eexact H2
    | H1: sem_laexps ?bk ?H ?ck ?C ?X,
          H2: sem_laexps ?bk ?H ?ck ?C ?Y |- ?X = ?Y =>
      eapply sem_laexps_det; eexact H1 || eexact H2
    | H1: sem_lexp_instant ?bk ?H ?C ?X,
          H2: sem_lexp_instant ?bk ?H ?C ?Y |- ?X = ?Y =>
      eapply sem_lexp_instant_det; eexact H1 || eexact H2
    | H1: sem_lexp ?bk ?H ?C ?X,
          H2: sem_lexp ?bk ?H ?C ?Y |- ?X = ?Y =>
      eapply sem_lexp_det; eexact H1 || eexact H2
    | H1: sem_laexp_instant ?bk ?H ?CK ?C ?X,
          H2: sem_laexp_instant ?bk ?H ?CK ?C ?Y |- ?X = ?Y =>
      eapply sem_laexp_instant_det; eexact H1 || eexact H2
    | H1: sem_laexp ?bk ?H ?CK ?C ?X,
          H2: sem_laexp ?bk ?H ?CK ?C ?Y |- ?X = ?Y =>
      eapply sem_laexp_det; eexact H1 || eexact H2
    | H1: sem_var_instant ?H ?C ?X,
          H2: sem_var_instant ?H ?C ?Y |- ?X = ?Y =>
      eapply sem_var_instant_det; eexact H1 || eexact H2
    | H1: sem_var ?bk ?H ?C ?X,
          H2: sem_var ?bk ?H ?C ?Y |- ?X = ?Y =>
      eapply sem_var_det; eexact H1 || eexact H2
    end.

  (** ** Properties of the [global] environment *)

  Lemma find_node_other:
    forall f node G node',
      node.(n_name) <> f
      -> (find_node f (node::G) = Some node'
         <-> find_node f G = Some node').
  Proof.
    intros f node G node' Hnf.
    apply BinPos.Pos.eqb_neq in Hnf.
    simpl.
    unfold ident_eqb.
    rewrite Hnf.
    reflexivity.
  Qed.

  Lemma sem_node_cons:
    forall node G f xs ys,
      Ordered_nodes (node::G)
      -> sem_node (node::G) f xs ys
      -> node.(n_name) <> f
      -> sem_node G f xs ys.
  Proof.
    intros node G f xs ys Hord Hsem Hnf.
    revert Hnf.
    induction Hsem as [
         | bk H y ck f lae ls ys ty Hlae Hvar Hnode IH
         |
         | bk f xs ys i o v eqs ingt0 defd vout decl nodup good Hbk Hf Heqs IH]
            using sem_node_mult
          with (P := fun bk H eq Hsem => ~Is_node_in_eq node.(n_name) eq
                                      -> sem_equation G bk H eq).
    - econstructor; eassumption.
    - intro Hnin.
      eapply @SEqApp with (1:=Hlae) (2:=Hvar).
      apply IH. intro Hnf. apply Hnin. rewrite Hnf. constructor.
    - intro; eapply SEqFby; eassumption.
    - intro.
      rewrite find_node_tl with (1:=Hnf) in Hf.
      eapply SNode; eauto.
      clear Heqs.
      destruct IH as [H [Hxs [Hys [Hout Heqs]]]].
      exists H.
      repeat (split; eauto).
      set (cnode := {| n_name  := f;
                       n_in    := i;
                       n_out   := o;
                       n_vars  := v;
                       n_eqs   := eqs;
                       n_ingt0 := ingt0;
                       n_defd  := defd;
                       n_vout  := vout;
                       n_decl  := decl;
                       n_nodup := nodup;
                       n_good  := good
                    |}).
      assert (Forall (fun eq => ~ Is_node_in_eq (n_name node) eq) (n_eqs cnode))
        by (eapply Is_node_in_Forall; try eassumption;
            eapply find_node_later_not_Is_node_in; try eassumption).
      eapply Forall_Forall in Heqs; try eauto.
      eapply Forall_impl with (2:=Heqs).
      destruct 1 as [Hnini [Hsem HH]].
      intuition.
  Qed.

  Lemma find_node_find_again:
    forall G f i o v eqs ingt0 defd vout decl nodup good g,
      Ordered_nodes G
      -> find_node f G =
         Some {| n_name := f; n_in := i; n_out := o;
                 n_vars := v; n_eqs := eqs; n_decl := decl;
                 n_ingt0 := ingt0; n_defd := defd; n_vout := vout;
                 n_nodup := nodup; n_good := good |}
      -> Is_node_in g eqs
      -> Exists (fun nd=> g = nd.(n_name)) G.
  Proof.
    intros G f i o v eqs ingt0 defd vout decl nodup good g Hord Hfind Hini.
    apply find_node_split in Hfind.
    destruct Hfind as [bG [aG Hfind]].
    rewrite Hfind in *.
    clear Hfind.
    apply Ordered_nodes_append in Hord.
    apply Exists_app.
    constructor 2.
    inversion_clear Hord as [|? ? ? HH H0]; clear H0.
    apply HH in Hini; clear HH.
    intuition.
  Qed.

  Lemma sem_node_cons2:
    forall nd G f xs ys,
      Ordered_nodes G
      -> sem_node G f xs ys
      -> Forall (fun nd' : node => n_name nd <> n_name nd') G
      -> sem_node (nd::G) f xs ys.
  Proof.
    Hint Constructors sem_equation.
    intros nd G f xs ys Hord Hsem Hnin.
    assert (Hnin':=Hnin).
    revert Hnin'.
    induction Hsem as [
       | bk H y f lae ls ys Hlae Hvar Hnode IH
       |
       | bk f xs ys i o v eqs ingt0 defd vout decl nodup good Hbk Hfind Heqs IH]
          using sem_node_mult
        with (P := fun bk H eq Hsem =>
                     ~Is_node_in_eq nd.(n_name) eq
                     -> sem_equation (nd::G) bk H eq);
      try eauto; intro HH.
    clear HH.
    assert (nd.(n_name) <> f) as Hnf.
    { intro Hnf.
      rewrite Hnf in *.
      apply find_node_split in Hfind.
      destruct Hfind as [bG [aG Hge]].
      rewrite Hge in Hnin.
      apply Forall_app in Hnin.
      destruct Hnin as [H0 Hfg]; clear H0.
      inversion_clear Hfg.
      match goal with H:f<>_ |- False => apply H end.
      reflexivity. }
    apply find_node_other with (2:=Hfind) in Hnf.
    econstructor; eauto.
    clear Heqs.
    destruct IH as [H [Hxs [Hys [Hout Heqs]]]].
    exists H.
    intuition; clear Hxs Hys.
    assert (forall g, Is_node_in g eqs
                 -> Exists (fun nd=> g = nd.(n_name)) G)
      as Hniex
        by (intros g Hini;
             apply find_node_find_again with (1:=Hord) (2:=Hfind) in Hini;
             exact Hini).
    assert (Forall
              (fun eq=> forall g,
                   Is_node_in_eq g eq
                   -> Exists (fun nd=> g = nd.(n_name)) G) eqs) as HH.
    {
      clear defd vout decl nodup good Hfind Heqs Hnf.
      induction eqs as [|eq eqs IH]; [now constructor|].
      constructor.
      - intros g Hini.
        apply Hniex.
        constructor 1; apply Hini.
      - apply IH.
        intros g Hini; apply Hniex.
        constructor 2; apply Hini.
    }
    apply Forall_Forall with (1:=HH) in Heqs.
    apply Forall_impl with (2:=Heqs).
    intros eq IH.
    destruct IH as [Hsem [IH0 IH1]].
    apply IH1.
    intro Hini.
    apply Hsem in Hini.
    apply Forall_Exists with (1:=Hnin) in Hini.
    apply Exists_exists in Hini.
    destruct Hini as [nd' [Hin [Hneq Heq]]].
    intuition.
  Qed.


  Lemma Forall_sem_equation_global_tl:
    forall bk nd G H eqs,
      Ordered_nodes (nd::G)
      -> ~ Is_node_in nd.(n_name) eqs
      -> Forall (sem_equation (nd::G) bk H) eqs
      -> Forall (sem_equation G bk H) eqs.
  Proof.
    intros bk nd G H eqs Hord.
    induction eqs as [|eq eqs IH]; [trivial|].
    intros Hnini Hsem.
    apply Forall_cons2 in Hsem; destruct Hsem as [Hseq Hseqs].
    apply IH in Hseqs.
    2:(apply not_Is_node_in_cons in Hnini;
        destruct Hnini; assumption).
    apply Forall_cons with (2:=Hseqs).
    inversion Hseq as [|? ? ? ? ? ? ? Hsem Hvar Hnode|]; subst.
    - econstructor; eassumption.
    - apply not_Is_node_in_cons in Hnini.
      destruct Hnini as [Hninieq Hnini].
      assert (nd.(n_name) <> f) as Hnf
          by (intro HH; apply Hninieq; rewrite HH; constructor).
      econstructor; eauto.
      eapply sem_node_cons; eauto.
    - econstructor; eauto.
  Qed.

  (** ** Clocking property *)

  Lemma subrate_clock:
    forall R ck,
      sem_clock_instant false R ck false.
  Proof.
    Hint Constructors sem_clock_instant.
    intros R ck.
    induction ck; eauto.
  Qed.

  (* XXX: Similarly, instead of [rhs_absent_instant] and friends, we
should prove that all the semantic rules taken at [base = false] yield
an absent value *)

  (** ** Presence and absence in non-empty lists *)

  Lemma not_absent_present_list:
    forall xss n vs,
      0 < length vs ->
      present_list xss n vs ->
      ~ absent_list xss n.
  Proof.
    intros * Hnz Hpres Habs.
    unfold present_list in Hpres.
    unfold absent_list in Habs.
    rewrite Hpres in *.
    destruct vs; [now inversion Hnz|].
    inversion_clear Habs; discriminate.
  Qed.

  Lemma sem_vars_gt0:
    forall bk H (xs: list (ident * typ)) ls,
      0 < length xs ->
      sem_vars bk H (map fst xs) ls ->
      forall n, 0 < length (ls n).
  Proof.
    intros ** Hgt0 Hsem n.
    unfold sem_vars, lift in Hsem.
    specialize Hsem with n.
    apply Forall2_length in Hsem.
    rewrite map_length in Hsem.
    now rewrite Hsem in Hgt0.
  Qed.
  
End SEMANTICS.
