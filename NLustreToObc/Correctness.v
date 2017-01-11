Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Require Import Velus.Common.
Require Import Velus.Operators.
Open Scope positive.

Require Import Velus.RMemory.
Require Import Velus.NLustre.
Require Import Velus.Obc.
Require Import Velus.NLustreToObc.Translation.
Require Import Velus.NLustreToObc.Correctness.IsPresent.
Require Import Velus.NLustreToObc.Correctness.MemoryCorres.
Require Import Velus.NLustreToObc.Typing.

Module Type CORRECTNESS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import DF    : NLUSTRE Ids Op OpAux)
       (Import Obc   : OBC Ids Op OpAux)
       (Import Mem   : MEMORIES Ids Op DF.Syn)

       (Import Trans : TRANSLATION Ids Op OpAux DF.Syn Obc.Syn Mem)
       (Import Typing: TYPING Ids Op OpAux DF Obc Mem Trans).

  Module Import IsP := IsPresentFun Ids Op OpAux DF.Syn Obc.Syn Obc.Sem Mem Trans.
  Module Import MemCor := MemoryCorresFun Ids Op OpAux DF Obc.
  
  (** ** Technical lemmas *)

  Lemma exp_eval_tovar:
    forall x ty v menv env mems,
      exp_eval menv env (tovar mems (x, ty)) v
      <-> (exp_eval menv env (State x ty) v /\ PS.In x mems)
        \/ (exp_eval menv env (Var x ty) v /\ ~PS.In x mems).
  Proof.
    split; intro Heval;
    destruct In_dec with x mems as [Hxm|Hxm];
    pose proof Hxm as Hxmt;
    apply PS.mem_spec in Hxmt || apply mem_spec_false in Hxmt;
    unfold tovar in *;
    rewrite Hxmt in *;
    intuition.
  Qed.

  Lemma stmt_eval_translate_eqns_cons:
    forall prog mems menv env menv' env' eq eqs,
      stmt_eval prog menv env (translate_eqns mems (eq :: eqs)) (menv', env')
      <->
      (exists menv'' env'',
          stmt_eval prog menv env (translate_eqns mems eqs) (menv'', env'')
          /\ stmt_eval prog menv'' env'' (translate_eqn mems eq) (menv', env')).
  Proof. (* TODO: redo proof *)
    split.
    - intro H.
      unfold translate_eqns in H.
      simpl in H.
      apply stmt_eval_fold_left_shift in H.
      destruct H as [menv'' [env'' [H1 H2]]].
      exists menv'', env''.
      split; [now apply H1|].
      inversion_clear H2.
      inversion H0.
      subst.
      exact H.
    - intro H.
      destruct H as [menv'' [env'' [H1 H2]]].
      unfold translate_eqns.
      simpl.
      apply stmt_eval_fold_left_shift.
      exists menv'', env''.
      split; [now apply H1|].
      eapply Icomp. apply H2.
      apply Iskip.
  Qed.

  (** ** [Control] absorption theorems *)

  Lemma stmt_eval_Control_fwd:
    forall prog menv env mems c s menv' env',
      stmt_eval prog menv env (Control mems c s) (menv', env')
      -> (Is_present_in mems menv env c
         /\ stmt_eval prog menv env s (menv', env'))
        \/ (Is_absent_in mems menv env c
           /\ menv' = menv /\ env' = env).
  Proof.
    Hint Constructors Is_present_in Is_absent_in.
    intros prog menv env mems c s menv' env' Hs.
    revert s Hs.
    induction c; [now intuition|].
    intros s Hs.
    simpl in Hs.
    destruct b;
    specialize (IHc _ Hs); clear Hs;
      destruct IHc as [[Hp Hs]|[Hp [Hmenv Henv]]];
      try inversion_clear Hs; subst; intuition.
    - destruct b; [now eauto|].
      right. match goal with H:stmt_eval _ _ _ _ _ |- _ => inv H end.
      assert (true = negb false) as Htrue by reflexivity.
      rewrite Htrue. eauto.
    - destruct b; [|now eauto].
      right. match goal with H:stmt_eval _ _ _ _ _ |- _ => inv H end.
      assert (false = negb true) as Hfalse by reflexivity.
      rewrite Hfalse. eauto.
  Qed.

  Lemma stmt_eval_Control:
    forall prog mems menv env ck stmt,
      (Is_absent_in mems menv env ck
       -> stmt_eval prog menv env (Control mems ck stmt) (menv, env))
      /\
      (forall menv' env',
          Is_present_in mems menv env ck
          -> stmt_eval prog menv env stmt (menv', env')
          -> stmt_eval prog menv env (Control mems ck stmt) (menv', env')).
  Proof.
    Hint Constructors stmt_eval.
    intros prog mems menv env ck.
    induction ck; intro s; split.
    - inversion 1.
    - intros menv' env' Hp Hs; exact Hs.
    - inversion_clear 1 as [? ? ? Hp|? ? ? ? Hp Hexp];
        destruct b; destruct (PS.mem i mems); try destruct b0;
          apply IHck with (1:=Hp); eauto.
    - inversion_clear 1 as [|? ? ? ? Hp Hexp]; intro Hs;
        destruct b; destruct (PS.mem i mems); try destruct b0;
          apply IHck with (1:=Hp); eauto.
  Qed.

  (** If the clock is absent, then the controlled statement evaluates as
  a [Skip].  *)

  Theorem stmt_eval_Control_absent:
    forall prog mems menv env ck stmt,
      Is_absent_in mems menv env ck
      -> stmt_eval prog menv env (Control mems ck stmt) (menv, env).
  Proof.
    apply stmt_eval_Control.
  Qed.

  (** If the clock is present, then the controlled statement evaluates
  as the underlying one.  *)

  Theorem stmt_eval_Control_present:
    forall prog mems menv env ck stmt menv' env',
      Is_present_in mems menv env ck
      -> stmt_eval prog menv env stmt (menv', env')
      -> stmt_eval prog menv env (Control mems ck stmt) (menv', env').
  Proof.
    apply stmt_eval_Control.
  Qed.

  (** ** More technical lemmas *)

  Lemma stmt_eval_translate_cexp_menv_inv:
    forall prog menv env mems x menv' env' ce,
      stmt_eval prog menv env (translate_cexp mems x ce) (menv', env')
      -> menv' = menv.
  Proof.
    intros until env'.
    induction ce;
      (apply IHce || inversion_clear 1; try destruct b); auto.
  Qed.

  Lemma stmt_eval_translate_cexp_env_add:
    forall prog menv env mems x menv' env' ce,
      stmt_eval prog menv env (translate_cexp mems x ce) (menv', env')
      -> exists c, env' = PM.add x c env.
  Proof.
    intros until env'.
    induction ce;
      (apply IHce || inversion_clear 1; try destruct b); auto;
      exists v; rewrite <- H1; intuition.
  Qed.

  Lemma not_Is_defined_in_eq_stmt_eval_menv_inv:
    forall prog x eq menv env mems menv' env',
      ~Is_defined_in_eq x eq
      -> stmt_eval prog menv env (translate_eqn mems eq) (menv', env')
      -> mfind_mem x menv' = mfind_mem x menv.
  Proof. (* TODO: Tidy proof *)
    intros ** Hneq Heval.
    destruct eq as [y ck ce | y ck f les | y ck v0 lae]; simpl in Heval.
    - apply stmt_eval_Control_fwd in Heval; destruct Heval as [Heval|Heval];
      destruct Heval as [Heval1 Heval2].
      apply stmt_eval_translate_cexp_menv_inv in Heval2.
      rewrite Heval2. intuition.
      destruct Heval2 as [Hmenv]; rewrite Hmenv; intuition.
    - simpl in Heval.
      apply stmt_eval_Control_fwd in Heval; destruct Heval as [Heval|Heval];
      destruct Heval as [Hipi Heval].
      inversion_clear Heval.
      rewrite <- H2.
      reflexivity.
      destruct Heval as [Hmenv Henv]; rewrite Hmenv; intuition.
    - apply not_Is_defined_in_eq_EqFby in Hneq.
      unfold translate_eqn in Heval.
      apply stmt_eval_Control_fwd in Heval; destruct Heval as [Heval|Heval];
      destruct Heval as [Hipi Heval].
      inversion_clear Heval.
      rewrite <- H0.
      unfold mfind_mem, madd_mem.
      simpl; rewrite PM.gso; [intuition | apply Hneq].
      destruct Heval as [Hmenv Henv]; rewrite Hmenv; intuition.
  Qed.

  Lemma not_Is_defined_in_eq_stmt_eval_mobj_inv:
    forall prog x eq menv env mems menv' env',
      ~ Is_defined_in_eq x eq
      -> (forall ck f les, eq <> EqApp [] ck f les)
      -> stmt_eval prog menv env (translate_eqn mems eq) (menv', env')
      -> mfind_inst x menv' = mfind_inst x menv.
  Proof. (* TODO: Tidy proof *)
    intros ** Hneq Hnemp Heval.
    destruct eq as [y ck ce | y ck f les | y ck v0 lae].
    - simpl in Heval.
      apply stmt_eval_Control_fwd in Heval; destruct Heval as [Heval|Heval];
      destruct Heval as [Heval1 Heval2].
      apply stmt_eval_translate_cexp_menv_inv in Heval2.
      rewrite Heval2. intuition.
      destruct Heval2 as [Hmenv]; rewrite Hmenv; intuition.
    - simpl in Heval.
      apply stmt_eval_Control_fwd in Heval; destruct Heval as [Heval|Heval];
      destruct Heval as [Hipi Heval].
      + inversion_clear Heval.
        rewrite <- H2.
        destruct (ident_eq_dec x (hd Ids.default y)) as [Hxy|Hxny].
        * exfalso.
          destruct y; simpl in *.
          eapply Hnemp; auto.
          rewrite Hxy in Hneq; apply Hneq; repeat constructor; auto.
        * now rewrite mfind_inst_gso.
      + destruct Heval as [HR1 HR2]; rewrite HR1; reflexivity.
    - unfold translate_eqn in Heval.
      apply stmt_eval_Control_fwd in Heval; destruct Heval as [Heval|Heval];
      destruct Heval as [Hipi Heval].
      inversion_clear Heval.
      rewrite <- H0.
      unfold mfind_inst, madd_mem.
      reflexivity.
      destruct Heval as [Hmenv Henv]; rewrite Hmenv; intuition.
  Qed.

  Lemma not_Is_variable_in_eq_stmt_eval_env_inv:
    forall prog x eq menv env mems menv' env',
      ~Is_variable_in_eq x eq
      -> stmt_eval prog menv env (translate_eqn mems eq) (menv', env')
      -> PM.find x env' = PM.find x env.
  Proof.
    intros ** Hnd Heval.
    destruct eq as [y ck ce | y ck f les | y ck v0 ce]; simpl in Heval.
    - apply stmt_eval_Control_fwd in Heval;
        destruct Heval as [[Hipi Heval]|[Habs [Hmenv Henv]]];
        [|rewrite Henv; reflexivity].
      apply stmt_eval_translate_cexp_env_add in Heval.
      destruct Heval; rewrite H; rewrite PM.gso;
      [reflexivity|intro HR; rewrite HR in *; apply Hnd; constructor].
    - apply stmt_eval_Control_fwd in Heval;
        destruct Heval as [Heval|Heval];
        destruct Heval as [Heval1 Heval2].
      2:now destruct Heval2; subst.
      inversion_clear Heval2.
      match goal with
      | H: adds _ _ _ = _ |- _ => rewrite <- H
      end.

      assert (~ In x y)
        by now (intro; eapply Hnd; constructor).

      now apply find_In_gsso.

    - apply stmt_eval_Control_fwd in Heval; destruct Heval as [Heval|Heval];
      destruct Heval as [Heval1 Heval2].
      inversion Heval2; intuition.
      destruct Heval2 as [Hmenv Henv]; rewrite Henv; intuition.
  Qed.

  Lemma not_Is_defined_in_eq_stmt_eval_env_inv:
    forall prog x eq menv env mems menv' env',
      ~Is_defined_in_eq x eq
      -> stmt_eval prog menv env (translate_eqn mems eq) (menv', env')
      -> PM.find x env' = PM.find x env.
  Proof.
    intros ** Hidi Hstmt.
    apply not_Is_defined_in_eq_not_Is_variable_in_eq in Hidi.
    now apply not_Is_variable_in_eq_stmt_eval_env_inv with (1:=Hidi) (2:=Hstmt).
  Qed.

  Lemma stmt_eval_translate_eqns_menv_inv:
    forall prog menv env mems eqs menv' env',
      stmt_eval prog menv env (translate_eqns mems eqs) (menv', env')
      -> (forall x, ~ Is_defined_in_eqs x eqs ->
              mfind_mem x menv' = mfind_mem x menv).
  Proof.
    induction eqs as [ |eq].
    + inversion_clear 1; reflexivity.
    + intros menv' env' Heval x Hnmem.
      apply not_Is_defined_in_cons in Hnmem.
      destruct Hnmem as [H0 H1].
      apply stmt_eval_translate_eqns_cons in Heval.
      destruct Heval as [menv'' [env'' [Heval0 Heval1]]].
      apply IHeqs with (x:=x) (2:=H1) in Heval0.
      apply not_Is_defined_in_eq_stmt_eval_menv_inv with (1:=H0) in Heval1.
      rewrite Heval1, Heval0.
      reflexivity.
  Qed.

  Lemma stmt_eval_translate_eqns_minst_inv:
    forall prog menv env mems eqs menv' env',
      stmt_eval prog menv env (translate_eqns mems eqs) (menv', env')
      -> (forall x, ~ Is_defined_in_eqs x eqs ->
              (forall ck f les,
                  ~ In (EqApp [] ck f les) eqs) ->
              mfind_inst x menv' = mfind_inst x menv).
  Proof.
    induction eqs as [ |eq].
    + inversion_clear 1; reflexivity.
    + intros menv' env' Heval x Hnmem Hndef.
      apply not_Is_defined_in_cons in Hnmem as [H0 H1].

      assert (forall ck f les, ~ In (EqApp [] ck f les) eqs)
        by now intros ** Hdef; eapply Hndef; constructor(apply Hdef).

      assert (forall ck f les, eq <> EqApp [] ck f les)
        by now intros ** -> ; eapply Hndef; constructor(now eauto).

      apply stmt_eval_translate_eqns_cons in Heval
        as [menv'' [env'' [Heval0 Heval1]]].
      eapply IHeqs in Heval0; eauto.
      eapply not_Is_defined_in_eq_stmt_eval_mobj_inv in Heval1; eauto.
      rewrite Heval1, Heval0.
      reflexivity.
  Qed.

  Lemma stmt_eval_translate_eqns_env_inv:
    forall prog menv env mems eqs menv' env',
      stmt_eval prog menv env (translate_eqns mems eqs) (menv', env')
      -> (forall x, ~Is_variable_in_eqs x eqs ->
              PM.find x env' = PM.find x env).
  Proof.
    induction eqs as [ |eq].
    + inversion_clear 1; reflexivity.
    + intros menv' env' Heval x Hndef.
      apply not_Is_variable_in_cons in Hndef.
      destruct Hndef as [H0 H1].
      apply stmt_eval_translate_eqns_cons in Heval.
      destruct Heval as [menv'' [env'' [Heval0 Heval1]]].
      apply IHeqs with (x:=x) (2:=H1) in Heval0.
      apply not_Is_variable_in_eq_stmt_eval_env_inv with (1:=H0) in Heval1.
      rewrite Heval1, Heval0.
      reflexivity.
  Qed.

  Local Ltac split_env_assumption :=
    match goal with
    | Henv: context Is_free_in_lexp [_], Hsem: sem_var_instant _ ?y _
      |- _ => apply Henv in Hsem; [destruct Hsem |solve [auto]]; clear Henv
    | Henv: context Is_free_in_clock [_], Hsem: sem_var_instant _ ?y _
      |- _ => apply Henv in Hsem; [destruct Hsem |solve [auto]]; clear Henv
    end.

  (** ** Correctness of expression's translation *)

  (**

An imperative stack [env] and an imperative memory [menv] are faithful
to a dataflow environment [R] over a set of identifiers [Is_free] if
their values agree with the dataflow environment.

   *)

  Definition equiv_env (Is_free: ident -> Prop) R memories env menv :=
    forall x c, Is_free x
           -> sem_var_instant R x (present c)
           -> (~PS.In x memories -> PM.find x env = Some c)
             /\ (PS.In x memories -> mfind_mem x menv = Some c).
  Hint Unfold equiv_env.

  (** We often need to weaken an equivalence to a subterm: for example we
know that the environments are equivalent for all [Is_free_caexp x
(AnnExp e ck)], we can deduce that the environements are equivalent
for all [Is_free_exp x e]. *)
  Lemma equiv_env_map (Is_free1 Is_free2: ident -> Prop) H memories env menv:
    (forall x, Is_free2 x -> Is_free1 x) ->
    equiv_env Is_free1 H memories env menv ->
    equiv_env Is_free2 H memories env menv.
  Proof.
    intros Hinv Hequiv1 x **; auto.
  Qed.

  Ltac weaken_equiv_env :=
    match goal with
    | [H: equiv_env ?is_free1 ?R ?mems ?env ?menv
       |- equiv_env ?is_free2 ?R ?mems ?env ?menv] =>
      eapply equiv_env_map; [|exact H]; constructor(auto)
    end.


  (** *** Correctness of clock's translation *)

  Lemma get_exp_eval_tovar:
    forall x ty mems menv env v,
      (~ PS.In x mems -> PM.find x env = Some v)
      -> (PS.In x mems -> mfind_mem x menv = Some v)
      -> exp_eval menv env (tovar mems (x, ty)) v.
  Proof.
    intros x ty mems menv env v Hvar Hmem.
    unfold tovar.
    destruct (In_dec x mems) as [Hin|Hnin].
    - specialize (Hmem Hin).
      apply PS.mem_spec in Hin; rewrite Hin.
      constructor; exact Hmem.
    - specialize (Hvar Hnin).
      apply mem_spec_false in Hnin; rewrite Hnin.
      constructor; exact Hvar.
  Qed.

  Theorem clock_correct_true:
    forall base R mems menv env ck,
      equiv_env (fun x => Is_free_in_clock x ck) R mems env menv
      -> sem_clock_instant base R ck true
      -> Is_present_in mems menv env ck.
  Proof.
    Hint Constructors Is_present_in.
    Hint Constructors sem_clock_instant.
    Hint Constructors Is_free_in_clock.
    Hint Constructors exp_eval.
    intros until env.
    induction ck as [|? ? x]; [ intuition | ].
    intro Henv.
    inversion 1; subst.
    econstructor; try eassumption.
    - apply IHck; [now weaken_equiv_env|assumption].
    - split_env_assumption.
      apply exp_eval_tovar.
      destruct In_dec with x mems; intuition.
  Qed.

  Theorem clock_correct_false:
    forall R mems menv env ck,
      equiv_env (fun x => Is_free_in_clock x ck) R mems env menv
      -> sem_clock_instant true R ck false
      -> Is_absent_in mems menv env ck.
  Proof.
    Hint Constructors Is_absent_in sem_clock_instant Is_free_in_clock exp_eval.
    intros until env.
    induction ck as [|? ? x]; [ now inversion 2 | ].
    intro Henv.
    inversion_clear 1.
    - constructor. apply IHck; auto.
    - destruct b0; [apply val_to_bool_true' in H2
                   |apply val_to_bool_false' in H2]; subst;
        eapply IsAbs2;
        try eapply clock_correct_true with (2:=H0);
        try apply val_to_bool_true;
        try apply val_to_bool_false;
        auto;
        split_env_assumption;
        destruct In_dec with x mems as [Hin|Hin];
        match goal with
        | H:~PS.In _ _ -> _, Hin:~PS.In _ _ |- _ => specialize (H Hin)
        | H:PS.In _ _ -> _, Hin:PS.In _ _ |- _ => specialize (H Hin)
        end;
        apply PS.mem_spec in Hin || apply mem_spec_false in Hin;
        unfold tovar; rewrite Hin; intuition.
  Qed.

  (** *** Correctness of [translate_lexp] *)

  Theorem typ_correct:
    forall mems e,
      typeof (translate_lexp mems e) = DF.Syn.typeof e.
  Proof.
    induction e as [|y ty| | |]; simpl; auto.
    destruct (PS.mem y mems); simpl; auto.
  Qed.

  Theorem lexp_correct:
    forall R mems menv env c e,
      sem_lexp_instant true R e (present c)
      -> equiv_env (fun x => Is_free_in_lexp x e) R mems env menv
      -> exp_eval menv env (translate_lexp mems e) c.
  Proof.
    Hint Constructors exp_eval.
    intros until e. revert c.
    (* XXX: Tidy up this proof *)
    induction e as [c0|y ty|e IH y yb|op le IHle ty|op le1 IHle1 le2 IHle2 ty];
      intro c; inversion 1 as [c' v Hp H'|x v ty' H'|s x b v ty' H' H''|
                      | |le' op' c' ty' H'| |le1' le2' op' c1 c2 ty' H' H''|];
        try (subst; injection H'); intros; subst;
          try apply IH; try apply econst; auto.
    - simpl. injection Hp. intro; subst. constructor.
    - split_env_assumption;
      unfold translate_lexp;
      destruct (PS.mem y mems) eqn:Hm;
      simpl; rewrite Hm.
      + auto.
      + rewrite mem_spec_false in Hm; auto.
    - simpl. apply eunop with c'.
      + apply IHle; auto.
      + now rewrite typ_correct.
    - simpl. apply ebinop with (c1 := c1) (c2 := c2).
      + apply IHle1; auto.
      + apply IHle2; auto.
      + now rewrite 2 typ_correct.
  Qed.

  Theorem lexps_correct:
    forall R mems menv env cs es,
      let vs := map present cs in
      Forall2 (fun e v => sem_lexp_instant true R e v) es vs
      -> equiv_env (fun x => Exists (Is_free_in_lexp x) es) R mems env menv
      -> Forall2 (exp_eval menv env) (map (translate_lexp mems) es) cs.
  Proof.
    Hint Constructors Forall2.
    intros until cs.
    induction cs; intros es Hvs Hsem Hequiv; subst Hvs.
    now inv Hsem; constructor.
    inv Hsem. constructor.
    - now eapply lexp_correct; eauto.
    - apply IHcs; trivial.
      repeat intro. apply Hequiv; trivial. now constructor(assumption).
  Qed.

  (** *** Correctness of [translate_cexp] *)

  Theorem cexp_correct:
    forall R mems prog menv env c x e,
      sem_cexp_instant true R e (present c)
      -> equiv_env (fun x => Is_free_in_cexp x e) R mems env menv
      -> stmt_eval prog menv env (translate_cexp mems x e)
                  (menv, PM.add x c env).
  Proof.
    intros until x.
    induction e as [y et IHt ef IHf|y t IHt f IHf|e].
    - (* Emerge *)
      inversion_clear 1; intro Henv.
      + apply IHt in H1; [|auto].
        simpl.
        eapply Iifte; [|now apply val_to_bool_true'|assumption].
        split_env_assumption. apply get_exp_eval_tovar; auto.
      + apply IHf in H2; [|auto].
        eapply Iifte; [|now apply val_to_bool_false'|assumption].
        split_env_assumption. apply get_exp_eval_tovar; auto.
    - (* Eite *)
      intro HH; inv HH; intro Henv.
      simpl; econstructor; [|eassumption|].
      eapply lexp_correct; now eauto.
      destruct b;
        match goal with H:present _ = present _ |- _ => injection H end;
        intro; subst; [apply IHt|apply IHf]; eauto.
    - (* Eexp *)
      inversion_clear 1; intro Henv.
      unfold translate_cexp.
      econstructor.
      eapply lexp_correct; [eassumption|now auto].
      reflexivity.
  Qed.

  (* Notes:
   1. The assumption sem_equations must be shown for a set of equations.
      TODO: lemma showing that a well-typed and well-clocked set of
            equations has a semantics.

   2. The assumption stmt_eval (translate_eqns mems vars eqs) implies that an
      execution exists and thus that exp_eval's evar and estate find some
      value for each required variable.
      This is somehow backwards; it should be an obligation to show that
      an execution exists. This is something assured indirectly in the
      lemma below where we require not just that evar and estate find
      some value, but also that it is the correct value.
   *)


  Lemma Is_memory_in_msem_var:
    forall G bk H M n x eqs c,
      Is_defined_in_eqs x eqs
      -> ~Is_variable_in_eqs x eqs
      -> sem_var_instant (restr H n) x (present c)
      -> List.Forall (msem_equation G bk H M) eqs
      -> (exists ms, mfind_mem x M = Some ms /\ ms n = c).
  Proof.
    induction eqs as [|eq eqs IH];
    inversion_clear 1 as [? ? Hidi|? ? Hidi];
    intros Hnvi Hsv Hmsem;
    apply Forall_cons2 in Hmsem;
    apply not_Is_variable_in_cons in Hnvi;
    destruct Hnvi as [Hnvi0 Hnvi1];
    destruct Hmsem as [Hmeq Hmeqs].
    - destruct eq; inversion Hidi; subst;
      try (exfalso; apply Hnvi0; now constructor).
      inversion_clear Hmeq
        as [| |? ? ? ? ? ? ls ? ? ? Hmfind Hms0 Hsemls HxS Hmls].
      exists ms.
      split; [apply Hmfind|].
      specialize Hmls with n; specialize (HxS n); simpl in HxS.
      destruct (ls n);
        destruct Hmls as [Hms Hsv'].
      rewrite Hsv' in HxS.
      + assert (present c = absent) by sem_det; discriminate.
      + cut (present (ms n) = present c); [injection 1; auto|].
        rewrite Hsv' in HxS.
        sem_det.
    - apply IH; assumption.
  Qed.

  (** *** Correctness of [translate_eqns] *)

  Definition equiv_node G prog f :=
    forall n xss yss M menv inputs outputs,
      Memory_Corres G n f M menv
      -> msem_node G f xss M yss
      -> xss n = map present inputs
      -> yss n = map present outputs
      -> exists menv',
          stmt_call_eval prog menv f step inputs menv' outputs
          /\  Memory_Corres G (S n) f M menv'.

  Definition equiv_prog G prog :=
    forall f,
      equiv_node G prog f.

  Section IsStepCorrect.

    Variables (G: global)
              (HG: Welldef_global G)
              (bk: stream bool)
              (H: history)
              (M: memory)
              (mems: PS.t)
              (alleqs : list equation)
              (Hsems: msem_equations G bk H M alleqs)
              (prog: program)
              (Hnode: equiv_prog G prog)
              (inputs: list ident)
              (Hinput: forall input, In input inputs -> ~ PS.In input mems)
              (n: nat)
              (Hbase: bk n = true)
              (menv: heap)
              (env: stack).

    (* TODO: Can we replace
    (forall x, PS.In x mems ->
		(Is_defined_in x alleqs /\ ~Is_variable_in x alleqs)) ->
  and
    ~PS.In input mems ->

  with a simply definition of mems in terms of alleqs and one or two
  auxilliary lemmas? *)

    Lemma is_step_correct:
      forall (eqs: list equation),
        (exists oeqs, alleqs = oeqs ++ eqs)
        -> (forall x, PS.In x mems
                -> (Is_defined_in_eqs x alleqs
                   /\ ~Is_variable_in_eqs x alleqs))

        (* - input (assumed) *)
        -> (forall c input, In input inputs ->
                      (sem_var_instant (restr H n) input (present c)
                       <-> PM.find input env = Some c))
        (* NB: PM.find x env' = Some c -> sem_var H x n (present c)
                 does not hold if PM.find x env = Some arbitrary_c, since
                 x will not be written to when its clock is absent.

                 It may just be better to show the direction:
                 sem_var H x n (present c) -> PM.find x env' = Some c

                 which is enough if the outputs are only sampled when
                 they are present (normally the case).

                 More discussion/context is needed. *)
        -> (forall x, Is_variable_in_eqs x eqs -> PM.find x env = None)
        -> (forall input, In input inputs -> ~ Is_defined_in_eqs input eqs)

        (* - execution of translated equations *)
        -> Is_well_sch mems inputs eqs

        (* - unwritten memories (assumed) *)
        -> List.Forall (Memory_Corres_eq G n M menv) alleqs

        (* - locals (shown) *)
        -> (exists menv' env',
              stmt_eval prog menv env (translate_eqns mems eqs) (menv', env')
              /\ (forall x, Is_variable_in_eqs x eqs
                  -> forall c : val, sem_var_instant (restr H n) x (present c)
                               <-> PM.find x env' = Some c)
              (* - written memories (shown) *)
              /\ List.Forall (Memory_Corres_eq G (S n) M menv') eqs).
    Proof.
      (* Induction on equations: translate_eqns [] = Skip *)
      induction eqs as [|eq];
      [ intros; exists menv, env;
        split; [unfold translate_eqns; constructor|];
        split; intros; [ match goal with
                         | H:Is_variable_in_eqs _ nil |- _ => inversion H
                         end | now constructor ]| ].
      intros Hall Hinmems Hin Henv Hin2 Hwsch Hmc.

      assert (exists menv' env',
               stmt_eval prog menv env (translate_eqns mems eqs) (menv', env')
               /\ (forall x, Is_variable_in_eqs x eqs
                       -> forall c, sem_var_instant (restr H n) x (present c)
                              <-> PM.find x env' = Some c)
               /\ List.Forall (Memory_Corres_eq G (S n) M menv') eqs) as IHeqs'.
      { eapply IHeqs; trivial.
        - apply List_shift_away with (1:=Hall).
        - intros; apply Henv; constructor(assumption).
        - intros; eapply not_Is_defined_in_cons; eauto.
        - eapply Is_well_sch_cons; eauto.
      }

      clear IHeqs.
      destruct IHeqs' as [menv' [env' [Hstmt [IHeqs0 IHeqs1]]]].

      destruct Hall as [oeqs Hall].
      assert (Hsems' := Hsems); rewrite Hall in Hsems'.

      apply Forall_app in Hsems'.
      destruct Hsems' as [H0 Hsems']; clear H0.
      apply Forall_cons2 in Hsems'.
      destruct Hsems' as [Hsem Hsems'].
      inversion Hsem as
          [bk0 H0 M0 i ck xs ce Hvar Hce HR1 HR2 HR3
          |bk0 H0 M0 y ys ck f Mo les ls xs Hsome Hmfind Hlaes Hvar Hmsem HR1 HR2 HR3
          |bk0 H0 M0 ms y ck ls yS v0 le Hmfind Hms0 Hlae HyS Hvar HR1 HR2 HR3];
        subst bk0 H0 M0 eq;
        (*    (rewrite <-HR3 in *; clear HR1 HR2 HR3 H0 M0); *)
        specialize (Hvar n).
      - (* Case EqDef: y = cae *)
        exists menv'. (* the memory does not change *)

        specialize (Hce n); simpl in *.
        assert (equiv_env (fun x => Is_free_in_caexp x ck ce)
                          (restr H n) mems env' menv')
          as Hce'.
        {
          Hint Constructors Is_free_in_eq.
          intros.
          split; intro Hmems.

          - assert (Hdecide_x: Is_variable_in_eqs x eqs \/ In x inputs)
              by (eapply Is_well_sch_free_variable; eauto).

            destruct Hdecide_x; try subst x.
            + apply IHeqs0; assumption.
            + erewrite stmt_eval_translate_eqns_env_inv; try eassumption.
              now apply Hin.
              apply not_Is_defined_in_not_Is_variable_in.
              intro Hnot_def. eapply Hin2; try eauto.
              constructor(assumption).

          - assert (~ Is_defined_in_eqs x eqs)
              by (eapply Is_well_sch_free_variable_in_mems; eauto).

            specialize (Hinmems _ Hmems); destruct Hinmems.
            erewrite stmt_eval_translate_eqns_menv_inv; try eassumption.
            eapply Is_memory_in_msem_var in H1; try eassumption.
            do 2 destruct H1; subst c.
            assert (Is_defined_in_eqs x alleqs) by intuition.
            assert (~ Is_variable_in_eqs x alleqs) by intuition.
            erewrite Is_memory_in_Memory_Corres_eqs; try eauto.
        }

        inversion Hce; subst ck0 ce0;
        match goal with
        | H: present _ = xs n |- _ => rewrite <- H in *
        | H: absent = xs n |- _ => rewrite <- H in *
        end.

        + (* xs n = present *)
          rename c into v.
          exists (PM.add i v env').
          split; [|split].
          * apply stmt_eval_translate_eqns_cons.
            exists menv', env'.
            split; [exact Hstmt|].
            apply stmt_eval_Control_present.
            eapply clock_correct_true; now eauto.
            rewrite Hbase in *.
            eapply cexp_correct; now eauto.
          * intros x0 Hivi c.
            inversion_clear Hivi as [? ? Hivi'|]; [inversion_clear Hivi'|].
            { rewrite PM.gss; split; intro HH.
              - assert (c = v) by
                    (cut (present c = present v); [injection 1; auto|];
                     sem_det).
                congruence.
              - injection HH; intro Heq. subst. assumption. }
            { destruct (ident_eq_dec x0 i) as [Hxy|Hnxy].
              - rewrite Hxy in *; clear Hxy.
                rewrite PM.gss.
                split; intro Hsv'.
                * assert (v = c)
                    by (cut (present v = present c); [injection 1; auto|]; sem_det).
                  congruence.
                * injection Hsv'; congruence.
              - erewrite PM.gso; try eassumption.
                apply IHeqs0; assumption.
            }
          * rewrite Hall in Hmc.
            apply Forall_app in Hmc; destruct Hmc as [Hmc0 Hmc]; clear Hmc0.
            apply Forall_cons2 in Hmc; destruct Hmc as [Hmc Hmc0]; clear Hmc0.
            inversion_clear Hmc.
            repeat constructor; assumption.

        + (* xs n = absent *)
          exists env'.
          split; [|split].
          * apply stmt_eval_translate_eqns_cons.
            exists menv', env'.
            split; [exact Hstmt|].
            rewrite Hbase in *.
            apply stmt_eval_Control_absent; auto.
            eapply clock_correct_false; eauto.
          * intros x0 Hivi c.
            (* TODO: do we really need this [destruct]? It seems that we *know*
                     that it cannot be a variable (proof by
                     [contradiction]/[discriminate]). If not, remove dependency
                     on [NLustre.IsVariable.Decide] *)
            destruct (Is_variable_in_dec x0 eqs) as [Hvin|Hvin];
              [now apply IHeqs0 with (1:=Hvin)|].
            apply stmt_eval_translate_eqns_env_inv with (2:=Hvin) in Hstmt.
            rewrite Hstmt.
            inversion_clear Hivi as [? ? Hivi'|];
              [|unfold Is_variable_in_eqs in Hvin; contradiction].
            inversion_clear Hivi'.
            split; intro Hsv'.
            assert (present c = absent) by sem_det. discriminate.
            assert (PM.find i env = None).
            apply Henv; now repeat constructor.
            rewrite Hsv' in *; discriminate.
          * rewrite Hall in Hmc.
            apply Forall_app in Hmc; destruct Hmc as [Hmc0 Hmc]; clear Hmc0.
            apply Forall_cons2 in Hmc; destruct Hmc as [Hmc Hmc0]; clear Hmc0.
            inversion_clear Hmc.
            repeat constructor; assumption.

      - (* Case EqApp: y = f lae *)

        (* used variables are defined *)
        assert (equiv_env (fun x => Is_free_in_laexps x ck les)
                          (restr H n) mems env' menv')
          as Hlae'. {
          intros.
          split; intro Hmems.

          - assert (Hdecide_x: Is_variable_in_eqs x eqs \/ In x inputs)
              by (eapply Is_well_sch_free_variable;
                   eassumption || constructor (assumption)).

            destruct Hdecide_x; try subst x.
            + apply IHeqs0; assumption.
            + erewrite stmt_eval_translate_eqns_env_inv; try eassumption.
              apply Hin; now eauto.
              apply not_Is_defined_in_not_Is_variable_in.
              intro Hnot_def. eapply Hin2; eauto.
              econstructor(eassumption).

          - assert (~ Is_defined_in_eqs x eqs)
              by (eapply Is_well_sch_free_variable_in_mems;
                   eassumption || constructor (assumption)).
            specialize (Hinmems _ Hmems); destruct Hinmems.
            erewrite stmt_eval_translate_eqns_menv_inv; try eassumption.
            eapply Is_memory_in_msem_var in H1; try eassumption.
            do 2 destruct H1; subst c.
            assert (Is_defined_in_eqs x alleqs) by intuition.
            assert (~ Is_variable_in_eqs x alleqs) by intuition.
            erewrite Is_memory_in_Memory_Corres_eqs; try eauto.
        }

        (* memory correspondence before execution *)
        assert (  Forall (Memory_Corres_eq G n M menv) oeqs
                /\ Memory_Corres_eq G n M menv (EqApp ys ck f les)
                /\ Forall (Memory_Corres_eq G n M menv) eqs)
          as (_ & Hmceq & Hmceqs)
            by now (rewrite <- Forall_cons2; apply Forall_app; rewrite <- Hall).
        clear Hmc.

        inversion_clear Hmceq as [|? ? ? ? ? ? ? Hsome' Hmc0|].

        assert (Hsomexy: Some x = Some y)
          by congruence.
        injection Hsomexy; intro; subst x; clear Hsomexy.

        edestruct Hmc0 as [omenv [Hfindo Hmc0']]; eauto.
        (* dataflow semantics *)
        assert (Hmsem':=Hmsem).
        inversion_clear Hmsem'
          as [? ? ? ? ? i o v neqs
                ingt0 outgt0 defd vout nodup good Hck Hfind Hnsem].
        destruct Hnsem as (Hn & Hlsn & Hxsn & Hsamexs & Hsameys & Hout & Hnsem).

        (* no other instance *)
        assert (~Is_defined_in_eqs y eqs) as Hniii.
        {
          assert (In y ys).
          {
            destruct ys; simpl in *; try discriminate.
            injection Hsome. now auto.
          }

          assert (Is_defined_in_eq y (EqApp ys ck f les))
            by now constructor.

          now inversion_clear Hwsch; eauto.
        }

        specialize (Hlaes n);
          specialize (Hxsn n);
          specialize (Hout n);
          simpl in *.

        inversion_clear Hlaes as [? ? ? ? Hlsp|].
        + (* y = present *)
          rename cs into inValues.
          assert (exists cs, xs n = map present cs)
            as (outValues & Hxsc).
          {
            assert (Hlen: (0 < length (ls n))%nat)
              by now (eapply sem_vars_gt0; [apply ingt0| eauto]).

            assert (~ absent_list (xs n)).
            {
              intro Habs.
              rewrite <- Hout in Habs.
              unfold absent_list in Habs.
              destruct (ls n); try now inv Hlen.
              destruct inValues; try discriminate.
              rewrite Hlsp in Habs.
              now inv Habs; destruct inValues; discriminate.
            }

            assert (present_list (xs n))
              by now apply present_not_absent_list; eauto.

            now apply present_list_spec.
          }
          rewrite Hxsc in *.

          assert (exists menv' : heap,
                     stmt_call_eval prog omenv f step inValues menv' outValues
                     /\ Memory_Corres G (S n) f Mo menv') as Hclass
              by (eapply Hnode; eauto).
          destruct Hclass as (omenv' & Hnstmt & Hnmc).

          simpl in *.
          exists (madd_obj y omenv' menv'), (adds ys outValues env').
          split;[|split].
          * apply stmt_eval_translate_eqns_cons.
            exists menv', env'.
            split; [exact Hstmt|].
            apply stmt_eval_Control_present.
            eapply clock_correct_true; now eauto.

            assert (equiv_env (fun x : ident => Exists (Is_free_in_lexp x) les)
                              (restr H n) mems env' menv')
              by weaken_equiv_env.

            assert (Forall2 (exp_eval menv' env')
                            (map (translate_lexp mems) les) inValues).
            {
              rewrite Hbase in *.
              eapply lexps_correct; eauto.
              match goal with
              | H: _ = map present inValues |- _ => rewrite <- H
              | H: map present inValues = _ |- _ => rewrite H
              end. eauto.
            }
            assert (Hhd: hd Ids.default ys = y).
            {
              unfold hd_error in Hsome'.
              destruct ys; try discriminate; simpl.
              now injection Hsome'.
            } rewrite Hhd; clear Hhd.

            assert (forall ck f les, ~ In (EqApp [] ck f les) eqs)
              by now eapply non_trivial_EqApp; eauto.

            Hint Constructors stmt_eval.
            erewrite <-stmt_eval_translate_eqns_minst_inv in Hfindo; eauto.
            econstructor; eauto. now rewrite Hfindo.

          * {
              intros x Hivi c.
              apply Is_variable_in_cons in Hivi.
              destruct Hivi as [Hivi | [notxy Hivi] ].
              - (* In x ys *)
                inversion_clear Hivi.
                clear - Hxsn H2 outgt0 Hvar.
                (* XXX: this should be an independant lemma *)
                generalize dependent outValues.
                generalize dependent o.
                induction ys; simpl in *; try contradiction.
                intros o outgt0 outValues Hvar Hxsn.

                assert (exists outValue outValues',
                           outValues = outValue :: outValues')
                  as (outValue & outValues' & HoutValues).
                {
                  destruct outValues.
                  - now (destruct o; [inv outgt0 | inv Hxsn ]).
                  - now eauto.
                }
                subst outValues.

                destruct (ident_eqb a x) eqn:Hax.
                + (* Case: x = a *)
                  apply ident_eqb_eq in Hax. subst a.

                  assert (sem_var_instant (restr H n) x (present outValue))
                    by now inv Hvar.

                  rewrite find_gsss.
                  split; intro HH.
                  * assert (present c = present outValue) by sem_det.
                    congruence.
                  * now injection HH; intro Heq; rewrite <-Heq.
                + (* In x ys *)
                  apply ident_eqb_neq in Hax.
                  destruct H2; [ now contradiction | ]; simpl in *.
                  rewrite find_gsso; [| now congruence].

                  destruct outValues' eqn:HoutValues'; simpl in *.
                  * exfalso.
                    inv Hvar. inv H6. inv H0.
                  * assert (Forall2 (sem_var_instant (restr H n)) ys (map present outValues'))
                      by now inv Hvar.

                    destruct o; simpl in *. inv outgt0.
                    destruct o eqn:Ho; simpl in *.
                    1: exfalso; inv Hxsn; inv H7.

                    assert (Forall2 (sem_var_instant (restr Hn n)) (map fst o) (map present outValues'))
                      by now inv Hxsn.

                    assert (0 < length o)%nat
                      by (subst o; simpl; apply Lt.lt_0_Sn).

                    now eapply IHys; subst o outValues'; eauto.

              - (* ~ In x ys *)
                assert (~ In x ys) by now (not_Is_variable x ys).
                now rewrite find_In_gsso; auto.
            }
          * apply Forall_cons.
            2:now apply Memory_Corres_eqs_add_obj with (1:=IHeqs1) (2:=Hniii).
            econstructor; eauto.
            intros Mo' Hmfind'.
            rewrite Hmfind in Hmfind'.
            injection Hmfind'; intro Heq; rewrite <-Heq in *; clear Heq Hmfind'.
            exists omenv'.
            split; [rewrite mfind_inst_gss; reflexivity|exact Hnmc].

        + (* y = absent *)
          exists menv', env'.

          assert (Habs: absent_list (ls n) ->
                        Forall (rhs_absent_instant (bk0 n) (restr Hn n)) neqs)
            by now eapply subrate_property_eqns; eauto;
                   eapply sem_vars_gt0 with (1:=ingt0) (2:=Hlsn).

          assert (absent_list (ls n)).
          {
            rewrite H0; clear.
            (* XXX: standalone lemma *)
            induction les; constructor(auto).
          }

          assert (absent_list (xs n)) as Hout'
              by now apply Hout.

          split; [|split].
          * apply stmt_eval_translate_eqns_cons.
            exists menv', env'.
            split; [exact Hstmt|].
            rewrite Hbase in *.
            apply stmt_eval_Control_absent.
            eapply clock_correct_false; eauto.
          * intros x Hivi c.
            destruct (Is_variable_in_dec x eqs) as [Hvin|Hvin];
              [now apply IHeqs0 with (1:=Hvin)|].
            apply stmt_eval_translate_eqns_env_inv with (2:=Hvin) in Hstmt.
            rewrite Hstmt.
            inversion_clear Hivi as [? ? Hivi'|];
              [|unfold Is_variable_in_eqs in Hvin; contradiction].

            assert (Hfind': PM.find x env = None)
              by (apply Henv; constructor(auto)).

            rewrite Hfind'; split; intro Hsv; try discriminate.

            exfalso.

            assert (Hsv': Forall2 (sem_var_instant (restr H n)) ys (map (fun _ => absent) (xs n)))
              by now apply absent_list_spec in Hout'; rewrite <- Hout'.

            assert (Hinx: In x ys)
              by now inversion_clear Hivi'.

            clear - Hsv' Hinx Hfind' Hsv.
            {
              (* XXX: Refactor as standalone Lemma *)
              remember (xs n) as xsn.
              clear Heqxsn.
              generalize dependent xsn.
              induction ys; intros xsn Hsv'; try inversion_clear Hinx.
              - subst a.
                destruct xsn; [ now inv Hsv' | ].
                simpl in *. inv Hsv'.
                assert (absent = present c) by sem_det.
                discriminate.
              - destruct xsn as [|v xsn]; [ now inv Hsv' | ].
                assert (Forall2 (sem_var_instant (restr H n)) ys (map (fun _ => absent) xsn))
                  by now inv Hsv'.
                eapply IHys; eauto.
            }

          * apply Forall_cons; [|now apply IHeqs1].
            econstructor; eauto.
            intros Mo' Hmfind'.
            rewrite Hmfind in Hmfind'.
            injection Hmfind'; intro He; rewrite <-He in *; clear He Hmfind'.
            exists omenv.

            assert (forall ck f les, ~ In (EqApp [] ck f les) eqs)
              by now eapply non_trivial_EqApp; eauto.

            erewrite stmt_eval_translate_eqns_minst_inv; eauto.
            split; eauto.
            now eapply Memory_Corres_unchanged; eauto.

      - (* Case EqFby: y = v0 fby lae *)
        specialize (Hlae n).
        assert (equiv_env (fun x => Is_free_in_laexp x ck le)
                          (restr H n) mems env' menv')
          as Hlae'.
        {
          intros.
          split; intro Hmems.

          - assert (Hdecide_x: Is_variable_in_eqs x eqs \/ In x inputs)
              by (eapply Is_well_sch_free_variable;
                   eassumption || constructor (assumption)).

            destruct Hdecide_x; try subst x.
            + apply IHeqs0; assumption.
            + erewrite stmt_eval_translate_eqns_env_inv; try eassumption.
              apply Hin; now eauto.
              apply not_Is_defined_in_not_Is_variable_in.
              intro. eapply Hin2; eauto. econstructor(eassumption).

          - assert (~ Is_defined_in_eqs x eqs)
              by (eapply Is_well_sch_free_variable_in_mems;
                   eassumption || constructor (assumption)).
            specialize (Hinmems _ Hmems); destruct Hinmems.
            erewrite stmt_eval_translate_eqns_menv_inv; try eassumption.
            eapply Is_memory_in_msem_var in H1; try eassumption.
            do 2 destruct H1; subst c.
            assert (Is_defined_in_eqs x alleqs) by intuition.
            assert (~ Is_variable_in_eqs x alleqs) by intuition.
            erewrite Is_memory_in_Memory_Corres_eqs; try eauto.
        }

        inversion Hlae; subst ck0 ce;
        match goal with
        | H: present _ = ls n |- _ => rewrite <- H in *
        | H: absent = ls n |- _ => rewrite <- H in *
        end;
        destruct Hvar as [Hms Hvar].
        + (* y = present *)
          rename c into v.
          exists (madd_mem y v menv'), env'.
          split; [|split].
          * apply stmt_eval_translate_eqns_cons.
            exists menv', env'.
            split; [exact Hstmt|].
            apply stmt_eval_Control_present.
            eapply clock_correct_true; now eauto.
            econstructor.
            rewrite Hbase in *.
            eapply lexp_correct; now eauto.
            reflexivity.
          * intros x Hivi c.
            inversion_clear Hivi as [? ? Hivi'|]; [now inversion_clear Hivi'|].
            apply IHeqs0.
            assumption.
          * rewrite <-Hms.
            apply Forall_cons.
            2:now apply Memory_Corres_eqs_add_mem with (1:=Hmfind) (2:=IHeqs1).
            constructor.
            intros ms' Hmfind'.
            rewrite Hmfind in Hmfind'.
            injection Hmfind'; intro Heq; rewrite <-Heq in *; clear Hmfind' Heq.
            now apply mfind_mem_gss.
        + (* y = absent *)
          exists menv', env'.
          split; [|split].
          * apply stmt_eval_translate_eqns_cons.
            exists menv', env'.
            split; [exact Hstmt|].
            rewrite Hbase in *;
              apply stmt_eval_Control_absent.
            eapply clock_correct_false; eauto.
          * intros x Hivi c.
            destruct (Is_variable_in_dec x eqs) as [Hvin|Hvin];
              [now apply IHeqs0 with (1:=Hvin)|].
            apply stmt_eval_translate_eqns_env_inv with (2:=Hvin) in Hstmt.
            rewrite Hstmt.
            inversion_clear Hivi as [? ? Hivi'|];
              [|unfold Is_variable_in_eqs in Hvin; contradiction].
            inversion_clear Hivi'.
          * {
              constructor.
              2:assumption.
              constructor.
              intros ms0' Hmfind'.
              rewrite Hmfind in Hmfind'.
              injection Hmfind'; intro Heq; rewrite <-Heq in *;
                clear Heq Hmfind'.
              (* TODO: do we really need this? We seem to *know* that it
        cannot be equal ([exfalso] branch). If unnecessary, remove the
        import on NLustre.IsDefined.Decide *)

              destruct (Is_defined_in_dec y eqs) as [Hxin|Hxin].
              - Hint Constructors Is_defined_in_eq.
                exfalso.
                inversion_clear Hwsch;
                  match goal with
                  | H: context[~ Is_defined_in_eqs _ _] |- _ =>
                    eapply H
                  end; eauto.

              - eauto.
                rewrite Hall in Hmc.
                apply Forall_app in Hmc.
                destruct Hmc as [HZ Hmc]; clear HZ.
                apply Forall_cons2 in Hmc.
                destruct Hmc as [Hmc HZ]; clear HZ.
                inversion_clear Hmc as [| |? ? ? ? ? ? Hfindc].
                rewrite Hms.
                eapply stmt_eval_translate_eqns_menv_inv in Hstmt;
                  try eassumption.
                rewrite Hstmt.
                eapply Hfindc; auto.
            }
    Qed.

  End IsStepCorrect.

  (** *** Correctness of [translate] *)

  Section IsNodeCorrect.

    Lemma equiv_prog_empty: equiv_prog [] (translate []).
    Proof.
      intro Hwdef.
      intros n **.
      exfalso.
      repeat match goal with
             | H: msem_node [] _ _ _ _ |- _ => inversion H; clear H
             | H: find_node _ [] = Some _ |- _ => inversion H; clear H
             end.
    Qed.

    Lemma adds_sem_var_find:
      forall Hn i (iargs: list (ident * type)) ivals c,
        NoDupMembers iargs ->
        In i (map fst iargs) ->
        Forall2 (sem_var_instant Hn) (map fst iargs) (map present ivals) ->
        (sem_var_instant Hn i (present c)
        <-> PM.find i (adds (map fst iargs) ivals sempty) = Some c).
    Proof.
      intros ** Hndup Hin Hsem.
      assert (length (map fst iargs) = length (map present ivals)) as Hlen
        by (apply Forall2_length with (1:=Hsem)).
      apply Forall2_combine in Hsem.
      unfold adds.
      assert (PM.find i (fold_right (fun (xv : ident * val) (env : PM.t val) =>
                                       let (x, v) := xv in PM.add x v env)
                                    sempty (combine (map fst iargs) ivals)) = Some c
              <-> PM.find i (fold_right (fun (xv : ident * value) env =>
                                         PM.add (fst xv) (snd xv) env)
                                      (PM.empty _) (combine (map fst iargs) (map present ivals)))
                = Some (present c)) as Hfeq.
      - clear Hndup Hin Hsem.
        rewrite combine_map_both, combine_map_fst.
        assert (forall x c, PM.find x sempty = Some c
                            <-> PM.find x (PM.empty value) = Some (present c))
          as Hrem by (intros; rewrite 2 PM.gempty; split; inversion 1).
        revert Hrem.
        generalize (combine iargs ivals), sempty, (PM.empty value).
        intro xs. induction xs as [|x xs]; [now auto|].
        intros S T Hrem.
        destruct x as [x ty]. destruct x as [i' ?]. simpl.
        destruct (equiv_dec i i') as [Heq|Hneq].
        + rewrite Heq.
          rewrite 2 PM.gss.
          split; injection 1; intro; now subst.
        + rewrite 2 PM.gso; try easy.
          now apply IHxs.
      - rewrite Hfeq; clear Hfeq.
        apply fst_NoDupMembers in Hndup.
        apply In_InMembers_combine with (1:=Hlen) in Hin.
        apply NoDup_NoDupMembers_combine with (ys:=map present ivals) in Hndup.
        revert Hndup Hin Hsem.
        generalize (combine (map fst iargs) (map present ivals)).
        clear Hlen iargs ivals.
        intros xs Hndup Hin Hsem.
        induction xs as [|ity xs]; [now inversion Hin|].
        simpl.
        destruct ity as [i' v'].
        apply nodupmembers_cons in Hndup.
        destruct Hndup as [Hnin Hndup].
        destruct Hin as [Heq|Hneq].
        + rewrite Heq in *.
          rewrite PM.gss.
          inversion_clear Hsem as [|? ? Hvar Hsem'].
          split; intro HH.
          now apply sem_var_instant_det with (1:=Hvar) in HH; rewrite HH.
          injection HH; intro Heq'; now rewrite <-Heq'.
        + rewrite PM.gso.
          2:intro Heq; rewrite Heq in *; contradiction.
          inversion_clear Hsem.
          apply IHxs; auto.
    Qed.

    Theorem is_node_correct:
      forall (G: global),
        (* =is_node_correct= *)
        Welldef_global G ->
        equiv_prog G (translate G).
    (* =end= *)
    Proof.
      (* TODO: Develop a version of msem_node_mult that works for eqs? *)
      induction G as [|node G IH].
      - intro; apply equiv_prog_empty.
      - intros Hwd f n xs ys M menv inputs output Hmc Hmsem Hxs Hys.
        set (nodeName := n_name node).

        assert (Welldef_global G) as HwdG
            by (eapply Welldef_global_cons; eassumption).

        assert (Ordered_nodes (node::G)) as Hord
            by (apply Welldef_global_Ordered_nodes; assumption).

        destruct (ident_eqb nodeName f) eqn:Hfeq.
        + (* Case: f = nodeName *)
          assert (nodeName = f)
            by (apply Pos.eqb_eq; assumption).
          subst f.

          set (prog := translate (node :: G)).

          inversion_clear Hwd as [|? ? Hwd' eqs Hwsch Hndef_in Hfind Hnodup].
          clear Hwd'.
          inversion_clear Hmsem as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hck Heqs
                                   (H & Hin & Hout & Hrabs & Hall)].
          subst eqs nodeName.
          simpl in Heqs; rewrite Hfeq in Heqs; simpl in Heqs.
          injection Heqs. intro Hnode. rewrite Hnode in *. clear Heqs. simpl in *.

          assert (i = node.(n_in) /\ o = node.(n_out) /\ eqs0 = node.(n_eqs) /\ v = node.(n_vars))
            as HR by (rewrite Hnode; intuition).
          destruct HR as (HR1 & HR2 & HR3 & HR4). subst i o eqs0 v.

          set (env := adds (map fst node.(n_in)) inputs sempty).

          assert (msem_equations G bk H M node.(n_eqs))
            by now eapply Forall_msem_equation_global_tl; eauto.

          assert (exists (menv' : heap) (env' : stack),
                     stmt_eval (translate G) menv env
                               (translate_eqns (memories node.(n_eqs)) node.(n_eqs))
                       (menv', env') /\
                     (forall x : ident,
                         Is_variable_in_eqs x node.(n_eqs) ->
                         forall c : val,
                           sem_var_instant (restr H n) x (present c) <->
                           PM.find x env' = Some c) /\
                     Forall (Memory_Corres_eq G (S n) M menv') node.(n_eqs))
            as His_step_correct.
          {
            assert (bk n = true).
            {
              assert (present_list (xs n))
                by now apply present_list_spec; eauto.

              now apply Hck.
            }

            assert (exists oeqs : list equation, n_eqs node = oeqs ++ n_eqs node)
              by now exists [].

            assert (forall x,
                       PS.In x (memories (n_eqs node)) ->
                         Is_defined_in_eqs x (n_eqs node)
                       /\ ~ Is_variable_in_eqs x (n_eqs node)).
            {
              intros y Hinm.
              assert (NoDup_defs node.(n_eqs)) as Hndds
                  by (eapply Is_well_sch_NoDup_defs; eauto).
              split; [now apply Is_defined_in_memories
                     |now apply not_Is_variable_in_memories].
            }

            assert (forall c input,
                       In input (map fst (n_in node)) ->
                       (sem_var_instant (restr H n) input (present c)
                          <->
                       PM.find input env = Some c)).
            {
              intros c input Hinput.
              subst env.
              specialize (Hin n). rewrite Hxs in Hin.

              assert (NoDupMembers node.(n_in))
                by (eapply NoDupMembers_app_l; eauto).

              now eapply adds_sem_var_find.
            }

            assert (forall x,
                       Is_variable_in_eqs x (n_eqs node) ->
                       PM.find x env = None).
            {
              intros x Hivi.
              subst env.
              destruct (in_dec ident_eq_dec x (map fst node.(n_in)))
                as [HinA|HninA].
              + apply Is_variable_in_eqs_Is_defined_in_eqs in Hivi.
                contradiction (not_Exists_Is_defined_in_eqs_n_in node).
                apply Exists_exists. exists x; intuition.
              + apply NotInMembers_find_adds with (1:=HninA).
                apply PM.gempty.
            }

            assert (forall input,
                       In input (map fst (n_in node)) ->
                       ~ Is_defined_in_eqs input (n_eqs node)).
            {
              intros input Hinput Hisdef.
              contradiction (not_Exists_Is_defined_in_eqs_n_in node).
              apply Exists_exists. exists input; intuition.
            }

            assert (Forall (Memory_Corres_eq G n M menv) (n_eqs node)).
            {
              inversion_clear Hmc as [? ? ? ? ? ? ? ? ? ? ? ? ? Hf Hmeqs].
              simpl in Hf.
              rewrite ident_eqb_refl in Hf.
              injection Hf; intros Heq0 Heq1 Heq2 Heq3.
              rewrite <-Heq0 in *.
              eapply Memory_Corres_eqs_node_tl; try eassumption.
            }

            eapply is_step_correct; eauto.
          }

          destruct His_step_correct as (menv' & env' & Hstmt & Hsemvar & Hmem).
          exists menv'.
          split.
          * { destruct (exists_step_method node) as [stepm Hstepm].
              econstructor; eauto.
              - simpl. rewrite Pos.eqb_refl. reflexivity.
              - subst env.
                simpl in Hstepm.
                rewrite ident_eqb_refl in Hstepm.
                injection Hstepm.
                clear Hstepm. intro Hstepm.
                rewrite <-Hstepm, Hnode. clear Hstepm.
                simpl in *.
                rewrite ps_from_list_gather_eqs_memories.
                eassumption.
              - rewrite find_method_stepm_out with (1:=Hstepm).
                specialize (Hout n); simpl in Hout; rewrite Hys in Hout.
                assert (length (map fst (n_out node)) = length output).
                {
                  rewrite <- map_length with (f := present).
                  now (eapply Forall2_length; eauto).
                }

                apply Forall2_forall; [ | now auto ].
                intros x v Hinx.

                assert (Is_variable_in_eqs x (n_eqs node)).
                {
                  assert (In x (map fst (n_out node)))
                    by now (eapply in_combine_l; eauto).

                  now apply n_out_variable_in_eqs.
                }

                assert (sem_var_instant (restr H n) x (present v)).
                {

                  assert (Forall2 (fun x v => sem_var_instant (restr H n) x (present v))
                                  (map fst (n_out node))
                                  output)
                    by now apply Forall2_swap_args,
                                 Forall2_map_1,
                                 Forall2_swap_args in Hout.

                  change ((fun x v => sem_var_instant (restr H n) x (present v)) x v).

                  now eapply Forall2_In; [ exact Hinx | auto ].
                }

                now apply Hsemvar.
            }
          * {
              econstructor.
              - simpl; rewrite Pos.eqb_refl; reflexivity.
              - eapply Memory_Corres_eqs_node_tl; eassumption.
            }

        + (* Case: f <> nodeName *)
          assert (nodeName <> f) as Hfneq
              by (eapply Pos.eqb_neq; try eassumption).

          rewrite Memory_Corres_node_tl in Hmc; try eassumption.
          apply msem_node_cons in Hmsem; try eassumption.
          eapply IH in HwdG.
          edestruct HwdG as [menv' [Hstmt' Hmc']]; try eassumption.
          inversion_clear Hstmt'.
          exists menv'; split.
          * econstructor; try eassumption.
            simpl. subst nodeName. rewrite Hfeq.
            eassumption.
          * rewrite Memory_Corres_node_tl; try assumption.
    Qed.

  End IsNodeCorrect.

  (** *** Correctness of the [reset] code *)

  (* TODO: remove after rewrite of translate_reset_eqns *)
  Lemma stmt_eval_translate_reset_eqn_shift:
    forall prog eqs iacc menv env menv' env',
      stmt_eval prog menv env
                (List.fold_left translate_reset_eqn eqs iacc)
                (menv', env')
      <->
      exists menv'' env'',
        stmt_eval prog menv env
                  (List.fold_left translate_reset_eqn eqs Skip)
                  (menv'', env'')
        /\
        stmt_eval prog menv'' env'' iacc (menv', env').
  Proof.
    Hint Constructors stmt_eval.
    induction eqs as [|eq eqs IH].
    - split; [ now eauto | ].
      intro H; do 2 destruct H.
      destruct H as [H0 H1].
      inversion_clear H0; apply H1.
    - intros.
      split.
      + intro H0.
        apply IH in H0.
        destruct H0 as [menv'' [env'' [H0 H1]]].
        destruct eq; [now eauto| |];
        inversion_clear H1;
        exists menv1; exists env1;
        split; try (simpl; apply IH); eauto.
      + intros.
        destruct eq; [ now (apply IH; auto) | |];
        (apply IH;
          simpl in H;
          destruct H as [menv'' [env'' [H0 H1]]];
          apply IH in H0;
          destruct H0 as [menv0 [env0 [H2 H3]]];
          exists menv0; exists env0;
          split; [now auto|];
          inversion_clear H3;
          inversion H0; subst;
          econstructor; eauto).
  Qed.

  Lemma stmt_eval_translate_reset_eqns_cons:
    forall prog menv env (eq:equation) eqs P,
      (exists menv'' env'',
          stmt_eval prog menv env
                    (translate_reset_eqns (eq :: eqs)) (menv'', env'')
          /\ P menv'' env'')
      <->
      (exists menv' env' menv'' env'',
          stmt_eval prog menv env (translate_reset_eqns eqs) (menv', env')
          /\ stmt_eval prog menv' env'
                      (translate_reset_eqn Skip eq) (menv'', env'')
          /\ P menv'' env'').
  Proof.
    split.
    - intro H.
      destruct H as [menv'' [env'' H]].
      unfold translate_reset_eqns in H.
      simpl in H.
      destruct H as [H HP].
      apply stmt_eval_translate_reset_eqn_shift in H.
      destruct H as [menv' [env' [H1 H2]]].
      exists menv', env', menv'', env''.
      now intuition.
    - intro H.
      destruct H as [menv' [env' [menv'' [env'' [H1 [H2 HP]]]]]].
      unfold translate_reset_eqns.
      simpl.
      exists menv'', env''.
      intuition.
      apply stmt_eval_translate_reset_eqn_shift.
      exists menv', env'.
      intuition.
  Qed.

  Definition equiv_reset G prog f :=
    forall xs ys M,
      msem_node G f xs M ys
      -> forall menv,
        exists menv',
          stmt_call_eval prog menv f reset [] menv' []
        /\ Memory_Corres G 0 f M menv'.

  (* TODO: remove/factorize with equiv_prog *)
  Lemma equiv_reset_empty: forall f, equiv_reset [] (translate []) f.
  Proof.
    intro Hwdef.
    intros n **.
    exfalso.
    repeat match goal with
           | H: msem_node [] _ _ _ _ |- _ => inversion H; clear H
           | H: find_node _ [] = Some _ |- _ => inversion H; clear H
           end.
  Qed.

  Section IsResetCorrect.

    Variables (G: global)
              (HG: Welldef_global G)
              (H: history)
              (M: memory)
              (mems: PS.t)
              (inputs: list ident).


    Lemma is_reset_correct:
      forall bk eqs,
        msem_equations G bk H M eqs ->
        Is_well_sch mems inputs eqs ->
        (forall f, equiv_reset G (translate G) f) ->
        forall menv,
        exists menv' env',
          stmt_eval (translate G) menv sempty (translate_reset_eqns eqs)
                    (menv', env')
          /\ Forall (Memory_Corres_eq G 0 M menv') eqs.
    Proof.
      intros * Hmsem Hwsch Hreset.
      induction eqs as [|eq eqs IH]; [eauto|].
      intro menv.
      destruct eq as [i ck e | is ck f e | i ck v e];
        inversion_clear Hmsem as [| ? ? Hsem Hmsem' ];
        inversion_clear Hwsch;
        edestruct IH as [menv' [env' [Hstmt Hmc]]]; try eassumption.
      - (* EqDef *)
        Hint Constructors Forall.
        Hint Constructors Memory_Corres_eq.
        eauto.
      - (* EqApp *)
        unfold translate_reset_eqns; simpl.
        inversion_clear Hsem
          as [|? ? ? i ? ? ? Mo ? xs' ys' Hsome Hmfind Hxs' Hys' HsemNode|].

        assert (Hhd: hd Ids.default is = i)
          by now destruct is; inv Hsome.
        rewrite Hhd in *.

        set (omenv := match mfind_inst i menv' with
                      | Some m => m | None => hempty end).
        assert (exists omenv',
                   stmt_call_eval (translate G) omenv f reset [] omenv' []
                   /\ Memory_Corres G 0 f Mo omenv')
          as [omenv' [Hstmt_reset Hmcf]]
          by (eapply Hreset; try eassumption).
        exists (madd_obj i omenv' menv'), env'.
        split.
        + rewrite stmt_eval_translate_reset_eqn_shift.
          exists menv', env'.
          split; try eassumption.
          econstructor; [|constructor].
          subst omenv.
          econstructor; eauto.
        + assert (Memory_Corres_eq G 0 M (madd_obj i omenv' menv') (EqApp is ck f e)).
          {
            econstructor; eauto.
            intros M' Hmfind'.
            rewrite Hmfind in Hmfind'; injection Hmfind'; intro Heq; subst M'.
            exists omenv'.
            rewrite mfind_inst_gss.
            now auto.
          }

          assert (Forall (Memory_Corres_eq G 0 M (madd_obj i omenv' menv')) eqs).
          {
            assert (Is_defined_in_eq i (EqApp is ck f e)).
            {
              constructor. destruct is; try inv Hsome.
              rewrite <- Hhd; simpl; auto.
            }

            assert (~ Is_defined_in_eqs i eqs)
              by now auto.

            now apply Memory_Corres_eqs_add_obj.
          }

          now repeat constructor.

      - (* EqFby *)
        exists (madd_mem i (sem_const v) menv'), env'.
        split.
        + unfold translate_reset_eqns; simpl;
          rewrite stmt_eval_translate_reset_eqn_shift.
          exists menv', env'.
          Hint Constructors stmt_eval.
          eauto.
        + inversion_clear Hsem as [| | ? ? ? ? ? ? ? ? ? ? Hmfind Hms Hlae Hls].
          rewrite <- Hms.
          constructor; [|apply Memory_Corres_eqs_add_mem; assumption].
          constructor. intros ms' Hmfind'.
          rewrite Hmfind in Hmfind'.
          injection Hmfind'; intro HR; rewrite HR in *; clear HR Hmfind'.
          rewrite mfind_mem_gss.
          reflexivity.
    Qed.

  End IsResetCorrect.

  Theorem is_node_reset_correct:
    forall (G: global) f,
      Welldef_global G ->
      equiv_reset G (translate G) f.
  Proof.
    induction G as [|node G IH].
    - intros f Hwd.
      apply equiv_reset_empty.
    - intros f Hwdef xs ys M Hmsem menv.

      assert (Ordered_nodes (node :: G)) as HordG
          by (apply Welldef_global_Ordered_nodes; assumption).

      set (nodeName := n_name node).

      destruct (ident_eqb nodeName f) eqn:Heqb.
      + assert (nodeName = f) as Hfeq
            by (apply Pos.eqb_eq; assumption).
        inversion_clear Hmsem as [? ? ? ? ?  inArgs outArg v eqs
                                    ingt0 outgt0 defd vout nodup good
                                    Hbk Hfind (H & Hin & Hout & Hrhs & Hmsem')].
        rename Hmsem' into Hmsem.

        specialize (Hin 0)%nat; specialize (Hout 0)%nat;
        simpl in Hin, Hout.

        simpl in Hfind; subst nodeName; rewrite Heqb in Hfind;
        injection Hfind; clear Hfind; intro Hfind.

        assert (msem_equations G bk H M eqs).
        {
          inversion_clear Hwdef. subst eqs0; rewrite Hfind in *; simpl in *.
          now eapply Forall_msem_equation_global_tl; eauto.
        }

        set (inArgs_fst := map fst inArgs).
        assert (Is_well_sch (memories eqs) inArgs_fst eqs)
          by (inversion Hwdef; subst inArgs_fst eqs0; now rewrite Hfind in *).

        assert (Welldef_global G)
          by (inversion Hwdef; assumption).

        assert (exists menv' env',
                   stmt_eval (translate G) menv sempty
                             (translate_reset_eqns eqs)
                             (menv', env')
                   /\ Forall (Memory_Corres_eq G 0 M menv') eqs)
          as [menv' [env' [Hstmt Hmc]]].
        {
          eapply is_reset_correct; try eassumption.
          intro; apply IH; assumption.
        }

        exists menv'.
        split.
        * { econstructor.
            - simpl. rewrite Heqb. reflexivity.
            - apply exists_reset_method.
            - unfold adds. rewrite Hfind. simpl.
              unfold adds. simpl. eassumption.
            - constructor.
          }
        * {
            econstructor.
            - simpl; rewrite Heqb. subst node. reflexivity.
            - apply Memory_Corres_eqs_node_tl; try assumption.
              inversion Hwdef. subst eqs0. rewrite Hfind in *.
              simpl. assumption.
          }

      + assert (nodeName <> f) as Hfneq
            by (apply Pos.eqb_neq; assumption).

        apply Welldef_global_cons in Hwdef.
        apply msem_node_cons in Hmsem; try assumption.
        edestruct IH as [menv' [Hstmt Hmc]]; try eassumption.
        exists menv'; split.
        * inversion_clear Hstmt.
          econstructor; try eassumption.
          simpl. subst nodeName. rewrite Heqb.
          eassumption.
        * apply Memory_Corres_node_tl; eassumption.
  Qed.

  (** ** Correctness, from the point of view of the event loop *)

  Section EventLoop.

    Variables (G     : global)
              (main  : ident)
              (ins   : stream (list const))
              (outs  : stream (list const))
              (r     : list ident)
              (r_nodup: NoDup r)
              (r_len: forall n, length r = length (outs n))
              (obj   : ident)
              (Hwdef : Welldef_global G)
              (Hwt   : wt_global G).

    (* XXX: [ins] and [outs] are taken to be constants. We thus assume
    that inputs are always presents and, indirectly, restrict our
    theorem to the case were outputs are always present. Note that
    this is true anyway since inputs and outputs are on the same
    clock. *)

    Let xss := fun n => map (fun c => present (sem_const c)) (ins n).
    Let yss := fun n => map (fun c => present (sem_const c)) (outs n).

    Variable (Hsem: sem_node G main xss yss).

    (* TODO: Tim: It seems a little bit strange to interpret the system input
                  as a stream of constant values that is 'passed' to a program
                  by converting them into expressions at each instant.
                  Maybe it would be better to put them in envN and execute
                  a statement whose arguments are the corresponding variable
                  names? *)

    Open Scope nat_scope.
    (* =step= *)
    Fixpoint dostep (n: nat) P r main obj css menv env: Prop :=
      match n with
      | 0 => stmt_eval P hempty sempty (Call [] main obj reset []) (menv, env)
      | S n => let cs := map Const (css n) in
               exists menvN envN, dostep n P r main obj css menvN envN
               /\ stmt_eval P menvN envN (Call r main obj step cs)
                            (menv, env)
      end.
    (* =end= *)

    Lemma is_event_loop_correctG:
      forall M,
        let P := translate G in
        msem_node G main xss M yss ->
        forall n,
        exists menv env omenv,
          dostep (S n) P r main obj ins menv env
          /\ mfind_inst obj menv = Some omenv
          /\ Memory_Corres G (S n) main M omenv
          /\ (forall co, yss n = map present co <-> List.Forall2 (fun r co => PM.find r env = Some co) r co).
    Proof.
      intros * Hmsem n.
      assert (exists menv' env',
                 stmt_eval (translate G) hempty sempty
                           (Call [] main obj reset []) (menv', env')
                 /\ (exists omenv0, mfind_inst obj menv' = Some omenv0
                                    /\ Memory_Corres G 0 main M omenv0))
        as (menv0 & env0 & Hstmtr & (omenv0 & Hmf0 & Hmc0)).
      {
        pose proof (is_node_reset_correct _ _ Hwdef _ _ _ Hmsem hempty) as Hrst.
        destruct Hrst as (omenv' & Hcall & Hcor).
        intros. do 2 eexists.
        split.
        - econstructor; eauto.
          rewrite mfind_inst_empty. eassumption.
        - exists omenv'.
          split; auto.
          apply mfind_inst_gss.
      }

      set (ci0 := ins 0).

      assert (Hpres: xss 0 = map present (map sem_const ci0))
        by (subst xss; unfold present_list; rewrite map_map; eauto).

      assert (exists co0, yss 0 = map present co0)%nat as [co0 Hco0].
      {
        inversion_clear Hmsem as
            [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hbk Hfind
                (H & Hsem_in & Hsem_out & Hsamexs & Hsameys & Habs & Hsem_eqns)].

        assert (Hlen: 0 < length ci0).
        {
          assert (length ci0 = length (xss 0)) as ->
            by now rewrite Hpres, 2 map_length.

          assert (length (map fst i) = length (xss 0)) as <-
              by now eapply Forall2_length;
                     specialize (Hsem_in 0); simpl in Hsem_in;
                     eauto.

          now rewrite map_length.
        }

        assert (present_list (yss 0)).
        {
          edestruct Hsameys as [Habs_ys|]; eauto.
          apply Habs in Habs_ys. rewrite Hpres in Habs_ys.
          destruct ci0; try now inv Hlen. simpl in Habs_ys.
          inv Habs_ys. discriminate.
        }

        now apply present_list_spec.
      }

      induction n.
      - (* Case: n ~ 0 *)

        assert (exists menv' env',
                   stmt_eval (translate G) menv0 env0
                             (Call r main obj step (map Const ci0))
                             (menv', env')
                   /\ (exists omenv, mfind_inst obj menv' = Some omenv
                                     /\ Memory_Corres G 1 main M omenv)
                   /\ List.Forall2 (fun r co0 => PM.find r env' = Some co0) r co0)
          as (menv' & env' & Hstmt & (omenv & Hmfind & Hmc) & Hout).
        { pose proof (is_node_correct _ Hwdef _ _ _ _ _ omenv0 _ _
                                      Hmc0 Hmsem Hpres Hco0)
            as (omenv' & Hstmt & Hmc1).
          do 2 eexists.
          repeat split.
          - econstructor; eauto.
            2:rewrite Hmf0; now eapply Hstmt.
            clear Hstmt Hpres.
            induction ci0; simpl; auto.
          - exists omenv'. split; auto.
            now rewrite mfind_inst_gss.
          - (* XXX: factorize with n ~ S n case *)
            assert (length r = length co0).
            {
              subst yss.
              rewrite <- map_length with (f := present), <- Hco0, map_length; auto. 
            }
            apply Forall2_forall2; split; auto.
            intros ? v n x c Hlen Hnth_r Hnth_co0.
            rewrite <- Hnth_co0.
            now eapply find_gssn; eauto.
        }

        do 3 eexists.
        split; [|split; [| split]]; try eauto.
        + do 2 eexists; eauto.
        + intros co.
          split; intro Hco.
          * assert (co = co0).
            {
              unfold present_list in Hco0, Hco.
              rewrite Hco in Hco0.
              eapply map_inj; eauto.
              now injection 1; auto.
            }
            subst co. auto.
          * (* XXX: Isolate as a lemma *)
            clear - Hco Hout Hco0.
            unfold present_list in Hco0 |- *.
            rewrite Hco0. clear Hco0.
            generalize dependent co0.
            generalize dependent r. clear .
            induction co as [|v co]; intros r Hco co0 Hout;
              destruct co0 as [|v0 co0]; inv Hco;
                inv Hout; simpl; auto.
            assert (v = v0) by congruence. subst v.
            now erewrite IHco; eauto.

      - (* Case: n ~ S n *)

        destruct IHn as [menvN [envN [omenvN [HstepN [HmfindN [HmcN HeqN]]]]]].

        set (ciSn := ins (S n)).

        assert (HpresN: xss (S n) = map present (map sem_const ciSn))
          by (subst xss; unfold present_list; rewrite map_map; eauto).

        assert (exists coSn, yss (S n) = map present coSn) as [coSn Hys].
        {
          inversion_clear Hmsem as
              [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hbk Hfind
                 (H & Hsem_in & Hsem_out & Hsamexs & Hsameys & Habs & Hsem_eqns)].

          assert (Hlen: 0 < length ciSn).
          {
            assert (length ciSn = length (xss (S n))) as ->
                by now rewrite HpresN, 2 map_length.

            assert (length (map fst i) = length (xss (S n))) as <-
                by now eapply Forall2_length;
                       specialize (Hsem_in (S n)); simpl in Hsem_in;
                       eauto.

            now rewrite map_length.
          }

          assert (present_list (yss (S n))).
          {
            edestruct Hsameys as [Habs_ys|]; eauto.
            apply Habs in Habs_ys. rewrite HpresN in Habs_ys.
            destruct ciSn; try now inv Hlen. simpl in Habs_ys.
            inv Habs_ys. discriminate.
          }

          now apply present_list_spec.
        }

        assert (exists menvN' envN',
                   stmt_eval (translate G) menvN envN
                             (Call r main obj step (map Const ciSn))
                             (menvN', envN')
                   /\ (exists omenvsN, mfind_inst obj menvN' = Some omenvsN
                                    /\ Memory_Corres G (S (S n)) main M omenvsN)
                   /\ Forall2 (fun r coSn => PM.find r envN' = Some coSn) r coSn)
          as (menvSn & envsN & Hstmt & (omenvSn & Hmfind & Hmc) & Hout).
        { pose proof (is_node_correct _ Hwdef _ _ _ _ _ omenvN _ _
                                      HmcN Hmsem HpresN Hys)
            as (omenvsN & Hstmt & HmcSn).
          do 2 eexists.
          repeat split.
          - econstructor; eauto.
            2:rewrite HmfindN; now eapply Hstmt.
            clear Hstmt HpresN.
            induction ciSn; simpl; auto.
          - exists omenvsN. split; auto.
            now rewrite mfind_inst_gss.
          - assert (length r = length coSn).
            {
              subst yss.
              rewrite <- map_length with (f := present), <- Hys, map_length; auto. 
            }
            apply Forall2_forall2; split; auto.
            intros ? v k x c Hlen Hnth_r Hnth_coSn.
            rewrite <- Hnth_coSn.
            now eapply find_gssn; eauto.
        }

        (* XXX: this explicit [exists] is necessary:
                Coq picks a wrong instance otherwise. *)
        exists (menvSn).
        do 2 eexists.

        split; [|split; [| split]]; eauto.
        + do 2 eexists; split; simpl step; try eauto.
        + (* XXX: factorize with n ~ 0 case *)
          intros co.
          split; intro Hco.
          * assert (co = coSn).
            {
              unfold present_list in Hys, Hco.
              rewrite Hco in Hys.
              eapply map_inj; eauto.
              now injection 1; auto.
            }
            now subst co.
          * clear - Hco Hout Hys.
            unfold present_list in Hys |- *.
            rewrite Hys. clear Hys.
            generalize dependent coSn.
            generalize dependent r. clear r.
            induction co as [|v co]; intros r Hco coSn Hout;
              destruct coSn as [|vSn coSn]; inv Hco;
                inv Hout; simpl; auto.
            assert (v = vSn) by congruence. subst v.
            now erewrite IHco; eauto.
    Qed.


    Theorem is_event_loop_correct:
      (* =translate_correct= *)
      sem_node G main xss yss ->
      forall n, exists menv env,
          dostep (S n) (translate G) r main obj ins menv env
          /\ (forall co, yss n = map present co <-> List.Forall2 (fun r co => PM.find r env = Some co) r co).
    (* =end= *)
    Proof.
      intros until n.

      assert (exists M, msem_node G main xss M yss) as [M Hmsem]
          by (eapply sem_msem_node; eauto).

      assert (exists menv env omenv,
                 dostep (S n) (translate G) r main obj ins menv env
                 /\ mfind_inst obj menv = Some omenv
                 /\ Memory_Corres G (S n) main M omenv
                 /\ (forall co, yss n = map present co <-> List.Forall2 (fun r co => PM.find r env = Some co) r co))
        as [menv [env [omenv [Hstep [_ [_ Hys]]]]]]
          by (eapply is_event_loop_correctG; eauto).

      do 2 eexists; eauto.
    Qed.

    CoInductive dostep' P : nat -> heap -> Prop
      := Step : forall n menv0 menv1,
          let cins := List.map sem_const (ins n) in
          let couts := List.map sem_const (outs n) in
          stmt_call_eval P menv0 main step cins menv1 couts ->
          dostep' P (S n) menv1 ->
          dostep' P n menv0.
    
    Section Dostep'_coind.

    Variable P : program.
    Variable R : nat -> heap -> Prop.

    Hypothesis StepCase: forall n menv0,
      R n menv0 ->
      exists menv1,
        let cins := map sem_const (ins n) in
        let couts := map sem_const (outs n) in
          stmt_call_eval P menv0 main step cins menv1 couts
        /\ R (S n) menv1.
    Lemma dostep'_coind : forall n menv,
        R n menv -> dostep' P n menv.
    Proof.
    cofix COINDHYP.
    intros ** HR.
    pose proof (StepCase _ _ HR) as Hstep.
    destruct Hstep as (? & ? & ? ).
    econstructor; eauto.
    Qed.
    
    End Dostep'_coind.

    Lemma dostep'_init:
      forall M,
        msem_node G main xss M yss ->
        exists menv0 c_main P',
            stmt_call_eval (translate G) hempty main reset [] menv0 []
          /\ Memory_Corres G 0 main M menv0
          /\ find_class main (translate G) = Some (c_main, P')
          /\ wt_mem menv0 P' c_main.
    Proof.
    intros M Hmsem.

    edestruct is_node_reset_correct as (menv0 & Hstmt & Hmem); eauto.

    assert (exists nd, find_node main G = Some nd) as [nd ?]
        by now inv Hmsem; eauto.

    edestruct find_node_translate as (cls & P' & ? & ?); eauto.
    pose proof exists_reset_method nd.

    assert (wt_program (translate G))
      by now apply Typing.translate_wt.
   
    subst.
    assert (wt_mem menv0 P' (translate_node nd))
      by now eapply pres_sem_stmt_call; eauto || constructor.

    firstorder.
    Qed.

    Lemma dostep'_correct_msem: 
      forall M menv0,
        let P := translate G in
        msem_node G main xss M yss ->
        stmt_call_eval (translate G) hempty main reset [] menv0 [] ->
        Memory_Corres G 0 main M menv0 ->
        dostep' P 0 menv0.
    Proof.
    intros M menv0 Hdef Hmsem Hstmt Hmc.  

    set (R := fun n menv => Memory_Corres G n main M menv).
    apply dostep'_coind with (R := R).
    2: now unfold R; eauto.
    intros. unfold R in H. 

    set (cinsN := ins n).
    set (coutsN := outs n).

    assert (HpresN: xss n = map present (map sem_const cinsN))
      by (subst xss; unfold present_list; rewrite map_map; eauto).
    
    assert (yss n = map present (map sem_const coutsN))
      by (subst yss; unfold present_list; rewrite map_map; eauto).
   
    edestruct is_node_correct as (omenvSn & HstmtSn & HmcSn); eauto.
    Qed.

    Theorem dostep'_correct:
      exists menv0 c_main P',
        stmt_call_eval (translate G) hempty main reset [] menv0 []
      /\ find_class main (translate G) = Some (c_main, P')
      /\ wt_mem menv0 P' c_main
      /\ dostep' (translate G) 0 menv0.
    Proof.
    intros.
    assert (exists M, msem_node G main xss M yss) as [M Hmsem]
        by now eapply sem_msem_node; eauto.

    edestruct dostep'_init as (? & ? & ? & ? & ? & ? & ?); eauto.
    do 3 eexists.
    repeat (split; eauto).
    eapply dostep'_correct_msem; eauto.
    Qed.

  End EventLoop.

End CORRECTNESS.

Module CorrectnessFun
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import DF    : NLUSTRE Ids Op OpAux)
       (Import Obc   : OBC Ids Op OpAux)
       (Import Mem   : MEMORIES Ids Op DF.Syn)
       (Import Trans : TRANSLATION Ids Op OpAux DF.Syn Obc.Syn Mem)
       (Import Typing: TYPING Ids Op OpAux DF Obc Mem Trans)

       <: CORRECTNESS Ids Op OpAux DF Obc Mem Trans Typing.

  Include CORRECTNESS Ids Op OpAux DF Obc Mem Trans Typing.

End CorrectnessFun.