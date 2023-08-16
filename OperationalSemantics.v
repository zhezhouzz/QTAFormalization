From stdpp Require Import mapset.
From CT Require Import CoreLang.
From CT Require Import CoreLangProp.

Import Atom.
Import CoreLang.
Import NamelessTactics.

Reserved Notation  "t1 '↪' t2" (at level 60, t1 constr, t2 constr).

(** the small step operational semantics *)
Inductive step : tm -> tm -> Prop :=
| STLetE1: forall e1 e1' e,
    body e ->
    e1 ↪ e1' ->
    (tlete e1 e) ↪ (tlete e1' e)
| STLetE2: forall (v1: value) e,
    lc v1 -> body e ->
    (tlete (treturn v1) e) ↪ (e ^t^ v1)
| STLetAppLam: forall T (v_x: value) e1 e,
    body e1 -> body e -> lc v_x ->
    (tletapp (vlam T e1) v_x e) ↪ tlete (e1 ^t^ v_x) e
| STMatchbTrue: forall e1 e2,
    lc e1 -> lc e2 ->
    (tmatchb true e1 e2) ↪ e1
| STMatchbFalse: forall e1 e2,
    lc e1 -> lc e2 ->
    (tmatchb false e1 e2) ↪ e2
where "t1 '↪' t2"  := (step t1 t2).

Lemma step_regular: forall e1 e2, e1 ↪ e2 -> lc e1 /\ lc e2.
Proof.
  intros.
  induction H; split; auto.
  - destruct_hyp_conj. rewrite lete_lc_body; split; auto.
  - destruct_hyp_conj. rewrite lete_lc_body; split; auto.
  - try destruct_hyp_conj. rewrite lete_lc_body; split; auto.
  - apply open_lc_tm; auto.
  - rewrite letapp_lc_body; split; auto. rewrite lc_abs_iff_body; auto.
  - rewrite lete_lc_body; split; auto. apply open_lc_tm; auto.
Qed.

Lemma step_regular1: forall e1 e2, e1 ↪ e2 -> lc e1.
Proof.
  intros. apply step_regular in H. destruct H; auto.
Qed.

Lemma step_regular2: forall e1 e2, e1 ↪ e2 -> lc e2.
Proof.
  intros. apply step_regular in H. destruct H; auto.
Qed.

Global Hint Resolve step_regular1: core.
Global Hint Resolve step_regular2: core.

Inductive multistep : tm -> tm -> Prop :=
| multistep_refl : forall (e : tm),
    lc e -> multistep e e
| multistep_step : forall (x y z: tm),
    x ↪ y ->
    multistep y z ->
    multistep x z.

Notation "t1 '↪*' t2" := (multistep t1 t2) (at level 60, t1 constr, t2 constr).

Global Hint Constructors multistep : core.

Theorem multistep_trans :
  forall (x y z : tm), x ↪* y -> y ↪* z -> x ↪* z.
Proof.
  intros. generalize dependent z.
  induction H; eauto.
Qed.

Theorem multistep_R : forall (x y : tm),
    x ↪ y -> x ↪* y.
Proof. intros; eauto.
Qed.

Lemma multi_step_regular: forall e1 e2, e1 ↪* e2 -> lc e1 /\ lc e2.
Proof.
  induction 1; intuition eauto.
Qed.

Lemma multi_step_regular1: forall e1 e2, e1 ↪* e2 -> lc e1.
Proof.
  intros. apply multi_step_regular in H. destruct H; auto.
Qed.

Lemma multi_step_regular2: forall e1 e2, e1 ↪* e2 ->  lc e2.
Proof.
  intros. apply multi_step_regular in H. destruct H; auto.
Qed.

Ltac step_regular_simp :=
  repeat match goal with
    | [H: _ ↪* _ |- lc _ ] => apply multi_step_regular in H; destruct H; auto
    | [H: _ ↪ _ |- lc _ ] => apply step_regular in H; destruct H; auto
    | [H: _ ↪* _ |- body _] => apply multi_step_regular in H; destruct H; auto
    | [H: _ ↪ _ |- body _] => apply step_regular in H; destruct H; auto
    end.
