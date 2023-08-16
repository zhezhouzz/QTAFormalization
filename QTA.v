From stdpp Require Import mapset.
From stdpp Require Import natmap.
From stdpp Require Import gmap.
From stdpp Require Import fin vector.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import OperationalSemantics.
Import BasicTyping.
Import List.

Notation typeset := (gset ty).
Global Instance base_ty_EqDecision : EqDecision base_ty.
Proof.
  intros x y. destruct x, y.
  - left; f_equal; eauto.
  - right; f_equal; eauto.
  - right; f_equal; eauto.
  - left; f_equal; eauto.
Qed.

Global Instance ty_EqDecision : EqDecision ty.
Proof.
  intro x. induction x; intros.
  - destruct y.
    destruct (decide (b = b0)); subst.
    + left; f_equal.
    + right. intro H; inversion H; subst; auto.
    + right. intro H; inversion H; subst; auto.
  - destruct y. right; intro H; inversion H.
    specialize (IHx1 y1). specialize (IHx2 y2).
    destruct IHx1; destruct IHx2; subst.
    + left; f_equal.
    + right. intro H; inversion H; subst; auto.
    + right. intro H; inversion H; subst; auto.
    + right. intro H; inversion H; subst; auto.
Qed.

Global Instance ty_countable : Countable ty.
Proof.
Admitted.

Definition qstate := ty.
(* Definition signature := aset. *)
(* Definition stateset := typeset. *)
Definition transition {n : nat} := vec qstate n -> atom -> qstate.
Definition similarity_edge := qstate -> qstate -> Prop.
