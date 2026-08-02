(** Standard-natural witness comparisons for bootstrapped proofs.

    Foundation also represents these relations by internal Sigma-one
    formulas.  This module deliberately isolates their external semantics:
    proof witnesses are ordinary natural numbers, so well-ordering of [nat]
    gives minimal witnesses without any internal induction principle. *)

From Stdlib Require Import Arith.PeanoNat Lia Lists.List.
From Foundation.Vorspiel.Nat Require Import Basic.
From Foundation.Syntax.Predicate Require Import Language.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Bootstrapping.Syntax Require Import Theory.
From Foundation.FirstOrder.Bootstrapping.Syntax.Proof Require Import Basic.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** [phi] has a proof no later than any possible proof of [psi]. *)
Definition boot_provability_comparison_le {L}
    (EL : language_encodable L) (T : theory L)
    (ET : boot_theory_encoding EL T) (phi psi : nat) : Prop :=
  exists b,
    @boot_proof L EL T ET b phi /\
    forall b', b' < b -> ~ @boot_proof L EL T ET b' psi.

(** [phi] has a proof strictly before every possible proof of [psi]. *)
Definition boot_provability_comparison_lt {L}
    (EL : language_encodable L) (T : theory L)
    (ET : boot_theory_encoding EL T) (phi psi : nat) : Prop :=
  exists b,
    @boot_proof L EL T ET b phi /\
    forall b', b' <= b -> ~ @boot_proof L EL T ET b' psi.

Lemma boot_provability_comparison_le_of_lt : forall L EL T ET phi psi,
  @boot_provability_comparison_lt L EL T ET phi psi ->
  @boot_provability_comparison_le L EL T ET phi psi.
Proof.
  intros L EL T ET phi psi [b [Hb Hleast]].
  exists b. split; [exact Hb |].
  intros b' Hb'. apply Hleast; lia.
Qed.

Lemma boot_provability_comparison_le_to_provable :
    forall L EL T ET phi psi,
  @boot_provability_comparison_le L EL T ET phi psi ->
  @boot_provable L EL T ET phi.
Proof.
  intros L EL T ET phi psi [b [Hb _]].
  now exists b.
Qed.

Lemma boot_provability_comparison_le_trans : forall L EL T ET phi psi chi,
  @boot_provability_comparison_le L EL T ET phi psi ->
  @boot_provability_comparison_le L EL T ET psi chi ->
  @boot_provability_comparison_le L EL T ET phi chi.
Proof.
  intros L EL T ET phi psi chi
    [b [Hb Hpsi]] [d [Hd Hchi]].
  assert (Hbd : b <= d).
  { destruct (Nat.le_gt_cases b d) as [Hbd | Hdb]; [exact Hbd |].
    exfalso. exact (Hpsi d Hdb Hd). }
  exists b. split; [exact Hb |].
  intros w Hw. apply Hchi. lia.
Qed.

(** A bootstrapped proof code determines its singleton conclusion.  This is
    the code-level counterpart of the source proof object's first field. *)
Lemma boot_proof_conclusion_unique : forall L EL T ET code phi psi,
  @boot_proof L EL T ET code phi ->
  @boot_proof L EL T ET code psi ->
  phi = psi.
Proof.
  intros L EL T ET code phi psi Hphi Hpsi.
  assert (Hcodes : boot_nat_list_code [phi] = boot_nat_list_code [psi]).
  { rewrite <- (boot_derivation_code_conseq Hphi).
    rewrite <- (boot_derivation_code_conseq Hpsi).
    reflexivity. }
  apply boot_nat_list_code_injective in Hcodes.
  now injection Hcodes.
Qed.

Lemma boot_provability_comparison_le_antisymm :
    forall L EL T ET phi psi,
  @boot_provability_comparison_le L EL T ET phi psi ->
  @boot_provability_comparison_le L EL T ET psi phi ->
  phi = psi.
Proof.
  intros L EL T ET phi psi
    [b [Hb Hpsi]] [d [Hd Hphi]].
  assert (Hbd : b <= d).
  { destruct (Nat.le_gt_cases b d) as [Hbd | Hdb]; [exact Hbd |].
    exfalso. exact (Hpsi d Hdb Hd). }
  assert (Hdb : d <= b).
  { destruct (Nat.le_gt_cases d b) as [Hdb | Hbd']; [exact Hdb |].
    exfalso. exact (Hphi b Hbd' Hb). }
  assert (Hcode : b = d) by lia.
  subst d. eapply boot_proof_conclusion_unique; eauto.
Qed.

Lemma boot_provability_comparison_iff_le_refl_provable :
    forall L EL T ET phi,
  @boot_provability_comparison_le L EL T ET phi phi <->
  @boot_provable L EL T ET phi.
Proof.
  intros L EL T ET phi. split.
  - intro H.
    exact (@boot_provability_comparison_le_to_provable
      L EL T ET phi phi H).
  - intros [bound Hbound].
    destruct (@nat_least_number
      (fun b => @boot_proof L EL T ET b phi))
      as [b [Hb Hleast]].
    + now exists bound.
    + exists b. now split.
Qed.

Lemma boot_provability_comparison_lt_irrefl : forall L EL T ET phi,
  ~ @boot_provability_comparison_lt L EL T ET phi phi.
Proof.
  intros L EL T ET phi [b [Hb Hleast]].
  exact (Hleast b (Nat.le_refl b) Hb).
Qed.

Lemma boot_provability_comparison_lt_trans : forall L EL T ET phi psi chi,
  @boot_provability_comparison_lt L EL T ET phi psi ->
  @boot_provability_comparison_lt L EL T ET psi chi ->
  @boot_provability_comparison_lt L EL T ET phi chi.
Proof.
  intros L EL T ET phi psi chi
    [b [Hb Hpsi]] [d [Hd Hchi]].
  assert (Hbd : b < d).
  { destruct (Nat.lt_ge_cases b d) as [Hbd | Hdb]; [exact Hbd |].
    exfalso. exact (Hpsi d Hdb Hd). }
  exists b. split; [exact Hb |].
  intros w Hw. apply Hchi. lia.
Qed.

Lemma boot_provability_comparison_not_lt_of_le :
    forall L EL T ET phi psi,
  @boot_provability_comparison_le L EL T ET phi psi ->
  ~ @boot_provability_comparison_lt L EL T ET psi phi.
Proof.
  intros L EL T ET phi psi
    [b [Hb Hpsi]] [d [Hd Hphi]].
  destruct (Nat.lt_ge_cases d b) as [Hdb | Hbd].
  - exact (Hpsi d Hdb Hd).
  - exact (Hphi b Hbd Hb).
Qed.

(** Foundation assumes a finite index type.  Externally, finiteness is not
    needed: one starting proof bounds a least proof code among all indices. *)
Lemma boot_provability_comparison_find_minimal_proof :
    forall L EL T ET (I : Type) (phi : I -> nat) i,
  @boot_provable L EL T ET (phi i) ->
  exists j, forall k,
    @boot_provability_comparison_le L EL T ET (phi j) (phi k).
Proof.
  intros L EL T ET I phi i [bound Hbound].
  destruct (@nat_least_number
    (fun b => exists j : I, @boot_proof L EL T ET b (phi j)))
    as [b [[j Hb] Hleast]].
  - exists bound, i. exact Hbound.
  - exists j. intro k. exists b. split; [exact Hb |].
    intros w Hw Hwk. apply (Hleast w Hw).
    now exists k.
Qed.
