(**
  The canonical rank-zero Sigma application is not an open PA theorem.

  This negative boundary is important for proof-compilation architecture.
  The canonical first-successor application has the semantics of a positive
  level-one truth certificate.  At the code of falsity no such certificate
  exists, independently of the two assignment arguments.  Consequently a
  compiler cannot first prove both canonical polarities over a bare PA-axiom
  context and only afterwards weaken them beneath the predecessor-state
  assumptions.  Those assumptions must participate in global traversal.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthTraversal
  RawCodedFixedLevelBottomLaws
  RawCodedDynamicTruthZeroLocalExclusiveTemplateIdentification
  RawCodedDynamicTruthNativeZeroCanonicalTraceExactification.

Module
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalApplicationNonprovability.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelBottomLaws.
Import
  PABoundedRawCodedDynamicTruthZeroLocalExclusiveTemplateIdentification.
Import
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalTraceExactification.

(** A local raw presentation of the ordinary natural-number PA model.  It is
    kept here rather than importing the much stronger non-isomorphism
    development merely for its copy of this five-field structure. *)
Definition canonicalCounterexampleNatRawPAModel : RawPAModel :=
  {| raw_carrier := nat;
     raw_zero := 0;
     raw_succ := S;
     raw_add := Nat.add;
     raw_mul := Nat.mul |}.

Lemma canonicalCounterexampleNatRaw_term_eval : forall
    (environment : nat -> nat) term,
  raw_term_eval canonicalCounterexampleNatRawPAModel environment term =
  PA.Term.eval PA.natModel environment term.
Proof.
  intros environment term. induction term; simpl; congruence.
Qed.

Lemma canonicalCounterexampleNatRaw_formula_sat : forall
    (environment : nat -> nat) formula,
  raw_formula_sat canonicalCounterexampleNatRawPAModel environment formula <->
  PA.Formula.Sat PA.natModel environment formula.
Proof.
  intros environment formula. revert environment.
  induction formula as [left right | | left ihLeft right ihRight |
      left ihLeft right ihRight | left ihLeft right ihRight |
      body ihBody | body ihBody]; intro environment; simpl.
  - rewrite !canonicalCounterexampleNatRaw_term_eval. reflexivity.
  - reflexivity.
  - rewrite ihLeft, ihRight. reflexivity.
  - rewrite ihLeft, ihRight. reflexivity.
  - rewrite ihLeft, ihRight. reflexivity.
  - split; intros hall value.
    + apply (proj1 (ihBody (scons nat value environment))).
      exact (hall value).
    + apply (proj2 (ihBody (scons nat value environment))).
      exact (hall value).
  - split; intros [value hbody]; exists value.
    + apply (proj1 (ihBody (scons nat value environment))). exact hbody.
    + apply (proj2 (ihBody (scons nat value environment))). exact hbody.
Qed.

(** The standard natural model satisfies the full sealed PA schema. *)
Lemma raw_natModel_satisfies_PA :
  RawPASatisfies canonicalCounterexampleNatRawPAModel.
Proof.
  intros ax hax environment.
  apply (proj2
    (canonicalCounterexampleNatRaw_formula_sat environment ax)).
  exact (Formula.sat_axiom_s PA.natModel environment ax hax).
Qed.

(** Set the root argument [#2] to the code of falsity.  The remaining two
    arguments are immaterial: the generic bottom law excludes a positive
    certificate for every assignment representation, including malformed
    ones. *)
Definition dynamicTruthZeroSigmaBottomCounterenvironment : nat -> nat :=
  fun index =>
    match index with
    | 2 => rawFormulaBotCode canonicalCounterexampleNatRawPAModel
    | _ => 0
    end.

Lemma dynamicTruthZeroInputGlobalSigmaApplicationFormula_not_nat_valid :
  ~ raw_formula_sat canonicalCounterexampleNatRawPAModel
      dynamicTruthZeroSigmaBottomCounterenvironment
      dynamicTruthZeroInputGlobalSigmaApplicationFormula.
Proof.
  intro happlication.
  apply (proj1
    (raw_sat_dynamicTruthZeroInputGlobalSigmaApplicationFormula_native_iff
      canonicalCounterexampleNatRawPAModel
      dynamicTruthZeroSigmaBottomCounterenvironment))
    in happlication.
  unfold dynamicTruthZeroSigmaEvidenceFormula in happlication.
  apply (proj1
    (raw_sat_fixedLevelSigmaTruthCertificateTermAt_iff
      1 canonicalCounterexampleNatRawPAModel
      dynamicTruthZeroSigmaBottomCounterenvironment
      (tVar 2) (tVar 1) (tVar 0))) in happlication.
  cbn [dynamicTruthZeroSigmaBottomCounterenvironment raw_term_eval]
    in happlication.
  exact
    (raw_fixedLevelSigmaBottomFalse_successor
      canonicalCounterexampleNatRawPAModel
      raw_natModel_satisfies_PA 0 0 0 happlication).
Qed.

(** In particular, no ordinary PA derivation can have the open canonical
    Sigma application as its conclusion.  Soundness is applied at the
    explicit counterenvironment rather than by universally closing the
    formula, so the theorem exactly matches the local-proof endpoints used
    by the callback development. *)
Theorem PA_not_proves_dynamicTruthZeroInputGlobalSigmaApplicationFormula :
  ~ Formula.BProv Formula.Ax_s nil
      dynamicTruthZeroInputGlobalSigmaApplicationFormula.
Proof.
  intro hproof.
  pose proof
    (raw_sat_of_BProv_axs_context canonicalCounterexampleNatRawPAModel nil
      dynamicTruthZeroInputGlobalSigmaApplicationFormula
      raw_natModel_satisfies_PA hproof
      dynamicTruthZeroSigmaBottomCounterenvironment)
    as hsound.
  apply dynamicTruthZeroInputGlobalSigmaApplicationFormula_not_nat_valid.
  apply hsound.
  intros formula hmember. contradiction.
Qed.

End
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalApplicationNonprovability.
