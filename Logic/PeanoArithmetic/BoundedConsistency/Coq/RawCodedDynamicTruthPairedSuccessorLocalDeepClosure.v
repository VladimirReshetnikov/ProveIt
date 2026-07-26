(**
  Unconditional deep closure of the paired local successor rows.

  The global dynamic-truth wrapper reaches a local row below ten existential
  and five universal binders, so its incoming contextual cutoff is 18.  Each
  local row then binds eight traversal witnesses.  Its domain and branch
  formulas are consequently visited at cutoff 26, while the lower-predicate
  application occurring below the three local binder witnesses is visited at
  cutoff 29.

  The two genuinely nonstandard leaves were treated separately:

  - a successor-domain witness is deeply closed from 26 by the concrete
    substitution-interchange square for its nonstandard numeral replacement;
  - a native lower application is deeply closed from 26 by reinterpreting its
    three fixed substitutions as ternary application at [#9,#1,#0] and using
    the deep shift/opening interchange laws.

  This file only assembles those leaves through the transparent Sigma and Pi
  row polynomials.  In particular, the exported callback has no operation,
  commutation, selector, or standardness premise beyond [RawPASatisfies].
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedFormulaRankStep
  RawCodedSyntaxConstructors
  RawCodedStandardFormulaScopeDecision
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthPairedSuccessorRowGraph
  RawCodedDynamicTruthGlobalSuccessorDeepClosure
  RawCodedDynamicTruthSuccessorDomainDeepClosure
  RawCodedDynamicTruthLowerApplicationDeepClosure.

Module PABoundedRawCodedDynamicTruthPairedSuccessorLocalDeepClosure.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedFormulaRankStep.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedStandardFormulaScopeDecision.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthGlobalSuccessorDeepClosure.
Import PABoundedRawCodedDynamicTruthSuccessorDomainDeepClosure.
Import PABoundedRawCodedDynamicTruthLowerApplicationDeepClosure.

(** Deep closure is contravariant in its displayed lower bound: once every
    operation above [small] fixes a code, the same is true above [large]. *)
Lemma rawCodedFormulaDeepClosedFrom_weaken : forall
    (M : RawPAModel), RawPASatisfies M -> forall small large code,
  rawLe M small large ->
  RawCodedFormulaDeepClosedFrom M small code ->
  RawCodedFormulaDeepClosedFrom M large code.
Proof.
  intros M hPA small large code hsmall
    [hadequate [hshift hopening]].
  split; [exact hadequate |]. split.
  - intros cutoff amount hlarge.
    apply hshift.
    exact (raw_le_trans M hPA small large cutoff hsmall hlarge).
  - intros replacement assignmentCode assignmentStep depth
      hreplacement hlarge.
    apply (hopening replacement assignmentCode assignmentStep depth
      hreplacement).
    exact (raw_le_trans M hPA small large depth hsmall hlarge).
Qed.

(** The sole nonstandard lower leaf is placed under three additional
    existential binders.  Cutoff-26 closure therefore supplies precisely the
    cutoff-29 instance needed by the constructor proof. *)
Lemma rawCodedFormulaDeepClosedFrom_twenty_six_to_twenty_nine : forall
    (M : RawPAModel), RawPASatisfies M -> forall code,
  RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 26) code ->
  RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 29) code.
Proof.
  intros M hPA code hcode.
  apply (rawCodedFormulaDeepClosedFrom_weaken M hPA
    (rawNumeralValue M 26) (rawNumeralValue M 29) code).
  - apply rawLe_numerals_of_le; [exact hPA | lia].
  - exact hcode.
Qed.

(** Executable scope checks discharge the finite syntax bookkeeping for all
    fixed leaves.  They make no claim about either nonstandard opaque leaf. *)
Local Ltac solve_scope :=
  apply (proj1 (standardFormulaScopedb_spec _ _));
  vm_compute; reflexivity.

Local Ltac solve_fixed_leaf :=
  apply raw_fixedFormulaNumeralCode_deep_closed_from_scope;
  [assumption | solve_scope].

(** The innermost Sigma branch.  Its lower application is below the three
    witnesses used to prepend a binder to the coded assignment. *)
Lemma rawDynamicTruthSigmaNoBinderCode_deep_closed_from_twenty_six : forall
    (M : RawPAModel), RawPASatisfies M -> forall lowerApplication,
  RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 29)
    lowerApplication ->
  RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 26)
    (rawDynamicTruthSigmaNoBinderCode M lowerApplication).
Proof.
  intros M hPA lowerApplication hlower.
  unfold rawDynamicTruthSigmaNoBinderCode, rawFormulaEx3Code.
  apply rawFormulaImpCode_deep_closed_from; [exact hPA | |].
  - repeat apply rawFormulaExCode_deep_closed_from; try exact hPA.
    change (RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 29)
      (rawFormulaAndCode M
        (rawFixedFormulaNumeralCode M
          dynamicTruthSigmaRowBinderPrependFormula)
        lowerApplication)).
    apply rawFormulaAndCode_deep_closed_from; [exact hPA | |].
    + solve_fixed_leaf.
    + exact hlower.
  - change (RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 26)
      (rawQuotedFormulaCode M pBot)).
    apply raw_quotedFormula_deep_closed_from_scope; [exact hPA |].
    solve_scope.
Qed.

(** All other Sigma branch constructors stay at cutoff 26. *)
Lemma rawDynamicTruthSigmaBranchesCode_deep_closed_from_twenty_six : forall
    (M : RawPAModel), RawPASatisfies M -> forall lowerApplication,
  RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 29)
    lowerApplication ->
  RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 26)
    (rawDynamicTruthSigmaBranchesCode M lowerApplication).
Proof.
  intros M hPA lowerApplication hlower.
  unfold rawDynamicTruthSigmaBranchesCode,
    rawDynamicTruthSigmaUniversalCode.
  apply rawFormulaOrCode_deep_closed_from; [exact hPA | |].
  - solve_fixed_leaf.
  - apply rawFormulaOrCode_deep_closed_from; [exact hPA | |].
    + solve_fixed_leaf.
    + apply rawFormulaOrCode_deep_closed_from; [exact hPA | |].
      * solve_fixed_leaf.
      * apply rawFormulaOrCode_deep_closed_from; [exact hPA | |].
        -- solve_fixed_leaf.
        -- apply rawFormulaOrCode_deep_closed_from; [exact hPA | |].
           ++ solve_fixed_leaf.
           ++ apply rawFormulaOrCode_deep_closed_from; [exact hPA | |].
              ** solve_fixed_leaf.
              ** apply rawFormulaAndCode_deep_closed_from;
                   [exact hPA | |].
                 --- solve_fixed_leaf.
                 --- exact
                       (rawDynamicTruthSigmaNoBinderCode_deep_closed_from_twenty_six
                         M hPA lowerApplication hlower).
Qed.

(** Eight existential constructors transport the two cutoff-26 children back
    to the wrapper-facing cutoff 18. *)
Theorem rawDynamicTruthSigmaSuccessorRowCode_deep_closed : forall
    (M : RawPAModel), RawPASatisfies M -> forall domain lowerApplication,
  RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 26) domain ->
  RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 26)
    lowerApplication ->
  RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 18)
    (rawDynamicTruthSigmaSuccessorRowCode M domain lowerApplication).
Proof.
  intros M hPA domain lowerApplication hdomain hlower.
  unfold rawDynamicTruthSigmaSuccessorRowCode, rawFormulaEx8Code.
  repeat apply rawFormulaExCode_deep_closed_from; try exact hPA.
  change (RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 26)
    (rawFormulaAndCode M domain
      (rawDynamicTruthSigmaBranchesCode M lowerApplication))).
  apply rawFormulaAndCode_deep_closed_from; [exact hPA | |].
  - exact hdomain.
  - apply rawDynamicTruthSigmaBranchesCode_deep_closed_from_twenty_six;
      [exact hPA |].
    exact (rawCodedFormulaDeepClosedFrom_twenty_six_to_twenty_nine
      M hPA lowerApplication hlower).
Qed.

(** Pi has the same three-binder no-binder branch, with the dual fixed
    prefix formulas. *)
Lemma rawDynamicTruthPiNoBinderCode_deep_closed_from_twenty_six : forall
    (M : RawPAModel), RawPASatisfies M -> forall lowerApplication,
  RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 29)
    lowerApplication ->
  RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 26)
    (rawDynamicTruthPiNoBinderCode M lowerApplication).
Proof.
  intros M hPA lowerApplication hlower.
  unfold rawDynamicTruthPiNoBinderCode,
    rawDynamicTruthPiFormulaEx3Code.
  apply rawFormulaImpCode_deep_closed_from; [exact hPA | |].
  - repeat apply rawFormulaExCode_deep_closed_from; try exact hPA.
    change (RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 29)
      (rawFormulaAndCode M
        (rawFixedFormulaNumeralCode M
          dynamicTruthPiRowBinderPrependFormula)
        lowerApplication)).
    apply rawFormulaAndCode_deep_closed_from; [exact hPA | |].
    + solve_fixed_leaf.
    + exact hlower.
  - change (RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 26)
      (rawQuotedFormulaCode M pBot)).
    apply raw_quotedFormula_deep_closed_from_scope; [exact hPA |].
    solve_scope.
Qed.

(** All other Pi branch constructors stay at cutoff 26. *)
Lemma rawDynamicTruthPiBranchesCode_deep_closed_from_twenty_six : forall
    (M : RawPAModel), RawPASatisfies M -> forall lowerApplication,
  RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 29)
    lowerApplication ->
  RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 26)
    (rawDynamicTruthPiBranchesCode M lowerApplication).
Proof.
  intros M hPA lowerApplication hlower.
  unfold rawDynamicTruthPiBranchesCode,
    rawDynamicTruthPiExistentialCode,
    rawDynamicTruthPiFixedFormulaNumeralCode.
  apply rawFormulaOrCode_deep_closed_from; [exact hPA | |].
  - solve_fixed_leaf.
  - apply rawFormulaOrCode_deep_closed_from; [exact hPA | |].
    + solve_fixed_leaf.
    + apply rawFormulaOrCode_deep_closed_from; [exact hPA | |].
      * solve_fixed_leaf.
      * apply rawFormulaOrCode_deep_closed_from; [exact hPA | |].
        -- solve_fixed_leaf.
        -- apply rawFormulaOrCode_deep_closed_from; [exact hPA | |].
           ++ solve_fixed_leaf.
           ++ apply rawFormulaAndCode_deep_closed_from;
                [exact hPA | |].
              ** solve_fixed_leaf.
              ** exact
                   (rawDynamicTruthPiNoBinderCode_deep_closed_from_twenty_six
                     M hPA lowerApplication hlower).
Qed.

Theorem rawDynamicTruthPiSuccessorRowCode_deep_closed : forall
    (M : RawPAModel), RawPASatisfies M -> forall domain lowerApplication,
  RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 26) domain ->
  RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 26)
    lowerApplication ->
  RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 18)
    (rawDynamicTruthPiSuccessorRowCode M domain lowerApplication).
Proof.
  intros M hPA domain lowerApplication hdomain hlower.
  unfold rawDynamicTruthPiSuccessorRowCode,
    rawDynamicTruthPiFormulaEx8Code.
  repeat apply rawFormulaExCode_deep_closed_from; try exact hPA.
  change (RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 26)
    (rawFormulaAndCode M domain
      (rawDynamicTruthPiBranchesCode M lowerApplication))).
  apply rawFormulaAndCode_deep_closed_from; [exact hPA | |].
  - exact hdomain.
  - apply rawDynamicTruthPiBranchesCode_deep_closed_from_twenty_six;
      [exact hPA |].
    exact (rawCodedFormulaDeepClosedFrom_twenty_six_to_twenty_nine
      M hPA lowerApplication hlower).
Qed.

(** The exact previously conditional callback, now discharged solely from
    PA.  We prove the stronger full deep-closure property for each actual row
    and then project the operational component requested by the interface. *)
Theorem raw_dynamicTruthPairedGlobalSuccessorLocalDeepClosure : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPairedGlobalSuccessorLocalDeepClosure M.
Proof.
  intros M hPA previousSigma previousPi lowerLevel localSigma localPi
    hpreviousSigma hpreviousPi [hsigma hpi].
  destruct hsigma as
    (sigmaNumeral & sigmaDomain & sigmaLower & hsigmaNumeral &
     hsigmaDomain & hsigmaLower & ->).
  destruct hpi as
    (piNumeral & piDomain & piLower & hpiNumeral &
     hpiDomain & hpiLower & ->).
  assert (hsigmaDomainDeep :
      RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 26)
        sigmaDomain).
  {
    exact (raw_dynamicTruthSigmaSuccessorDomain_deep_closed
      M hPA lowerLevel sigmaNumeral sigmaDomain
      hsigmaNumeral hsigmaDomain).
  }
  assert (hpiDomainDeep :
      RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 26)
        piDomain).
  {
    exact (raw_dynamicTruthPiSuccessorDomain_deep_closed
      M hPA lowerLevel piNumeral piDomain hpiNumeral hpiDomain).
  }
  assert (hsigmaLowerDeep :
      RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 26)
        sigmaLower).
  {
    exact
      (raw_dynamicTruthCoqLowerApplication_deep_closed_from_twenty_six
        M hPA previousPi sigmaLower hpreviousPi hsigmaLower).
  }
  assert (hpiLowerDeep :
      RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 26)
        piLower).
  {
    exact
      (raw_dynamicTruthPiCoqLowerApplication_deep_closed_from_twenty_six
        M hPA previousSigma piLower hpreviousSigma hpiLower).
  }
  split.
  - exact (proj2 (rawDynamicTruthSigmaSuccessorRowCode_deep_closed
      M hPA sigmaDomain sigmaLower hsigmaDomainDeep hsigmaLowerDeep)).
  - exact (proj2 (rawDynamicTruthPiSuccessorRowCode_deep_closed
      M hPA piDomain piLower hpiDomainDeep hpiLowerDeep)).
Qed.

(** Alias with the premise-first naming used by other PA-model callbacks. *)
Corollary
    raw_dynamicTruthPairedGlobalSuccessorLocalDeepClosure_of_PA : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPairedGlobalSuccessorLocalDeepClosure M.
Proof.
  exact raw_dynamicTruthPairedGlobalSuccessorLocalDeepClosure.
Qed.

End PABoundedRawCodedDynamicTruthPairedSuccessorLocalDeepClosure.
