(**
  Instantiate the shared successor-row translation from an aligned native
  predecessor trace.

  The aligned package has two complementary sources of information.  Its
  current local trace supplies the numeral at [succ predecessor] and the two
  admissibility-domain substitutions.  Its paired successor supplies the
  local Sigma/Pi row codes at the next hierarchy level and wraps those same
  rows into the public next-global predicates.

  The row graph may choose two numeral codes independently.  Both represent
  the same successor level, so represented numeral-code functionality first
  identifies them.  One parameter record can then serve the soundness
  predicates, both relocated row templates, and the eventual predecessor
  handoff.  Deep closure of the current adequate orbit selects the two lower
  ternary predicates with their honest-syntax commuting laws.
*)

From Stdlib Require Import List.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedNumeralTermCode
  RawCodedFormulaOperations
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateNumeralParameters
  RawCodedTemplateTernaryApplication
  RawCodedTernaryPredicateDeepClosure
  RawCodedDynamicTruthTemplateNumeralParameters
  RawCodedDynamicTruthTemplateDirectInputs
  RawCodedDynamicTruthUniversalLeafSourceTemplate
  RawCodedDynamicTruthPiUniversalLeafSourceTemplate
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthPairedGlobalAdequateOrbitDeepClosure
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthNativeLocalProofCompilation
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessExtendedDirectInputs
  RawCodedRestrictedPADerivationSoundnessExtendedRowIdentification.

Module PABoundedRawCodedDynamicTruthAlignedPredecessorExtendedRows.

Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTernaryPredicateDeepClosure.
Import PABoundedRawCodedDynamicTruthTemplateNumeralParameters.
Import PABoundedRawCodedDynamicTruthTemplateDirectInputs.
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthPiUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import
  PABoundedRawCodedDynamicTruthPairedGlobalAdequateOrbitDeepClosure.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeLocalProofCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessExtendedDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessExtendedRowIdentification.

(** The conclusion deliberately quantifies the two soundness selectors only
    after fixing the shared parameter record and lower-predicate selectors.
    A later native-soundness adapter may therefore install its coherent
    context/conclusion pair without changing either row translation. *)
Theorem raw_dynamicTruthAlignedPredecessor_extended_rows_exists : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (tail : nat -> M) predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi
    (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi),
  exists inputLevelNumeral upperLevelNumeral
      localSigmaRow localPiRow
      sigmaRowDomain piRowDomain
      sigmaLowerApplication piLowerApplication : M,
  exists parameters : RawCodedTemplateNumeralParameters M,
  exists lowerPiSelector : RawCodedTernaryApplicationSelector M
      (rawDynamicTruthNativeLocalAligned_currentInputGlobalPi M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned),
  exists lowerSigmaSelector : RawCodedTernaryApplicationSelector M
      (rawDynamicTruthNativeLocalAligned_currentInputGlobalSigma M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned),
  exists lowerPiCommuting :
      RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax M
        (rawDynamicTruthNativeLocalAligned_currentInputGlobalPi M tail
          predecessorLevel baseContext currentLocal
          nextInputGlobalSigma nextInputGlobalPi aligned)
        lowerPiSelector,
  exists lowerSigmaCommuting :
      RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax M
        (rawDynamicTruthNativeLocalAligned_currentInputGlobalSigma M tail
          predecessorLevel baseContext currentLocal
          nextInputGlobalSigma nextInputGlobalPi aligned)
        lowerSigmaSelector,
    rawNumeralTemplateParameterBound parameters
      coqDynamicTruthLowerLevelParameterName =
        raw_succ M predecessorLevel /\
    rawNumeralTemplateParameterBound parameters
      coqDynamicTruthUpperLevelParameterName =
        raw_succ M (raw_succ M predecessorLevel) /\
    rawNumeralTemplateParameterCode parameters
      coqDynamicTruthLowerLevelParameterName = inputLevelNumeral /\
    rawNumeralTemplateParameterCode parameters
      coqDynamicTruthUpperLevelParameterName = upperLevelNumeral /\
    RawNumeralTermCodeAt M
      (raw_succ M predecessorLevel) inputLevelNumeral /\
    RawNumeralTermCodeAt M
      (raw_succ M (raw_succ M predecessorLevel)) upperLevelNumeral /\
    RawCodedFormulaSingleSubstitution M inputLevelNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
      (rawDynamicTruthNativeLocalAligned_currentSigmaDomain M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned) /\
    RawCodedFormulaSingleSubstitution M inputLevelNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthLocalPiInputDomainTemplate))
      (rawDynamicTruthNativeLocalAligned_currentPiDomain M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned) /\
    RawDynamicTruthPairedGlobalWrapperAt M
      localSigmaRow localPiRow nextInputGlobalSigma nextInputGlobalPi /\
    (forall contextTruth conclusionTruth :
        RawCoqRestrictedPATruthDirectSelector M parameters,
      let inputs := rawCoqRestrictedPAExtendedRowsInputs
        M hPA parameters contextTruth conclusionTruth
        (rawDynamicTruthNativeLocalAligned_currentInputGlobalPi M tail
          predecessorLevel baseContext currentLocal
          nextInputGlobalSigma nextInputGlobalPi aligned)
        (rawDynamicTruthNativeLocalAligned_currentInputGlobalSigma M tail
          predecessorLevel baseContext currentLocal
          nextInputGlobalSigma nextInputGlobalPi aligned)
        lowerPiSelector lowerSigmaSelector
        lowerPiCommuting lowerSigmaCommuting in
      rawDirectTemplateTerm inputs
        coqRestrictedPASoundnessLowerLevelTerm = inputLevelNumeral /\
      rawDirectTemplateFormula inputs
        (coqDynamicTruthSigmaSuccessorRowTemplateAt
          coqRestrictedPALowerPiTruthPredicateName) = localSigmaRow /\
      rawDirectTemplateFormula inputs
        (coqDynamicTruthPiSuccessorRowTemplateAt
          coqRestrictedPALowerSigmaTruthPredicateName) = localPiRow).
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned.
  pose proof
    (rawDynamicTruthNativeLocalAligned_currentTrace M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned) as hcurrentTrace.
  destruct hcurrentTrace as [hcurrentOrbit hcurrentBody].
  destruct hcurrentBody as
    (inputLevel & evidenceGlobalSigma & evidenceGlobalPi &
     inputLevelNumeral & hinputLevel & hcurrentSuccessor &
     hinputNumeral & hlocalSigmaDomain & hlocalPiDomain &
     hlocalSigmaEvidence & hlocalPiEvidence).
  subst inputLevel.
  destruct
    (rawDynamicTruthNativeLocalAligned_successor M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned) as
    (localSigmaRow & localPiRow & [hsigmaRow hpiRow] & hglobalWrapper).
  destruct hsigmaRow as
    (sigmaUpperNumeral & sigmaRowDomain & sigmaLowerApplication &
     hsigmaUpperNumeral & hsigmaRowDomain & hsigmaLower & hsigmaRowCode).
  destruct hpiRow as
    (piUpperNumeral & piRowDomain & piLowerApplication &
     hpiUpperNumeral & hpiRowDomain & hpiLower & hpiRowCode).
  pose proof (raw_numeralTermCodeAt_functional M hPA
    (raw_succ M (raw_succ M predecessorLevel))
    sigmaUpperNumeral piUpperNumeral
    hsigmaUpperNumeral hpiUpperNumeral) as hupperNumerals.
  subst piUpperNumeral.
  destruct
    (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_deep_closed
      M hPA tail (raw_succ M predecessorLevel)
      (rawDynamicTruthNativeLocalAligned_currentInputGlobalSigma M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)
      (rawDynamicTruthNativeLocalAligned_currentInputGlobalPi M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)
      hcurrentOrbit) as [hcurrentSigmaDeep hcurrentPiDeep].
  destruct
    (raw_coqDynamicTruthTemplateTernarySelector_exists_of_deepClosed
      M hPA
      (rawDynamicTruthNativeLocalAligned_currentInputGlobalPi M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)
      hcurrentPiDeep) as [lowerPiSelector lowerPiCommuting].
  destruct
    (raw_coqDynamicTruthTemplateTernarySelector_exists_of_deepClosed
      M hPA
      (rawDynamicTruthNativeLocalAligned_currentInputGlobalSigma M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)
      hcurrentSigmaDeep) as [lowerSigmaSelector lowerSigmaCommuting].
  set (parameters :=
    rawCoqDynamicTruthTemplateNumeralParameters M
      (raw_succ M predecessorLevel)
      (raw_succ M (raw_succ M predecessorLevel))
      inputLevelNumeral sigmaUpperNumeral
      hinputNumeral hsigmaUpperNumeral).
  exists inputLevelNumeral, sigmaUpperNumeral,
    localSigmaRow, localPiRow,
    sigmaRowDomain, piRowDomain,
    sigmaLowerApplication, piLowerApplication,
    parameters, lowerPiSelector, lowerSigmaSelector,
    lowerPiCommuting, lowerSigmaCommuting.
  split; [reflexivity |].
  split; [reflexivity |].
  split; [reflexivity |].
  split; [reflexivity |].
  split; [exact hinputNumeral |].
  split; [exact hsigmaUpperNumeral |].
  split; [exact hlocalSigmaDomain |].
  split; [exact hlocalPiDomain |].
  split; [exact hglobalWrapper |].
  intros contextTruth conclusionTruth.
  set (inputs := rawCoqRestrictedPAExtendedRowsInputs
    M hPA parameters contextTruth conclusionTruth
    (rawDynamicTruthNativeLocalAligned_currentInputGlobalPi M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned)
    (rawDynamicTruthNativeLocalAligned_currentInputGlobalSigma M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned)
    lowerPiSelector lowerSigmaSelector
    lowerPiCommuting lowerSigmaCommuting).
  assert (hlowerTerm : rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm = inputLevelNumeral).
  {
    unfold inputs, rawCoqRestrictedPAExtendedRowsInputs,
      coqRestrictedPASoundnessLowerLevelTerm.
    rewrite
      rawCoqRestrictedPADerivationSoundnessExtendedDirectTerm_view.
    unfold rawCoqRestrictedPADerivationSoundnessTemplateTermView,
      rawCoqRestrictedPADerivationSoundnessTermViewSymbols,
      coqDynamicTruthLowerLevelTerm.
    cbn [rawStructuralTemplateTermWith rawNumeralTemplateSymbols].
    reflexivity.
  }
  pose proof
    (raw_coqRestrictedPAExtendedRows_identify_native
      M hPA parameters contextTruth conclusionTruth
      (raw_succ M predecessorLevel)
      (raw_succ M (raw_succ M predecessorLevel))
      (rawDynamicTruthNativeLocalAligned_currentInputGlobalPi M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)
      (rawDynamicTruthNativeLocalAligned_currentInputGlobalSigma M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)
      lowerPiSelector lowerSigmaSelector
      lowerPiCommuting lowerSigmaCommuting
      eq_refl eq_refl sigmaUpperNumeral
      sigmaRowDomain piRowDomain
      sigmaLowerApplication piLowerApplication
      eq_refl hsigmaRowDomain hpiRowDomain hsigmaLower hpiLower) as hrows.
  destruct hrows as [hsigmaTemplate hpiTemplate].
  split; [exact hlowerTerm |].
  split.
  - unfold inputs. rewrite hsigmaTemplate. symmetry. exact hsigmaRowCode.
  - unfold inputs. rewrite hpiTemplate. symmetry. exact hpiRowCode.
Qed.

End PABoundedRawCodedDynamicTruthAlignedPredecessorExtendedRows.
