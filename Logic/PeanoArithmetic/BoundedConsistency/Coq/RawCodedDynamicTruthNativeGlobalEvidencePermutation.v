(**
  Isolate the free-variable permutation used by native global evidence.

  Append traversal constructs a ternary global formula with its free inputs
  in the ordinary de Bruijn order [0,1,2].  The derivation-soundness
  template presents the current formula and its two assignment arguments as
  [2,1,0].  Applying the represented ternary predicate therefore does not
  reproduce the append source literally: it reverses the outer three free
  variables.

  The distinction matters below existential elimination.  In particular,
  an opened append-source body cannot be reused as native evidence without
  accounting for this permutation.  The two fixed normalization lemmas and
  their raw trace corollaries make that boundary explicit for the shared
  Sigma/Pi successor rows.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateNumeralParameters
  RawCodedTemplateTernaryApplication
  RawCodedTemplateTernaryApplicationFunctionality
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPATemplateTernaryApplicationCompilation
  RawCodedDynamicTruthPredecessorGlobalExistentialElimination
  RawCodedDynamicTruthSuccessorRowsAppendNormalization.

Module PABoundedRawCodedDynamicTruthNativeGlobalEvidencePermutation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTemplateTernaryApplicationFunctionality.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import
  PABoundedRawCodedRestrictedPATemplateTernaryApplicationCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorGlobalExistentialElimination.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.

(** Reverse precisely the three free argument slots of a ternary formula.
    Indices above the interface are left unchanged.  The concrete global
    sources below are scoped by three, so that final clause is deliberately
    irrelevant there, but spelling it as the identity makes the intended
    operation clear to later proof-renaming clients. *)
Definition templateReverseFirstThreeRenaming (index : nat) : nat :=
  match index with
  | 0 => 2
  | 1 => 1
  | 2 => 0
  | S (S (S outer)) => S (S (S outer))
  end.

(** These are finite syntax normalizations, not semantic truth claims.  The
    large successor rows are fixed templates; kernel reduction verifies that
    the protected three-opening protocol is exactly the advertised reversal.
    Keeping separate polarity names prevents clients from silently swapping
    the mode selected by the corresponding append root. *)
Lemma coqDynamicTruthSharedSigmaGlobalTernaryApplication_reverse :
  coqRestrictedPATemplateTernaryApplication
    (coqDynamicTruthGlobalExistentialSource 0
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate)
    (ttVar 2) (ttVar 1) (ttVar 0) =
  templateFormulaRename templateReverseFirstThreeRenaming
    (coqDynamicTruthGlobalExistentialSource 0
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate).
Proof. vm_compute. reflexivity. Qed.

Lemma coqDynamicTruthSharedPiGlobalTernaryApplication_reverse :
  coqRestrictedPATemplateTernaryApplication
    (coqDynamicTruthGlobalExistentialSource 1
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate)
    (ttVar 2) (ttVar 1) (ttVar 0) =
  templateFormulaRename templateReverseFirstThreeRenaming
    (coqDynamicTruthGlobalExistentialSource 1
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate).
Proof. vm_compute. reflexivity. Qed.

(** The syntactic normalization is useful only if it preserves the exact
    represented five-trace application.  These corollaries connect it to the
    direct structural translator used by the native strong-step package. *)
Theorem raw_coqDynamicTruthSharedSigmaGlobalTernaryApplication_reverse_trace :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (parameters : RawCodedTemplateNumeralParameters M)
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters),
  let inputs :=
    rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth in
  RawCodedTernaryApplication M
    (rawDirectTemplateFormula inputs
      (coqDynamicTruthGlobalExistentialSource 0
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate))
    (rawDirectTemplateTerm inputs (ttVar 2))
    (rawDirectTemplateTerm inputs (ttVar 1))
    (rawDirectTemplateTerm inputs (ttVar 0))
    (rawDirectTemplateFormula inputs
      (templateFormulaRename templateReverseFirstThreeRenaming
        (coqDynamicTruthGlobalExistentialSource 0
          coqDynamicTruthSharedSigmaSuccessorRowTemplate
          coqDynamicTruthSharedPiSuccessorRowTemplate))).
Proof.
  intros M hPA parameters contextTruth conclusionTruth inputs.
  rewrite <- coqDynamicTruthSharedSigmaGlobalTernaryApplication_reverse.
  exact (raw_coqRestrictedPATemplateTernaryApplication_trace
    M hPA parameters contextTruth conclusionTruth
    (coqDynamicTruthGlobalExistentialSource 0
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate)
    (ttVar 2) (ttVar 1) (ttVar 0)).
Qed.

Theorem raw_coqDynamicTruthSharedPiGlobalTernaryApplication_reverse_trace :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (parameters : RawCodedTemplateNumeralParameters M)
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters),
  let inputs :=
    rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth in
  RawCodedTernaryApplication M
    (rawDirectTemplateFormula inputs
      (coqDynamicTruthGlobalExistentialSource 1
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate))
    (rawDirectTemplateTerm inputs (ttVar 2))
    (rawDirectTemplateTerm inputs (ttVar 1))
    (rawDirectTemplateTerm inputs (ttVar 0))
    (rawDirectTemplateFormula inputs
      (templateFormulaRename templateReverseFirstThreeRenaming
        (coqDynamicTruthGlobalExistentialSource 1
          coqDynamicTruthSharedSigmaSuccessorRowTemplate
          coqDynamicTruthSharedPiSuccessorRowTemplate))).
Proof.
  intros M hPA parameters contextTruth conclusionTruth inputs.
  rewrite <- coqDynamicTruthSharedPiGlobalTernaryApplication_reverse.
  exact (raw_coqRestrictedPATemplateTernaryApplication_trace
    M hPA parameters contextTruth conclusionTruth
    (coqDynamicTruthGlobalExistentialSource 1
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate)
    (ttVar 2) (ttVar 1) (ttVar 0)).
Qed.

(** Functional selection converts the relational traces into the literal
    code equations used when an aligned native selector is transported along
    the paired-global wrapper equation. *)
Corollary
    raw_coqDynamicTruthSharedSigmaGlobalTernaryApplication_reverse_output :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (parameters : RawCodedTemplateNumeralParameters M)
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters),
  let inputs :=
    rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth in
  forall selector : RawCodedTernaryApplicationSelector M
      (rawDirectTemplateFormula inputs
        (coqDynamicTruthGlobalExistentialSource 0
          coqDynamicTruthSharedSigmaSuccessorRowTemplate
          coqDynamicTruthSharedPiSuccessorRowTemplate)),
  rawTernaryApplicationOutput selector
      (rawDirectTemplateTerm inputs (ttVar 2))
      (rawDirectTemplateTerm inputs (ttVar 1))
      (rawDirectTemplateTerm inputs (ttVar 0)) =
    rawDirectTemplateFormula inputs
      (templateFormulaRename templateReverseFirstThreeRenaming
        (coqDynamicTruthGlobalExistentialSource 0
          coqDynamicTruthSharedSigmaSuccessorRowTemplate
          coqDynamicTruthSharedPiSuccessorRowTemplate)).
Proof.
  intros M hPA parameters contextTruth conclusionTruth inputs selector.
  rewrite <- coqDynamicTruthSharedSigmaGlobalTernaryApplication_reverse.
  exact (raw_coqRestrictedPATemplateTernaryApplication_output
    M hPA parameters contextTruth conclusionTruth
    (coqDynamicTruthGlobalExistentialSource 0
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate)
    selector (ttVar 2) (ttVar 1) (ttVar 0)).
Qed.

Corollary
    raw_coqDynamicTruthSharedPiGlobalTernaryApplication_reverse_output :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (parameters : RawCodedTemplateNumeralParameters M)
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters),
  let inputs :=
    rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth in
  forall selector : RawCodedTernaryApplicationSelector M
      (rawDirectTemplateFormula inputs
        (coqDynamicTruthGlobalExistentialSource 1
          coqDynamicTruthSharedSigmaSuccessorRowTemplate
          coqDynamicTruthSharedPiSuccessorRowTemplate)),
  rawTernaryApplicationOutput selector
      (rawDirectTemplateTerm inputs (ttVar 2))
      (rawDirectTemplateTerm inputs (ttVar 1))
      (rawDirectTemplateTerm inputs (ttVar 0)) =
    rawDirectTemplateFormula inputs
      (templateFormulaRename templateReverseFirstThreeRenaming
        (coqDynamicTruthGlobalExistentialSource 1
          coqDynamicTruthSharedSigmaSuccessorRowTemplate
          coqDynamicTruthSharedPiSuccessorRowTemplate)).
Proof.
  intros M hPA parameters contextTruth conclusionTruth inputs selector.
  rewrite <- coqDynamicTruthSharedPiGlobalTernaryApplication_reverse.
  exact (raw_coqRestrictedPATemplateTernaryApplication_output
    M hPA parameters contextTruth conclusionTruth
    (coqDynamicTruthGlobalExistentialSource 1
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate)
    selector (ttVar 2) (ttVar 1) (ttVar 0)).
Qed.

End PABoundedRawCodedDynamicTruthNativeGlobalEvidencePermutation.
