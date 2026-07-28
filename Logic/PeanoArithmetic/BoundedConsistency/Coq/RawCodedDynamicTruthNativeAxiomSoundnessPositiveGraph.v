(**
  The carrier-indexed positive PA-axiom-soundness field.

  At predecessor [p], the current truth level is [S p].  The fifth master
  coordinate must therefore say that every transparently witnessed PA axiom
  in the lower domain at [S p] has a Sigma certificate in the genuine next
  predicate at [S (S p)].  This file constructs that sentence from the
  actual paired global orbit and its actual paired successor; neither truth
  predicate is an unconstrained formula-code parameter.

  The graph construction is deliberately separated from object provability.
  Its exact semantics and adequate relational totality use only represented
  syntax operations.  For every externally fixed standard level we prove the
  exact sentence in PA, quote that proof, and obtain [RawCodedPAProofOf].  A
  possibly nonstandard carrier index cannot be converted to a metatheoretic
  level, so the final section isolates precisely that remaining uniform
  object-proof compiler.  In particular, semantic truth is never used as a
  source of proof syntax.  The represented standard graph trace is kept in
  literal substitution normal form; the fixed-level field polynomial below
  separately carries the represented proof of its propositionally aligned
  pretty-printed instance.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  RawCodedPAProvability
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedAssignment
  RawCodedFormulaOperations
  RawCodedFormulaOperationsStandardRealization
  RawCodedNumeralTermCode
  RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthTraversal
  RawCodedFixedLevelTruthTotality
  RawCodedFormulaShiftAtomicAdequacy
  RawCodedTemplateTernaryApplication
  RawCodedPAAxiomTruth
  RawCodedDynamicTruthAxiomSoundnessBaseGraph
  RawCodedDynamicTruthFixedSyntaxFragments
  RawCodedDynamicTruthTernaryApplicationTotality
  RawCodedTermOpeningAfterShiftSyntaxStability
  RawCodedDynamicTruthPairedSuccessorAdequacy
  RawCodedDynamicTruthPairedSuccessorRowGraph
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthNativeCrossLevelPositiveGraph
  RawCodedOutputFirstPairedFormulaGraphComposition.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthNativeAxiomSoundnessPositiveGraph.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedPAProvability.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaOperationsStandardRealization.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFormulaShiftAtomicAdequacy.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedPAAxiomTruth.
Import PABoundedRawCodedDynamicTruthAxiomSoundnessBaseGraph.
Import PABoundedRawCodedDynamicTruthFixedSyntaxFragments.
Import PABoundedRawCodedDynamicTruthTernaryApplicationTotality.
Import PABoundedRawCodedTermOpeningAfterShiftSyntaxStability.
Import PABoundedRawCodedDynamicTruthPairedSuccessorAdequacy.
Import PABoundedRawCodedDynamicTruthPairedSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelPositiveGraph.
Import PABoundedRawCodedOutputFirstPairedFormulaGraphComposition.

(** ------------------------------------------------------------------
    The exact one-variable target family.

    The two domain parameters and the next-Sigma parameter have the single
    axiom variable [#0] free.  The assignment code and assignment step are
    literal zero terms.  Thus [dynamicTruthNativeAxiomLowerAdmissibleFormula]
    is exactly [fixedLevelTruthAdmissibleTermAt] after standard alignment. *)

Definition dynamicTruthNativeAxiomLowerAdmissibleFormula
    (sigmaDomain piDomain : formula) : formula :=
  pAnd
    (codedFormulaAtomicallyAdequateTermAt (tVar 0))
    (pAnd
      (codedAssignmentDefinedThroughTermAt tZero tZero (tVar 0))
      (pOr sigmaDomain piDomain)).

Definition dynamicTruthNativeAxiomSoundnessCarrierBodyFormula
    (sigmaDomain piDomain nextSigma : formula) : formula :=
  pImp
    (pAnd
      (witnessedPAAxiomRecognitionTermAt (tVar 0))
      (dynamicTruthNativeAxiomLowerAdmissibleFormula
        sigmaDomain piDomain))
    nextSigma.

Definition dynamicTruthNativeAxiomSoundnessCarrierFormula
    (sigmaDomain piDomain nextSigma : formula) : formula :=
  pAll
    (dynamicTruthNativeAxiomSoundnessCarrierBodyFormula
      sigmaDomain piDomain nextSigma).

Definition dynamicTruthNativeAxiomSigmaDomainTemplate : formula :=
  dynamicTruthSigmaRecordDomainTermAt (tVar 0) (tVar 1).

Definition dynamicTruthNativeAxiomPiDomainTemplate : formula :=
  dynamicTruthPiRecordDomainTermAt (tVar 0) (tVar 1).

(** The one-variable templates instantiate by the represented syntax
    operation itself.  Naming that literal substituted syntax is important:
    reducing [codedFormulaRankTermAt] through substitution would normalize
    its complete represented traversal.  The literal output is
    propositionally, rather than cheaply definitionally, the corresponding
    fixed-level domain formula. *)
Lemma raw_dynamicTruthNativeAxiomSigmaDomain_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawCodedFormulaSingleSubstitution M
    (rawQuotedTermCode M (Term.numeral level))
    (rawQuotedFormulaCode M dynamicTruthNativeAxiomSigmaDomainTemplate)
    (rawQuotedFormulaCode M
      (Formula.subst (Formula.instTerm (Term.numeral level))
        dynamicTruthNativeAxiomSigmaDomainTemplate)).
Proof.
  intros M hPA level.
  exact (raw_codedFormulaSingleSubstitution_standard M hPA
    (Term.numeral level) dynamicTruthNativeAxiomSigmaDomainTemplate).
Qed.

Lemma raw_dynamicTruthNativeAxiomPiDomain_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall level,
  RawCodedFormulaSingleSubstitution M
    (rawQuotedTermCode M (Term.numeral level))
    (rawQuotedFormulaCode M dynamicTruthNativeAxiomPiDomainTemplate)
    (rawQuotedFormulaCode M
      (Formula.subst (Formula.instTerm (Term.numeral level))
        dynamicTruthNativeAxiomPiDomainTemplate)).
Proof.
  intros M hPA level.
  exact (raw_codedFormulaSingleSubstitution_standard M hPA
    (Term.numeral level) dynamicTruthNativeAxiomPiDomainTemplate).
Qed.

Definition dynamicTruthNativeAxiomSoundnessFixedLevelBodyFormula
    (currentLevel : nat) : formula :=
  pImp
    (pAnd
      (witnessedPAAxiomRecognitionTermAt (tVar 0))
      (fixedLevelTruthAdmissibleTermAt
        currentLevel (tVar 0) tZero tZero))
    (fixedLevelSigmaTruthCertificateTermAt
      (S currentLevel) (tVar 0) tZero tZero).

(** A literal single universal is important: the carrier polynomial below
    constructs precisely one [All] node rather than an opaque closure. *)
Definition dynamicTruthNativeAxiomSoundnessFixedLevelFormula
    (currentLevel : nat) : formula :=
  pAll (dynamicTruthNativeAxiomSoundnessFixedLevelBodyFormula currentLevel).

Lemma dynamicTruthNativeAxiomSoundnessCarrierFormula_fixedLevel : forall
    currentLevel,
  dynamicTruthNativeAxiomSoundnessCarrierFormula
    (fixedLevelSigmaDomainTermAt currentLevel (tVar 0))
    (fixedLevelPiDomainTermAt currentLevel (tVar 0))
    (fixedLevelSigmaTruthCertificateTermAt
      (S currentLevel) (tVar 0) tZero tZero) =
  dynamicTruthNativeAxiomSoundnessFixedLevelFormula currentLevel.
Proof.
  intro currentLevel.
  unfold dynamicTruthNativeAxiomSoundnessCarrierFormula,
    dynamicTruthNativeAxiomSoundnessCarrierBodyFormula,
    dynamicTruthNativeAxiomLowerAdmissibleFormula,
    dynamicTruthNativeAxiomSoundnessFixedLevelFormula,
    dynamicTruthNativeAxiomSoundnessFixedLevelBodyFormula,
    fixedLevelTruthAdmissibleTermAt.
  reflexivity.
Qed.

(** Law-free semantics of the carrier formula, before any fixed-level
    identification.  The three carried formula parameters are evaluated in
    the environment where the universally bound axiom is at index zero. *)
Definition RawDynamicTruthNativeAxiomSoundnessCarrierAt
    (M : RawPAModel) (tail : nat -> M)
    (sigmaDomain piDomain nextSigma : formula) : Prop :=
  forall axiom : M,
    RawWitnessedPAAxiomRecognition M axiom ->
    RawCodedFormulaAtomicallyAdequate M axiom ->
    RawCodedAssignmentDefinedThrough M
      (raw_zero M) (raw_zero M) axiom ->
    (raw_formula_sat M (scons M axiom tail) sigmaDomain \/
     raw_formula_sat M (scons M axiom tail) piDomain) ->
    raw_formula_sat M (scons M axiom tail) nextSigma.

Arguments RawDynamicTruthNativeAxiomSoundnessCarrierAt
  M tail sigmaDomain piDomain nextSigma : clear implicits.

Theorem raw_sat_dynamicTruthNativeAxiomSoundnessCarrierFormula_iff : forall
    (M : RawPAModel) tail sigmaDomain piDomain nextSigma,
  raw_formula_sat M tail
    (dynamicTruthNativeAxiomSoundnessCarrierFormula
      sigmaDomain piDomain nextSigma) <->
  RawDynamicTruthNativeAxiomSoundnessCarrierAt M tail
    sigmaDomain piDomain nextSigma.
Proof.
  intros M tail sigmaDomain piDomain nextSigma.
  unfold dynamicTruthNativeAxiomSoundnessCarrierFormula,
    dynamicTruthNativeAxiomSoundnessCarrierBodyFormula,
    dynamicTruthNativeAxiomLowerAdmissibleFormula,
    RawDynamicTruthNativeAxiomSoundnessCarrierAt.
  cbn [raw_formula_sat].
  split.
  - intros h axiom hrecognized hadequate hdefined hdomain.
    apply (h axiom). split.
    + apply (proj2 (raw_sat_witnessedPAAxiomRecognitionTermAt_iff
        M (scons M axiom tail) (tVar 0))).
      cbn [raw_term_eval scons]. exact hrecognized.
    + split.
      * apply (proj2 (raw_sat_codedFormulaAtomicallyAdequateTermAt_iff
          M (scons M axiom tail) (tVar 0))).
        cbn [raw_term_eval scons]. exact hadequate.
      * split.
        -- apply (proj2
             (raw_sat_codedAssignmentDefinedThroughTermAt_iff M
               tZero tZero (tVar 0) (scons M axiom tail))).
           cbn [raw_term_eval scons]. exact hdefined.
        -- exact hdomain.
  - intros h axiom (hrecognized & hadequate & hdefined & hdomain).
    apply (h axiom).
    + apply (proj1 (raw_sat_witnessedPAAxiomRecognitionTermAt_iff
        M (scons M axiom tail) (tVar 0))) in hrecognized.
      cbn [raw_term_eval scons] in hrecognized. exact hrecognized.
    + apply (proj1 (raw_sat_codedFormulaAtomicallyAdequateTermAt_iff
        M (scons M axiom tail) (tVar 0))) in hadequate.
      cbn [raw_term_eval scons] in hadequate. exact hadequate.
    + apply (proj1
        (raw_sat_codedAssignmentDefinedThroughTermAt_iff M
          tZero tZero (tVar 0) (scons M axiom tail))) in hdefined.
      cbn [raw_term_eval scons] in hdefined. exact hdefined.
    + exact hdomain.
Qed.

Definition RawDynamicTruthNativeAxiomSoundnessFixedLevelAt
    (M : RawPAModel) (currentLevel : nat) : Prop :=
  forall axiom : M,
    RawWitnessedPAAxiomRecognition M axiom ->
    RawFixedLevelTruthAdmissible M currentLevel axiom
      (raw_zero M) (raw_zero M) ->
    RawFixedLevelSigmaTruthCertificate M (S currentLevel) axiom
      (raw_zero M) (raw_zero M).

Arguments RawDynamicTruthNativeAxiomSoundnessFixedLevelAt
  M currentLevel : clear implicits.

Theorem raw_sat_dynamicTruthNativeAxiomSoundnessFixedLevelFormula_iff :
    forall (M : RawPAModel) e currentLevel,
  raw_formula_sat M e
    (dynamicTruthNativeAxiomSoundnessFixedLevelFormula currentLevel) <->
  RawDynamicTruthNativeAxiomSoundnessFixedLevelAt M currentLevel.
Proof.
  intros M e currentLevel.
  unfold dynamicTruthNativeAxiomSoundnessFixedLevelFormula,
    dynamicTruthNativeAxiomSoundnessFixedLevelBodyFormula,
    RawDynamicTruthNativeAxiomSoundnessFixedLevelAt.
  cbn [raw_formula_sat].
  split.
  - intros h axiom hrecognized hadmissible.
    apply (proj1
      (raw_sat_fixedLevelSigmaTruthCertificateTermAt_iff
        (S currentLevel) M (scons M axiom e)
        (tVar 0) tZero tZero)).
    apply (h axiom). split.
    + apply (proj2 (raw_sat_witnessedPAAxiomRecognitionTermAt_iff
        M (scons M axiom e) (tVar 0))).
      cbn [raw_term_eval scons]. exact hrecognized.
    + apply (proj2 (raw_sat_fixedLevelTruthAdmissibleTermAt_iff
        M (scons M axiom e) currentLevel (tVar 0) tZero tZero)).
      cbn [raw_term_eval scons]. exact hadmissible.
  - intros h axiom (hrecognized & hadmissible).
    apply (proj2
      (raw_sat_fixedLevelSigmaTruthCertificateTermAt_iff
        (S currentLevel) M (scons M axiom e)
        (tVar 0) tZero tZero)).
    cbn [raw_term_eval scons]. apply (h axiom).
    + apply (proj1 (raw_sat_witnessedPAAxiomRecognitionTermAt_iff
        M (scons M axiom e) (tVar 0))) in hrecognized.
      cbn [raw_term_eval scons] in hrecognized. exact hrecognized.
    + apply (proj1 (raw_sat_fixedLevelTruthAdmissibleTermAt_iff
        M (scons M axiom e) currentLevel (tVar 0) tZero tZero))
        in hadmissible.
      cbn [raw_term_eval scons] in hadmissible. exact hadmissible.
Qed.

(** At level zero this is semantically exactly the already audited base
    coordinate.  Stating the alignment through the two law-free semantic
    interfaces avoids asking conversion to unfold [sealPA]'s bound over the
    complete represented truth formula. *)
Lemma dynamicTruthNativeAxiomSoundnessFixedLevelFormula_zero :
  forall (M : RawPAModel) e,
  raw_formula_sat M e
    (dynamicTruthNativeAxiomSoundnessFixedLevelFormula 0) <->
  raw_formula_sat M e dynamicTruthAxiomSoundnessBaseFieldFormula.
Proof.
  intros M e.
  rewrite raw_sat_dynamicTruthNativeAxiomSoundnessFixedLevelFormula_iff,
    raw_sat_dynamicTruthAxiomSoundnessBaseFieldFormula_iff.
  unfold RawDynamicTruthNativeAxiomSoundnessFixedLevelAt,
    RawDynamicTruthAxiomSoundnessBaseAt.
  reflexivity.
Qed.

(** The standard law is the genuine fixed-level PA-axiom theorem.  Its
    induction-witness case is supplied by the already proved, all-level
    induction soundness theorem rather than by a semantic assumption. *)
Theorem raw_dynamicTruthNativeAxiomSoundnessFixedLevel_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall currentLevel,
  RawDynamicTruthNativeAxiomSoundnessFixedLevelAt M currentLevel.
Proof.
  intros M hPA currentLevel axiom [witness hwitness] hadmissible.
  exact (raw_codedPAAxiomWitness_sigma_zero M hPA currentLevel
    (raw_fixedLevelPAAxiomInductionSigmaSound_all M hPA currentLevel)
    witness axiom hwitness hadmissible).
Qed.

Theorem dynamicTruthNativeAxiomSoundnessFixedLevelFormula_raw_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall currentLevel e,
  raw_formula_sat M e
    (dynamicTruthNativeAxiomSoundnessFixedLevelFormula currentLevel).
Proof.
  intros M hPA currentLevel e.
  apply (proj2
    (raw_sat_dynamicTruthNativeAxiomSoundnessFixedLevelFormula_iff
      M e currentLevel)).
  exact (raw_dynamicTruthNativeAxiomSoundnessFixedLevel_all
    M hPA currentLevel).
Qed.

Theorem PA_proves_dynamicTruthNativeAxiomSoundnessFixedLevelFormula : forall
    currentLevel,
  Formula.BProv Formula.Ax_s []
    (dynamicTruthNativeAxiomSoundnessFixedLevelFormula currentLevel).
Proof.
  intro currentLevel.
  set (target :=
    dynamicTruthNativeAxiomSoundnessFixedLevelFormula currentLevel).
  assert (hclosed : Formula.BProv Formula.Ax_s []
      (Formula.sealPA target)).
  {
    apply PA_BProv_of_raw_valid.
    - apply Formula.sealPA_sentence.
    - intros M hPA e.
      apply raw_formula_sat_sealPA_of_valid.
      intro inner.
      unfold target.
      exact (dynamicTruthNativeAxiomSoundnessFixedLevelFormula_raw_valid
        M hPA currentLevel inner).
  }
  pose proof (Formula.BProv_sealPA_allE_rename
    Formula.Ax_s [] target (fun n => n) hclosed) as hopen.
  rewrite Formula.rename_id in hopen.
  exact hopen.
Qed.

Theorem raw_dynamicTruthNativeAxiomSoundnessFixedLevel_quoted_proof : forall
    (M : RawPAModel), RawPASatisfies M -> forall currentLevel,
  exists certificate : M,
    RawCodedPAProofOf M
      (rawQuotedFormulaCode M
        (dynamicTruthNativeAxiomSoundnessFixedLevelFormula currentLevel))
      certificate.
Proof.
  intros M hPA currentLevel.
  destruct (raw_codedPAProofOf_of_BProv M hPA
    (dynamicTruthNativeAxiomSoundnessFixedLevelFormula currentLevel)
    (PA_proves_dynamicTruthNativeAxiomSoundnessFixedLevelFormula
      currentLevel)) as [certificate hcertificate].
  exists certificate.
  rewrite rawQuotedFormulaCode_standard by exact hPA.
  exact hcertificate.
Qed.

(** ------------------------------------------------------------------
    Application of the next global Sigma predicate to [(axiom,0,0)].

    The global predicate interface is [#0 = formula], [#1 = assignment
    code], and [#2 = assignment step].  Each represented substitution removes
    free variable zero.  The axiom variable must therefore enter the first
    substitution as [#2]: the two subsequent zero substitutions lower it to
    the surviving [#0].  This is the sequential-substitution realization of
    the generic ternary application at [(#0, 0, 0)]. *)

Definition dynamicTruthNativeAxiomApplicationFirstReplacement : term :=
  tVar 2.
Definition dynamicTruthNativeAxiomApplicationSecondReplacement : term :=
  tZero.
Definition dynamicTruthNativeAxiomApplicationThirdReplacement : term :=
  tZero.

Definition dynamicTruthNativeAxiomApplicationTermAt
    (input output : term) : formula :=
  pEx (pEx
    (pAnd
      (codedFormulaSingleSubstitutionTermAt
        (Term.numeral
          (termCode dynamicTruthNativeAxiomApplicationFirstReplacement))
        (liftTerm 2 input) (tVar 1))
      (pAnd
        (codedFormulaSingleSubstitutionTermAt
          (Term.numeral
            (termCode dynamicTruthNativeAxiomApplicationSecondReplacement))
          (tVar 1) (tVar 0))
        (codedFormulaSingleSubstitutionTermAt
          (Term.numeral
            (termCode dynamicTruthNativeAxiomApplicationThirdReplacement))
          (tVar 0) (liftTerm 2 output))))).

Definition RawDynamicTruthNativeAxiomApplication (M : RawPAModel)
    (input output : M) : Prop :=
  exists first second : M,
    RawCodedFormulaSingleSubstitution M
      (rawNumeralValue M
        (termCode dynamicTruthNativeAxiomApplicationFirstReplacement))
      input first /\
    RawCodedFormulaSingleSubstitution M
      (rawNumeralValue M
        (termCode dynamicTruthNativeAxiomApplicationSecondReplacement))
      first second /\
    RawCodedFormulaSingleSubstitution M
      (rawNumeralValue M
        (termCode dynamicTruthNativeAxiomApplicationThirdReplacement))
      second output.

Arguments RawDynamicTruthNativeAxiomApplication M input output
  : clear implicits.

Theorem raw_sat_dynamicTruthNativeAxiomApplicationTermAt_iff : forall
    (M : RawPAModel) e input output,
  raw_formula_sat M e
    (dynamicTruthNativeAxiomApplicationTermAt input output) <->
  RawDynamicTruthNativeAxiomApplication M
    (raw_term_eval M e input) (raw_term_eval M e output).
Proof.
  intros M e input output.
  unfold dynamicTruthNativeAxiomApplicationTermAt,
    RawDynamicTruthNativeAxiomApplication.
  cbn [raw_formula_sat].
  repeat setoid_rewrite raw_sat_codedFormulaSingleSubstitutionTermAt_iff.
  repeat setoid_rewrite raw_term_eval_numeral.
  repeat setoid_rewrite raw_fixedLevel_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_dynamicTruthNativeAxiomApplication_exists_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall input,
  RawCodedFormulaAtomicallyAdequate M input ->
  exists output,
    RawDynamicTruthNativeAxiomApplication M input output /\
    RawCodedFormulaAtomicallyAdequate M output.
Proof.
  intros M hPA input hinput.
  destruct (raw_codedFormulaSingleSubstitution_three_exists_total M hPA
    input hinput
    (rawNumeralValue M
      (termCode dynamicTruthNativeAxiomApplicationFirstReplacement))
    (raw_zero M) (raw_zero M)
    (raw_dynamicTruthApplication_fixedReplacement_syntax M hPA
      dynamicTruthNativeAxiomApplicationFirstReplacement)
    (rawNumeralValue M
      (termCode dynamicTruthNativeAxiomApplicationSecondReplacement))
    (raw_zero M) (raw_zero M)
    (raw_dynamicTruthApplication_fixedReplacement_syntax M hPA
      dynamicTruthNativeAxiomApplicationSecondReplacement)
    (rawNumeralValue M
      (termCode dynamicTruthNativeAxiomApplicationThirdReplacement))
    (raw_zero M) (raw_zero M)
    (raw_dynamicTruthApplication_fixedReplacement_syntax M hPA
      dynamicTruthNativeAxiomApplicationThirdReplacement)) as
    (first & second & output & hfirst & _hfirstAdequate &
     hsecond & _hsecondAdequate & hthird & houtputAdequate).
  exists output. split; [|exact houtputAdequate].
  exists first, second. repeat split; assumption.
Qed.

Definition standardDynamicTruthNativeAxiomApplication
    (input : formula) : formula :=
  Formula.subst
    (Formula.instTerm dynamicTruthNativeAxiomApplicationThirdReplacement)
    (Formula.subst
      (Formula.instTerm dynamicTruthNativeAxiomApplicationSecondReplacement)
      (Formula.subst
        (Formula.instTerm dynamicTruthNativeAxiomApplicationFirstReplacement)
        input)).

(** Regression guard for the argument order above.  In particular, the
    custom three-opening graph is not application at [(0,0,#0)]. *)
Theorem standardDynamicTruthNativeAxiomApplication_correct_order : forall
    input,
  standardDynamicTruthNativeAxiomApplication input =
  standardTernaryApplication input (tVar 0) tZero tZero.
Proof.
  intro input.
  reflexivity.
Qed.

Theorem raw_dynamicTruthNativeAxiomApplication_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall input,
  RawDynamicTruthNativeAxiomApplication M
    (rawQuotedFormulaCode M input)
    (rawQuotedFormulaCode M
      (standardDynamicTruthNativeAxiomApplication input)).
Proof.
  intros M hPA input.
  unfold standardDynamicTruthNativeAxiomApplication.
  set (first := Formula.subst
    (Formula.instTerm dynamicTruthNativeAxiomApplicationFirstReplacement)
    input).
  set (second := Formula.subst
    (Formula.instTerm dynamicTruthNativeAxiomApplicationSecondReplacement)
    first).
  exists (rawQuotedFormulaCode M first),
    (rawQuotedFormulaCode M second).
  split.
  - rewrite <- (rawQuotedTermCode_standard M hPA
      dynamicTruthNativeAxiomApplicationFirstReplacement).
    exact (raw_codedFormulaSingleSubstitution_standard M hPA
      dynamicTruthNativeAxiomApplicationFirstReplacement input).
  - split.
    + rewrite <- (rawQuotedTermCode_standard M hPA
        dynamicTruthNativeAxiomApplicationSecondReplacement).
      exact (raw_codedFormulaSingleSubstitution_standard M hPA
        dynamicTruthNativeAxiomApplicationSecondReplacement first).
    + rewrite <- (rawQuotedTermCode_standard M hPA
        dynamicTruthNativeAxiomApplicationThirdReplacement).
      exact (raw_codedFormulaSingleSubstitution_standard M hPA
        dynamicTruthNativeAxiomApplicationThirdReplacement second).
Qed.

(** The literal represented output is kept in substitution normal form.
    Identifying the recursive fixed-level truth syntax definitionally with
    the pretty-printed [(axiom,0,0)] instance would force a full recursive
    normalization. *)
Corollary raw_dynamicTruthNativeAxiomApplication_fixedLevelSigma_standard :
  forall (M : RawPAModel), RawPASatisfies M -> forall level,
  RawDynamicTruthNativeAxiomApplication M
    (rawQuotedFormulaCode M
      (fixedLevelSigmaTruthCertificateTermAt level
        (tVar 0) (tVar 1) (tVar 2)))
    (rawQuotedFormulaCode M
      (standardDynamicTruthNativeAxiomApplication
        (fixedLevelSigmaTruthCertificateTermAt level
          (tVar 0) (tVar 1) (tVar 2)))).
Proof.
  intros M hPA level.
  exact (raw_dynamicTruthNativeAxiomApplication_standard M hPA
    (fixedLevelSigmaTruthCertificateTermAt level
      (tVar 0) (tVar 1) (tVar 2))).
Qed.

(** ------------------------------------------------------------------
    Transparent constructor polynomial for the selected sentence. *)

Definition dynamicTruthNativeAxiomLowerAdmissibleCodeTerm
    (sigmaDomain piDomain : term) : term :=
  dynamicTruthLocalFormulaAndCodeTerm
    (Term.numeral
      (formulaCode
        (codedFormulaAtomicallyAdequateTermAt (tVar 0))))
    (dynamicTruthLocalFormulaAndCodeTerm
      (Term.numeral
        (formulaCode
          (codedAssignmentDefinedThroughTermAt tZero tZero (tVar 0))))
      (dynamicTruthLocalFormulaOrCodeTerm sigmaDomain piDomain)).

Definition dynamicTruthNativeAxiomSoundnessFieldCodeTerm
    (sigmaDomain piDomain nextSigma : term) : term :=
  dynamicTruthLocalFormulaAllCodeTerm
    (dynamicTruthLocalFormulaImpCodeTerm
      (dynamicTruthLocalFormulaAndCodeTerm
        (Term.numeral
          (formulaCode
            (witnessedPAAxiomRecognitionTermAt (tVar 0))))
        (dynamicTruthNativeAxiomLowerAdmissibleCodeTerm
          sigmaDomain piDomain))
      nextSigma).

Definition rawDynamicTruthNativeAxiomLowerAdmissibleCode
    (M : RawPAModel) (sigmaDomain piDomain : M) : M :=
  rawFormulaAndCode M
    (rawNumeralValue M
      (formulaCode
        (codedFormulaAtomicallyAdequateTermAt (tVar 0))))
    (rawFormulaAndCode M
      (rawNumeralValue M
        (formulaCode
          (codedAssignmentDefinedThroughTermAt tZero tZero (tVar 0))))
      (rawFormulaOrCode M sigmaDomain piDomain)).

Definition rawDynamicTruthNativeAxiomSoundnessFieldCode
    (M : RawPAModel) (sigmaDomain piDomain nextSigma : M) : M :=
  rawFormulaAllCode M
    (rawFormulaImpCode M
      (rawFormulaAndCode M
        (rawNumeralValue M
          (formulaCode
            (witnessedPAAxiomRecognitionTermAt (tVar 0))))
        (rawDynamicTruthNativeAxiomLowerAdmissibleCode M
          sigmaDomain piDomain))
      nextSigma).

Lemma raw_eval_dynamicTruthNativeAxiomLowerAdmissibleCodeTerm : forall
    (M : RawPAModel) e sigmaDomain piDomain,
  raw_term_eval M e
    (dynamicTruthNativeAxiomLowerAdmissibleCodeTerm sigmaDomain piDomain) =
  rawDynamicTruthNativeAxiomLowerAdmissibleCode M
    (raw_term_eval M e sigmaDomain) (raw_term_eval M e piDomain).
Proof.
  intros.
  unfold dynamicTruthNativeAxiomLowerAdmissibleCodeTerm,
    rawDynamicTruthNativeAxiomLowerAdmissibleCode.
  rewrite !raw_eval_dynamicTruthLocalFormulaAndCodeTerm,
    raw_eval_dynamicTruthLocalFormulaOrCodeTerm,
    !raw_term_eval_numeral. reflexivity.
Qed.

Lemma raw_eval_dynamicTruthNativeAxiomSoundnessFieldCodeTerm : forall
    (M : RawPAModel) e sigmaDomain piDomain nextSigma,
  raw_term_eval M e
    (dynamicTruthNativeAxiomSoundnessFieldCodeTerm
      sigmaDomain piDomain nextSigma) =
  rawDynamicTruthNativeAxiomSoundnessFieldCode M
    (raw_term_eval M e sigmaDomain) (raw_term_eval M e piDomain)
    (raw_term_eval M e nextSigma).
Proof.
  intros.
  unfold dynamicTruthNativeAxiomSoundnessFieldCodeTerm,
    rawDynamicTruthNativeAxiomSoundnessFieldCode.
  rewrite raw_eval_dynamicTruthLocalFormulaAllCodeTerm,
    raw_eval_dynamicTruthLocalFormulaImpCodeTerm,
    raw_eval_dynamicTruthLocalFormulaAndCodeTerm,
    raw_eval_dynamicTruthNativeAxiomLowerAdmissibleCodeTerm,
    raw_term_eval_numeral. reflexivity.
Qed.

Definition dynamicTruthNativeAxiomSoundnessFieldCodeTermAt
    (output sigmaDomain piDomain nextSigma : term) : formula :=
  pEq output
    (dynamicTruthNativeAxiomSoundnessFieldCodeTerm
      sigmaDomain piDomain nextSigma).

Lemma raw_sat_dynamicTruthNativeAxiomSoundnessFieldCodeTermAt_iff : forall
    (M : RawPAModel) e output sigmaDomain piDomain nextSigma,
  raw_formula_sat M e
    (dynamicTruthNativeAxiomSoundnessFieldCodeTermAt
      output sigmaDomain piDomain nextSigma) <->
  raw_term_eval M e output =
    rawDynamicTruthNativeAxiomSoundnessFieldCode M
      (raw_term_eval M e sigmaDomain) (raw_term_eval M e piDomain)
      (raw_term_eval M e nextSigma).
Proof.
  intros.
  unfold dynamicTruthNativeAxiomSoundnessFieldCodeTermAt.
  change (raw_term_eval M e output =
      raw_term_eval M e
        (dynamicTruthNativeAxiomSoundnessFieldCodeTerm
          sigmaDomain piDomain nextSigma) <->
    raw_term_eval M e output =
      rawDynamicTruthNativeAxiomSoundnessFieldCode M
        (raw_term_eval M e sigmaDomain) (raw_term_eval M e piDomain)
        (raw_term_eval M e nextSigma)).
  rewrite raw_eval_dynamicTruthNativeAxiomSoundnessFieldCodeTerm.
  reflexivity.
Qed.

Theorem rawDynamicTruthNativeAxiomSoundnessFieldCode_quoted : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      sigmaDomain piDomain nextSigma,
  rawDynamicTruthNativeAxiomSoundnessFieldCode M
    (rawQuotedFormulaCode M sigmaDomain)
    (rawQuotedFormulaCode M piDomain)
    (rawQuotedFormulaCode M nextSigma) =
  rawQuotedFormulaCode M
    (dynamicTruthNativeAxiomSoundnessCarrierFormula
      sigmaDomain piDomain nextSigma).
Proof.
  intros M hPA sigmaDomain piDomain nextSigma.
  unfold rawDynamicTruthNativeAxiomSoundnessFieldCode,
    rawDynamicTruthNativeAxiomLowerAdmissibleCode,
    dynamicTruthNativeAxiomSoundnessCarrierFormula,
    dynamicTruthNativeAxiomSoundnessCarrierBodyFormula,
    dynamicTruthNativeAxiomLowerAdmissibleFormula.
  rewrite <- (rawQuotedFormulaCode_standard M hPA
    (witnessedPAAxiomRecognitionTermAt (tVar 0))).
  rewrite <- (rawQuotedFormulaCode_standard M hPA
    (codedFormulaAtomicallyAdequateTermAt (tVar 0))).
  rewrite <- (rawQuotedFormulaCode_standard M hPA
    (codedAssignmentDefinedThroughTermAt tZero tZero (tVar 0))).
  reflexivity.
Qed.

Corollary
    rawDynamicTruthNativeAxiomSoundnessFieldCode_quoted_successor_level :
  forall (M : RawPAModel), RawPASatisfies M -> forall predecessor,
  rawDynamicTruthNativeAxiomSoundnessFieldCode M
    (rawQuotedFormulaCode M
      (fixedLevelSigmaDomainTermAt (S predecessor) (tVar 0)))
    (rawQuotedFormulaCode M
      (fixedLevelPiDomainTermAt (S predecessor) (tVar 0)))
    (rawQuotedFormulaCode M
      (fixedLevelSigmaTruthCertificateTermAt
        (S (S predecessor)) (tVar 0) tZero tZero)) =
  rawQuotedFormulaCode M
    (dynamicTruthNativeAxiomSoundnessFixedLevelFormula (S predecessor)).
Proof.
  intros M hPA predecessor.
  rewrite rawDynamicTruthNativeAxiomSoundnessFieldCode_quoted
    by exact hPA.
  rewrite dynamicTruthNativeAxiomSoundnessCarrierFormula_fixedLevel.
  reflexivity.
Qed.

Corollary rawDynamicTruthNativeAxiomSoundnessFieldCode_standard_proof :
  forall (M : RawPAModel), RawPASatisfies M -> forall predecessor,
  exists certificate : M,
    RawCodedPAProofOf M
      (rawDynamicTruthNativeAxiomSoundnessFieldCode M
        (rawQuotedFormulaCode M
          (fixedLevelSigmaDomainTermAt (S predecessor) (tVar 0)))
        (rawQuotedFormulaCode M
          (fixedLevelPiDomainTermAt (S predecessor) (tVar 0)))
        (rawQuotedFormulaCode M
          (fixedLevelSigmaTruthCertificateTermAt
            (S (S predecessor)) (tVar 0) tZero tZero)))
      certificate.
Proof.
  intros M hPA predecessor.
  rewrite
    rawDynamicTruthNativeAxiomSoundnessFieldCode_quoted_successor_level
    by exact hPA.
  exact (raw_dynamicTruthNativeAxiomSoundnessFixedLevel_quoted_proof
    M hPA (S predecessor)).
Qed.

(** ------------------------------------------------------------------
    Genuine current orbit at [S p].

    This is definitionally the input side of the native cross-level graph.
    Reusing it prevents a second, subtly different convention for the
    predecessor/current-level shift. *)

Definition dynamicTruthNativeAxiomSoundnessInputOrbitGraph : formula :=
  dynamicTruthNativeCrossLevelInputOrbitGraph.

Definition RawDynamicTruthNativeAxiomSoundnessInputOrbitAt
    (M : RawPAModel) (tail : nat -> M)
    (predecessorLevel currentGlobalSigma currentGlobalPi : M) : Prop :=
  RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M
    tail (raw_succ M predecessorLevel)
    currentGlobalSigma currentGlobalPi.

Arguments RawDynamicTruthNativeAxiomSoundnessInputOrbitAt
  M tail predecessorLevel currentGlobalSigma currentGlobalPi
  : clear implicits.

Theorem raw_sat_dynamicTruthNativeAxiomSoundnessInputOrbitGraph_iff : forall
    (M : RawPAModel) tail predecessorLevel currentGlobalSigma currentGlobalPi,
  raw_formula_sat M
    (scons M currentGlobalSigma (scons M currentGlobalPi
      (scons M predecessorLevel tail)))
    dynamicTruthNativeAxiomSoundnessInputOrbitGraph <->
  RawDynamicTruthNativeAxiomSoundnessInputOrbitAt M
    tail predecessorLevel currentGlobalSigma currentGlobalPi.
Proof.
  intros.
  unfold dynamicTruthNativeAxiomSoundnessInputOrbitGraph,
    RawDynamicTruthNativeAxiomSoundnessInputOrbitAt.
  exact (raw_sat_dynamicTruthNativeCrossLevelInputOrbitGraph_iff
    M tail predecessorLevel currentGlobalSigma currentGlobalPi).
Qed.

Corollary
    raw_sat_dynamicTruthNativeAxiomSoundnessInputOrbitGraph_standard_iff :
  forall (M : RawPAModel) tail predecessor currentGlobalSigma currentGlobalPi,
  raw_formula_sat M
    (scons M currentGlobalSigma (scons M currentGlobalPi
      (scons M (rawNumeralValue M predecessor) tail)))
    dynamicTruthNativeAxiomSoundnessInputOrbitGraph <->
  RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M
    tail (rawNumeralValue M (S predecessor))
    currentGlobalSigma currentGlobalPi.
Proof.
  intros.
  unfold dynamicTruthNativeAxiomSoundnessInputOrbitGraph.
  exact
    (raw_sat_dynamicTruthNativeCrossLevelInputOrbitGraph_standard_iff
      M tail predecessor currentGlobalSigma currentGlobalPi).
Qed.

(** ------------------------------------------------------------------
    Transform the current pair into the fifth field.

    Beneath the seven existential witnesses the environment is

      nextSigmaEvidence :: piDomain :: sigmaDomain :: currentLevelNumeral ::
      nextGlobalPi :: nextGlobalSigma :: currentLevel :: fieldCode ::
      currentGlobalSigma :: currentGlobalPi :: predecessorLevel :: tail.

    The renamed successor graph consumes the current pair and produces the
    actual next pair.  Only its Sigma component is subsequently applied, but
    retaining the paired successor is essential: it certifies that this is
    the same native [Sigma-Or7/Pi-Or6] recursion as every other master field. *)

Definition dynamicTruthNativeAxiomSoundnessEx7 (body : formula) : formula :=
  pEx (pEx (pEx (pEx (pEx (pEx (pEx body)))))).

Definition dynamicTruthNativeAxiomSoundnessAnd5
    (a b c d e : formula) : formula :=
  pAnd a (pAnd b (pAnd c (pAnd d e))).

Definition dynamicTruthNativeAxiomSoundnessSuccessorRenaming
    (index : nat) : nat :=
  match index with
  | 0 => 5
  | 1 => 4
  | 2 => 8
  | 3 => 9
  | 4 => 6
  | S (S (S (S (S tailIndex)))) => 11 + tailIndex
  end.

Definition dynamicTruthNativeAxiomSoundnessTransformEnvironment
    (M : RawPAModel)
    (nextSigmaEvidence piDomain sigmaDomain currentLevelNumeral
      nextGlobalPi nextGlobalSigma currentLevel fieldCode
      currentGlobalSigma currentGlobalPi predecessorLevel : M)
    (tail : nat -> M) : nat -> M :=
  scons M nextSigmaEvidence (scons M piDomain (scons M sigmaDomain
    (scons M currentLevelNumeral (scons M nextGlobalPi
      (scons M nextGlobalSigma (scons M currentLevel (scons M fieldCode
        (scons M currentGlobalSigma (scons M currentGlobalPi
          (scons M predecessorLevel tail)))))))))).

Definition dynamicTruthNativeAxiomSoundnessSuccessorBodyGraph : formula :=
  Formula.rename dynamicTruthNativeAxiomSoundnessSuccessorRenaming
    dynamicTruthPairedGlobalSuccessorGraph.

Lemma raw_sat_dynamicTruthNativeAxiomSoundnessSuccessorBodyGraph_iff : forall
    (M : RawPAModel) tail nextSigmaEvidence piDomain sigmaDomain
      currentLevelNumeral nextGlobalPi nextGlobalSigma currentLevel fieldCode
      currentGlobalSigma currentGlobalPi predecessorLevel,
  raw_formula_sat M
    (dynamicTruthNativeAxiomSoundnessTransformEnvironment M
      nextSigmaEvidence piDomain sigmaDomain currentLevelNumeral
      nextGlobalPi nextGlobalSigma currentLevel fieldCode
      currentGlobalSigma currentGlobalPi predecessorLevel tail)
    dynamicTruthNativeAxiomSoundnessSuccessorBodyGraph <->
  raw_formula_sat M
    (scons M nextGlobalSigma (scons M nextGlobalPi
      (scons M currentGlobalSigma (scons M currentGlobalPi
        (scons M currentLevel tail)))))
    dynamicTruthPairedGlobalSuccessorGraph.
Proof.
  intros.
  unfold dynamicTruthNativeAxiomSoundnessSuccessorBodyGraph.
  rewrite raw_formula_sat_rename.
  apply raw_formula_sat_ext. intro index.
  destruct index as [|[|[|[|[|tailIndex]]]]];
    cbn [dynamicTruthNativeAxiomSoundnessTransformEnvironment
      dynamicTruthNativeAxiomSoundnessSuccessorRenaming scons]; reflexivity.
Qed.

Local Opaque dynamicTruthNativeAxiomSoundnessSuccessorBodyGraph.
Local Opaque dynamicTruthPairedGlobalSuccessorGraph.
Local Opaque dynamicTruthNativeAxiomApplicationTermAt.

Definition dynamicTruthNativeAxiomSoundnessFieldTransformGraph : formula :=
  dynamicTruthNativeAxiomSoundnessEx7
    (pAnd
      (pEq (tVar 6) (tSucc (tVar 10)))
      (pAnd
        dynamicTruthNativeAxiomSoundnessSuccessorBodyGraph
        (dynamicTruthNativeAxiomSoundnessAnd5
          (numeralTermCodeAtTermAt (tVar 6) (tVar 3))
          (codedFormulaSingleSubstitutionTermAt
            (tVar 3)
            (Term.numeral
              (formulaCode dynamicTruthNativeAxiomSigmaDomainTemplate))
            (tVar 2))
          (codedFormulaSingleSubstitutionTermAt
            (tVar 3)
            (Term.numeral
              (formulaCode dynamicTruthNativeAxiomPiDomainTemplate))
            (tVar 1))
          (dynamicTruthNativeAxiomApplicationTermAt
            (tVar 5) (tVar 0))
          (dynamicTruthNativeAxiomSoundnessFieldCodeTermAt
            (tVar 7) (tVar 2) (tVar 1) (tVar 0))))).

Definition RawDynamicTruthNativeAxiomSoundnessFieldTransformAt
    (M : RawPAModel)
    (currentGlobalSigma currentGlobalPi predecessorLevel fieldCode : M)
    : Prop :=
  exists currentLevel nextGlobalSigma nextGlobalPi currentLevelNumeral
      sigmaDomain piDomain nextSigmaEvidence : M,
    currentLevel = raw_succ M predecessorLevel /\
    RawDynamicTruthPairedGlobalSuccessorAt M
      currentGlobalSigma currentGlobalPi currentLevel
      nextGlobalSigma nextGlobalPi /\
    RawNumeralTermCodeAt M currentLevel currentLevelNumeral /\
    RawCodedFormulaSingleSubstitution M currentLevelNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthNativeAxiomSigmaDomainTemplate))
      sigmaDomain /\
    RawCodedFormulaSingleSubstitution M currentLevelNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthNativeAxiomPiDomainTemplate))
      piDomain /\
    RawDynamicTruthNativeAxiomApplication M
      nextGlobalSigma nextSigmaEvidence /\
    fieldCode = rawDynamicTruthNativeAxiomSoundnessFieldCode M
      sigmaDomain piDomain nextSigmaEvidence.

Arguments RawDynamicTruthNativeAxiomSoundnessFieldTransformAt
  M currentGlobalSigma currentGlobalPi predecessorLevel fieldCode
  : clear implicits.

Theorem raw_sat_dynamicTruthNativeAxiomSoundnessFieldTransformGraph_iff :
  forall (M : RawPAModel) tail currentGlobalSigma currentGlobalPi
      predecessorLevel fieldCode,
  raw_formula_sat M
    (scons M fieldCode (scons M currentGlobalSigma
      (scons M currentGlobalPi (scons M predecessorLevel tail))))
    dynamicTruthNativeAxiomSoundnessFieldTransformGraph <->
  RawDynamicTruthNativeAxiomSoundnessFieldTransformAt M
    currentGlobalSigma currentGlobalPi predecessorLevel fieldCode.
Proof.
  intros M tail currentGlobalSigma currentGlobalPi predecessorLevel fieldCode.
  unfold dynamicTruthNativeAxiomSoundnessFieldTransformGraph,
    RawDynamicTruthNativeAxiomSoundnessFieldTransformAt,
    dynamicTruthNativeAxiomSoundnessEx7,
    dynamicTruthNativeAxiomSoundnessAnd5.
  cbn [raw_formula_sat].
  split.
  - intros (currentLevel & nextGlobalSigma & nextGlobalPi &
      currentLevelNumeral & sigmaDomain & piDomain & nextSigmaEvidence &
      hlevel & hsuccessor & hnumeral & hsigmaDomain & hpiDomain &
      hnextSigma & hfield).
    change (currentLevel = raw_succ M predecessorLevel) in hlevel.
    apply (proj1
      (raw_sat_dynamicTruthNativeAxiomSoundnessSuccessorBodyGraph_iff
        M tail nextSigmaEvidence piDomain sigmaDomain currentLevelNumeral
        nextGlobalPi nextGlobalSigma currentLevel fieldCode
        currentGlobalSigma currentGlobalPi predecessorLevel)) in hsuccessor.
    apply (proj1
      (raw_sat_dynamicTruthPairedGlobalSuccessorGraph_iff M tail currentLevel
        currentGlobalSigma currentGlobalPi nextGlobalSigma nextGlobalPi))
      in hsuccessor.
    apply (proj1 (raw_sat_numeralTermCodeAtTermAt_iff M _
      (tVar 6) (tVar 3))) in hnumeral.
    cbn [raw_term_eval scons] in hnumeral.
    apply (proj1 (raw_sat_codedFormulaSingleSubstitutionTermAt_iff M _
      (tVar 3)
      (Term.numeral
        (formulaCode dynamicTruthNativeAxiomSigmaDomainTemplate))
      (tVar 2))) in hsigmaDomain.
    rewrite raw_term_eval_numeral in hsigmaDomain.
    cbn [raw_term_eval scons] in hsigmaDomain.
    apply (proj1 (raw_sat_codedFormulaSingleSubstitutionTermAt_iff M _
      (tVar 3)
      (Term.numeral
        (formulaCode dynamicTruthNativeAxiomPiDomainTemplate))
      (tVar 1))) in hpiDomain.
    rewrite raw_term_eval_numeral in hpiDomain.
    cbn [raw_term_eval scons] in hpiDomain.
    apply (proj1 (raw_sat_dynamicTruthNativeAxiomApplicationTermAt_iff
      M _ (tVar 5) (tVar 0))) in hnextSigma.
    cbn [raw_term_eval scons] in hnextSigma.
    apply (proj1
      (raw_sat_dynamicTruthNativeAxiomSoundnessFieldCodeTermAt_iff M _
        (tVar 7) (tVar 2) (tVar 1) (tVar 0))) in hfield.
    cbn [raw_term_eval scons] in hfield.
    exists currentLevel, nextGlobalSigma, nextGlobalPi, currentLevelNumeral,
      sigmaDomain, piDomain, nextSigmaEvidence.
    repeat split; assumption.
  - intros (currentLevel & nextGlobalSigma & nextGlobalPi &
      currentLevelNumeral & sigmaDomain & piDomain & nextSigmaEvidence &
      hlevel & hsuccessor & hnumeral & hsigmaDomain & hpiDomain &
      hnextSigma & hfield).
    exists currentLevel, nextGlobalSigma, nextGlobalPi, currentLevelNumeral,
      sigmaDomain, piDomain, nextSigmaEvidence.
    repeat split.
    + change (currentLevel = raw_succ M predecessorLevel). exact hlevel.
    + apply (proj2
        (raw_sat_dynamicTruthNativeAxiomSoundnessSuccessorBodyGraph_iff
          M tail nextSigmaEvidence piDomain sigmaDomain currentLevelNumeral
          nextGlobalPi nextGlobalSigma currentLevel fieldCode
          currentGlobalSigma currentGlobalPi predecessorLevel)).
      apply (proj2
        (raw_sat_dynamicTruthPairedGlobalSuccessorGraph_iff M tail
          currentLevel currentGlobalSigma currentGlobalPi
          nextGlobalSigma nextGlobalPi)).
      exact hsuccessor.
    + apply (proj2 (raw_sat_numeralTermCodeAtTermAt_iff M _
        (tVar 6) (tVar 3))).
      cbn [raw_term_eval scons]. exact hnumeral.
    + apply (proj2
        (raw_sat_codedFormulaSingleSubstitutionTermAt_iff M _
          (tVar 3)
          (Term.numeral
            (formulaCode dynamicTruthNativeAxiomSigmaDomainTemplate))
          (tVar 2))).
      rewrite raw_term_eval_numeral.
      cbn [raw_term_eval scons]. exact hsigmaDomain.
    + apply (proj2
        (raw_sat_codedFormulaSingleSubstitutionTermAt_iff M _
          (tVar 3)
          (Term.numeral
            (formulaCode dynamicTruthNativeAxiomPiDomainTemplate))
          (tVar 1))).
      rewrite raw_term_eval_numeral.
      cbn [raw_term_eval scons]. exact hpiDomain.
    + apply (proj2
        (raw_sat_dynamicTruthNativeAxiomApplicationTermAt_iff
          M _ (tVar 5) (tVar 0))).
      cbn [raw_term_eval scons]. exact hnextSigma.
    + apply (proj2
        (raw_sat_dynamicTruthNativeAxiomSoundnessFieldCodeTermAt_iff M _
          (tVar 7) (tVar 2) (tVar 1) (tVar 0))).
      cbn [raw_term_eval scons]. exact hfield.
Qed.

(** The semantic trace exposes the actual native paired successor rows. *)
Theorem
    raw_dynamicTruthNativeAxiomSoundnessFieldTransformAt_exposes_rows :
  forall (M : RawPAModel) currentGlobalSigma currentGlobalPi
      predecessorLevel fieldCode,
  RawDynamicTruthNativeAxiomSoundnessFieldTransformAt M
    currentGlobalSigma currentGlobalPi predecessorLevel fieldCode ->
  exists currentLevel nextGlobalSigma nextGlobalPi localSigmaRow localPiRow,
    currentLevel = raw_succ M predecessorLevel /\
    RawDynamicTruthPairedSuccessorRowAt M
      currentGlobalSigma currentGlobalPi currentLevel
      localSigmaRow localPiRow /\
    RawDynamicTruthPairedGlobalWrapperAt M
      localSigmaRow localPiRow nextGlobalSigma nextGlobalPi.
Proof.
  intros M currentGlobalSigma currentGlobalPi predecessorLevel fieldCode
    (currentLevel & nextGlobalSigma & nextGlobalPi & currentLevelNumeral &
     sigmaDomain & piDomain & nextSigmaEvidence & hlevel & hsuccessor & _).
  destruct hsuccessor as
    [localSigmaRow [localPiRow [hrows hwrapper]]].
  exists currentLevel, nextGlobalSigma, nextGlobalPi,
    localSigmaRow, localPiRow.
  split; [exact hlevel |].
  split; [exact hrows | exact hwrapper].
Qed.

(** Structural closure preserves the formula-code invariant required by the
    carrier orbit induction. *)
Lemma rawDynamicTruthNativeAxiomSoundnessFieldCode_atomically_adequate :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      sigmaDomain piDomain nextSigma,
  RawCodedFormulaAtomicallyAdequate M sigmaDomain ->
  RawCodedFormulaAtomicallyAdequate M piDomain ->
  RawCodedFormulaAtomicallyAdequate M nextSigma ->
  RawCodedFormulaAtomicallyAdequate M
    (rawDynamicTruthNativeAxiomSoundnessFieldCode M
      sigmaDomain piDomain nextSigma).
Proof.
  intros M hPA sigmaDomain piDomain nextSigma
    hsigmaDomain hpiDomain hnextSigma.
  unfold rawDynamicTruthNativeAxiomSoundnessFieldCode,
    rawDynamicTruthNativeAxiomLowerAdmissibleCode.
  apply raw_formulaAllCode_atomically_adequate; [exact hPA |].
  apply raw_formulaImpCode_atomically_adequate; [exact hPA | |].
  - apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
    + exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
        (witnessedPAAxiomRecognitionTermAt (tVar 0))).
    + apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
      * exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
          (codedFormulaAtomicallyAdequateTermAt (tVar 0))).
      * apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
        -- exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
             (codedAssignmentDefinedThroughTermAt tZero tZero (tVar 0))).
        -- apply raw_formulaOrCode_atomically_adequate;
             [exact hPA | exact hsigmaDomain | exact hpiDomain].
  - exact hnextSigma.
Qed.

Definition RawDynamicTruthNativeAxiomSoundnessFieldTransformTotalOnAdequate
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) currentGlobalSigma currentGlobalPi
      predecessorLevel,
    RawCodedFormulaAtomicallyAdequate M currentGlobalSigma ->
    RawCodedFormulaAtomicallyAdequate M currentGlobalPi ->
    exists fieldCode : M,
      raw_formula_sat M
        (scons M fieldCode (scons M currentGlobalSigma
          (scons M currentGlobalPi (scons M predecessorLevel tail))))
        dynamicTruthNativeAxiomSoundnessFieldTransformGraph /\
      RawCodedFormulaAtomicallyAdequate M fieldCode.

Arguments RawDynamicTruthNativeAxiomSoundnessFieldTransformTotalOnAdequate M
  : clear implicits.

Theorem
    dynamicTruthNativeAxiomSoundnessFieldTransformGraph_raw_total_on_adequate :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeAxiomSoundnessFieldTransformTotalOnAdequate M.
Proof.
  intros M hPA tail currentGlobalSigma currentGlobalPi predecessorLevel
    hcurrentSigma hcurrentPi.
  set (currentLevel := raw_succ M predecessorLevel).
  destruct (dynamicTruthPairedGlobalSuccessorGraph_raw_adequate_total
    M hPA tail currentLevel currentGlobalSigma currentGlobalPi
    hcurrentSigma hcurrentPi) as
    (nextGlobalSigma & nextGlobalPi & hsuccessor &
     hnextSigma & _hnextPi).
  pose proof (proj1
    (raw_sat_dynamicTruthPairedGlobalSuccessorGraph_iff M tail currentLevel
      currentGlobalSigma currentGlobalPi nextGlobalSigma nextGlobalPi)
    hsuccessor) as hsuccessorAt.
  destruct (raw_numeralTermCodeExists_all M hPA currentLevel) as
    [currentLevelNumeral hcurrentLevelNumeral].
  destruct (raw_dynamicTruthLocalInputDomain_exists_adequate
    M hPA currentLevel currentLevelNumeral
    dynamicTruthNativeAxiomSigmaDomainTemplate hcurrentLevelNumeral) as
    (sigmaDomain & hsigmaDomain & hsigmaDomainAdequate).
  destruct (raw_dynamicTruthLocalInputDomain_exists_adequate
    M hPA currentLevel currentLevelNumeral
    dynamicTruthNativeAxiomPiDomainTemplate hcurrentLevelNumeral) as
    (piDomain & hpiDomain & hpiDomainAdequate).
  destruct (raw_dynamicTruthNativeAxiomApplication_exists_adequate
    M hPA nextGlobalSigma hnextSigma) as
    (nextSigmaEvidence & hnextSigmaApplication &
     hnextSigmaEvidenceAdequate).
  exists (rawDynamicTruthNativeAxiomSoundnessFieldCode M
    sigmaDomain piDomain nextSigmaEvidence).
  split.
  - apply (proj2
      (raw_sat_dynamicTruthNativeAxiomSoundnessFieldTransformGraph_iff
        M tail currentGlobalSigma currentGlobalPi predecessorLevel _)).
    exists currentLevel, nextGlobalSigma, nextGlobalPi, currentLevelNumeral,
      sigmaDomain, piDomain, nextSigmaEvidence.
    split; [unfold currentLevel; reflexivity |].
    split; [exact hsuccessorAt |].
    split; [exact hcurrentLevelNumeral |].
    split; [exact hsigmaDomain |].
    split; [exact hpiDomain |].
    split; [exact hnextSigmaApplication | reflexivity].
  - exact
      (rawDynamicTruthNativeAxiomSoundnessFieldCode_atomically_adequate
        M hPA sigmaDomain piDomain nextSigmaEvidence
        hsigmaDomainAdequate hpiDomainAdequate
        hnextSigmaEvidenceAdequate).
Qed.

(** ------------------------------------------------------------------
    Output-first positive graph and totality. *)

Definition dynamicTruthNativeAxiomSoundnessPositiveGraph : formula :=
  outputFirstPairedFormulaGraphComposition
    dynamicTruthNativeAxiomSoundnessInputOrbitGraph
    dynamicTruthNativeAxiomSoundnessFieldTransformGraph.

Definition RawDynamicTruthNativeAxiomSoundnessPositiveAt
    (M : RawPAModel) (tail : nat -> M)
    (predecessorLevel fieldCode : M) : Prop :=
  exists currentGlobalSigma currentGlobalPi : M,
    RawDynamicTruthPairedGlobalFormulaCodeOrbitAt M
      tail (raw_succ M predecessorLevel)
      currentGlobalSigma currentGlobalPi /\
    RawDynamicTruthNativeAxiomSoundnessFieldTransformAt M
      currentGlobalSigma currentGlobalPi predecessorLevel fieldCode.

Arguments RawDynamicTruthNativeAxiomSoundnessPositiveAt
  M tail predecessorLevel fieldCode : clear implicits.

Theorem raw_sat_dynamicTruthNativeAxiomSoundnessPositiveGraph_iff : forall
    (M : RawPAModel) tail predecessorLevel fieldCode,
  raw_formula_sat M
    (scons M fieldCode (scons M predecessorLevel tail))
    dynamicTruthNativeAxiomSoundnessPositiveGraph <->
  RawDynamicTruthNativeAxiomSoundnessPositiveAt M
    tail predecessorLevel fieldCode.
Proof.
  intros M tail predecessorLevel fieldCode.
  unfold dynamicTruthNativeAxiomSoundnessPositiveGraph,
    RawDynamicTruthNativeAxiomSoundnessPositiveAt.
  rewrite raw_sat_outputFirstPairedFormulaGraphComposition_iff.
  unfold RawOutputFirstPairedFormulaGraphCompositionAt.
  split.
  - intros (currentGlobalSigma & currentGlobalPi & horbit & htransform).
    exists currentGlobalSigma, currentGlobalPi. split.
    + apply (proj1
        (raw_sat_dynamicTruthNativeAxiomSoundnessInputOrbitGraph_iff
          M tail predecessorLevel currentGlobalSigma currentGlobalPi)).
      exact horbit.
    + apply (proj1
        (raw_sat_dynamicTruthNativeAxiomSoundnessFieldTransformGraph_iff
          M tail currentGlobalSigma currentGlobalPi predecessorLevel
          fieldCode)).
      exact htransform.
  - intros (currentGlobalSigma & currentGlobalPi & horbit & htransform).
    exists currentGlobalSigma, currentGlobalPi. split.
    + apply (proj2
        (raw_sat_dynamicTruthNativeAxiomSoundnessInputOrbitGraph_iff
          M tail predecessorLevel currentGlobalSigma currentGlobalPi)).
      exact horbit.
    + apply (proj2
        (raw_sat_dynamicTruthNativeAxiomSoundnessFieldTransformGraph_iff
          M tail currentGlobalSigma currentGlobalPi predecessorLevel
          fieldCode)).
      exact htransform.
Qed.

Definition RawDynamicTruthNativeAxiomSoundnessPositiveAdequateTotal
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel,
    exists fieldCode : M,
      raw_formula_sat M
        (scons M fieldCode (scons M predecessorLevel tail))
        dynamicTruthNativeAxiomSoundnessPositiveGraph /\
      RawCodedFormulaAtomicallyAdequate M fieldCode.

Arguments RawDynamicTruthNativeAxiomSoundnessPositiveAdequateTotal M
  : clear implicits.

Theorem dynamicTruthNativeAxiomSoundnessPositiveGraph_raw_adequate_total :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeAxiomSoundnessPositiveAdequateTotal M.
Proof.
  intros M hPA tail predecessorLevel.
  destruct
    (dynamicTruthPairedGlobalFormulaCodeOrbitGraph_raw_adequate_total
      M hPA tail (raw_succ M predecessorLevel)) as
    (currentGlobalSigma & currentGlobalPi & horbit &
     hcurrentSigma & hcurrentPi).
  destruct
    (dynamicTruthNativeAxiomSoundnessFieldTransformGraph_raw_total_on_adequate
      M hPA tail currentGlobalSigma currentGlobalPi predecessorLevel
      hcurrentSigma hcurrentPi) as
    (fieldCode & htransform & hfieldAdequate).
  exists fieldCode. split; [|exact hfieldAdequate].
  apply (proj2
    (raw_sat_dynamicTruthNativeAxiomSoundnessPositiveGraph_iff
      M tail predecessorLevel fieldCode)).
  exists currentGlobalSigma, currentGlobalPi. split.
  - apply (proj1
      (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff M tail
        (raw_succ M predecessorLevel)
        currentGlobalSigma currentGlobalPi)).
    exact horbit.
  - apply (proj1
      (raw_sat_dynamicTruthNativeAxiomSoundnessFieldTransformGraph_iff
        M tail currentGlobalSigma currentGlobalPi predecessorLevel
        fieldCode)).
    exact htransform.
Qed.

Definition RawDynamicTruthNativeAxiomSoundnessPositiveTotal
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel,
    exists fieldCode : M,
      raw_formula_sat M
        (scons M fieldCode (scons M predecessorLevel tail))
        dynamicTruthNativeAxiomSoundnessPositiveGraph.

Arguments RawDynamicTruthNativeAxiomSoundnessPositiveTotal M
  : clear implicits.

Corollary dynamicTruthNativeAxiomSoundnessPositiveGraph_raw_total :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeAxiomSoundnessPositiveTotal M.
Proof.
  intros M hPA tail predecessorLevel.
  destruct
    (dynamicTruthNativeAxiomSoundnessPositiveGraph_raw_adequate_total
      M hPA tail predecessorLevel) as (fieldCode & hfield & _).
  now exists fieldCode.
Qed.

(** ------------------------------------------------------------------
    Exact remaining arbitrary-carrier proof compiler.

    [rawDynamicTruthNativeAxiomSoundnessFieldCode_standard_proof] supplies a
    genuine represented proof for the propositionally aligned fixed field
    polynomial at every external natural predecessor.  For a nonstandard
    carrier predecessor, the following interface asks only for compilation
    on the exact adequate orbit and exact literal transform trace.  It has no
    semantic-validity premise. *)

Definition RawDynamicTruthNativeAxiomSoundnessProofCompiler
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi fieldCode,
    RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
      tail (raw_succ M predecessorLevel)
      currentGlobalSigma currentGlobalPi ->
    RawDynamicTruthNativeAxiomSoundnessFieldTransformAt M
      currentGlobalSigma currentGlobalPi predecessorLevel fieldCode ->
    exists certificate : M,
      RawCodedPAProofOf M fieldCode certificate.

Arguments RawDynamicTruthNativeAxiomSoundnessProofCompiler M
  : clear implicits.

Definition RawDynamicTruthNativeAxiomSoundnessPositiveProofTotal
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel,
    exists fieldCode certificate : M,
      raw_formula_sat M
        (scons M fieldCode (scons M predecessorLevel tail))
        dynamicTruthNativeAxiomSoundnessPositiveGraph /\
      RawCodedFormulaAtomicallyAdequate M fieldCode /\
      RawCodedPAProofOf M fieldCode certificate.

Arguments RawDynamicTruthNativeAxiomSoundnessPositiveProofTotal M
  : clear implicits.

Theorem
    dynamicTruthNativeAxiomSoundnessPositiveGraph_raw_proof_total_of_compiler :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeAxiomSoundnessProofCompiler M ->
  RawDynamicTruthNativeAxiomSoundnessPositiveProofTotal M.
Proof.
  intros M hPA hcompiler tail predecessorLevel.
  destruct
    (dynamicTruthPairedGlobalFormulaCodeOrbitGraph_raw_adequate_total
      M hPA tail (raw_succ M predecessorLevel)) as
    (currentGlobalSigma & currentGlobalPi & horbit &
     hcurrentSigma & hcurrentPi).
  assert (hadequateOrbit :
      RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
        tail (raw_succ M predecessorLevel)
        currentGlobalSigma currentGlobalPi).
  {
    apply (proj2
      (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M tail
        (raw_succ M predecessorLevel)
        currentGlobalSigma currentGlobalPi)).
    split.
    - apply (proj1
        (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff M tail
          (raw_succ M predecessorLevel)
          currentGlobalSigma currentGlobalPi)).
      exact horbit.
    - split; assumption.
  }
  destruct
    (dynamicTruthNativeAxiomSoundnessFieldTransformGraph_raw_total_on_adequate
      M hPA tail currentGlobalSigma currentGlobalPi predecessorLevel
      hcurrentSigma hcurrentPi) as
    (fieldCode & htransformSat & hfieldAdequate).
  pose proof (proj1
    (raw_sat_dynamicTruthNativeAxiomSoundnessFieldTransformGraph_iff
      M tail currentGlobalSigma currentGlobalPi predecessorLevel fieldCode)
    htransformSat) as htransform.
  destruct (hcompiler tail predecessorLevel currentGlobalSigma
    currentGlobalPi fieldCode hadequateOrbit htransform) as
    [certificate hcertificate].
  exists fieldCode, certificate.
  split.
  - apply (proj2
      (raw_sat_dynamicTruthNativeAxiomSoundnessPositiveGraph_iff
        M tail predecessorLevel fieldCode)).
    exists currentGlobalSigma, currentGlobalPi. split.
    + apply (proj1
        (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M tail
          (raw_succ M predecessorLevel)
          currentGlobalSigma currentGlobalPi)).
      exact hadequateOrbit.
    + exact htransform.
  - split; assumption.
Qed.

End PABoundedRawCodedDynamicTruthNativeAxiomSoundnessPositiveGraph.
