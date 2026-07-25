(**
  Internalize one universally quantified PA theorem, then instantiate it
  inside the model at an arbitrary carrier element.

  This is the general engine for producing a model-coded PA proof of a
  substantive statement at a *possibly nonstandard* parameter, without any
  external recursion over that parameter.  It has exactly two moves.

  First, the first derivability condition.  [raw_codedPAProofOf_of_BProv]
  turns a single metatheoretic PA theorem into a coded proof inside every PA
  model.  Crucially the theorem internalized here is one fixed sentence
  [pAll phi], not a family indexed by a metatheoretic natural number, so this
  step is performed once.

  Second, model-internal universal elimination.  [raw_codedPALocalProofOf_allE]
  accepts an entirely arbitrary carrier element as the replacement; nothing in
  it is standard.  Composing the two therefore converts

      "PA proves forall x, phi(x)"                       (external, one sentence)

  into

      "in every PA model, at every carrier element r, there is a coded PA
       proof of phi(r)"                                  (internal, uniform)

  which is precisely the escape from the external-recursion trap.

  Two limits of the engine are recorded honestly below.

  (1) Its input premise must be a genuine PA theorem.  For the six-premise
      dynamic-soundness source this premise is [PA |- forall n, DS(n)], which
      Goedel's second theorem refutes.  The final corollary states that
      application exactly, and is labelled as a diagnosis rather than as
      progress: it is a conditional whose hypothesis is known to fail.  The
      engine is nevertheless the right tool for those ingredients whose
      uniform version is *not* blocked.

  (2) Its output lives in the witnessed-axiom context produced by the first
      derivability condition, not in a context prescribed by the caller.
      Transplanting a coded proof into a prescribed context is a separate
      missing lemma (coded-proof weakening), because every node code in this
      formalism stores its own context.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawModelCompleteness
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedFormulaOperationsStandardRealization
  RawCodedNumeralTermCode
  RawCodedRestrictedPAProof
  RawCodedPAProvability
  RawCodedProofAllEConstructor
  RawCodedPALocalProofExistential
  RawCodedPALocalProofUniversalElimination
  RawCodedRestrictedPADynamicSoundnessComposition
  RawCodedRestrictedPADynamicSoundnessSource
  RawCodedRestrictedPADynamicSoundnessSubstitution.

Import ListNotations.

Module PABoundedRawCodedPAInternalizedUniversalInstance.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaOperationsStandardRealization.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedProofAllEConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofUniversalElimination.
Import PABoundedRawCodedRestrictedPADynamicSoundnessComposition.
Import PABoundedRawCodedRestrictedPADynamicSoundnessSource.
Import PABoundedRawCodedRestrictedPADynamicSoundnessSubstitution.

(** Quotation commutes with the universal constructor by definition. *)
Lemma rawQuotedFormulaCode_all : forall (M : RawPAModel) phi,
  rawQuotedFormulaCode M (pAll phi) =
  rawFormulaAllCode M (rawQuotedFormulaCode M phi).
Proof. reflexivity. Qed.

(** The engine, in local-proof form.  The witnessed-axiom context is exposed
    so that a caller can see exactly which context the produced derivation
    lives in. *)
Theorem raw_codedPALocalProofOf_internalized_universal_instance : forall
    (M : RawPAModel), RawPASatisfies M -> forall phi,
  Formula.BProv Formula.Ax_s [] (pAll phi) ->
  forall replacement instance : M,
  RawCodedFormulaSingleSubstitution M replacement
    (rawQuotedFormulaCode M phi) instance ->
  exists witnessList context child : M,
    RawCodedPAAxiomWitnessContext M witnessList context /\
    RawCodedPALocalProofOf M context instance child.
Proof.
  intros M hPA phi hprov replacement instance hsubstitution.
  destruct (raw_codedPAProofOf_of_BProv M hPA (pAll phi) hprov)
    as [certificate hcertificate].
  destruct hcertificate as
    (witnessList & proof & context &
      _hview & hwitness & hcoverage & hendpoint).
  assert (hall : RawCodedPALocalProofOf M context
      (rawFormulaAllCode M (rawQuotedFormulaCode M phi)) proof).
  {
    split; [exact hcoverage |].
    rewrite <- rawQuotedFormulaCode_all.
    rewrite (rawQuotedFormulaCode_standard M hPA (pAll phi)).
    exact hendpoint.
  }
  exists witnessList, context,
    (rawProofAllERoot M context (rawQuotedFormulaCode M phi)
      replacement proof).
  split; [exact hwitness |].
  exact (raw_codedPALocalProofOf_allE M hPA context
    (rawQuotedFormulaCode M phi) replacement instance proof
    hall hsubstitution).
Qed.

(** The same engine repackaged as an ordinary PA proof certificate. *)
Theorem raw_codedPAProofOf_internalized_universal_instance : forall
    (M : RawPAModel), RawPASatisfies M -> forall phi,
  Formula.BProv Formula.Ax_s [] (pAll phi) ->
  forall replacement instance : M,
  RawCodedFormulaSingleSubstitution M replacement
    (rawQuotedFormulaCode M phi) instance ->
  exists certificate : M, RawCodedPAProofOf M instance certificate.
Proof.
  intros M hPA phi hprov replacement instance hsubstitution.
  destruct (raw_codedPALocalProofOf_internalized_universal_instance
    M hPA phi hprov replacement instance hsubstitution)
    as (witnessList & context & child & hwitness & hcoverage & hendpoint).
  eexists.
  exists witnessList, child, context.
  split; [reflexivity |].
  split; [exact hwitness |].
  split; [exact hcoverage |].
  exact hendpoint.
Qed.

(** ** A fully closed demonstration at an arbitrary carrier element

    [pAll (pEq (tVar 0) (tVar 0))] is a closed PA theorem.  Internalizing it
    once and eliminating its quantifier inside the model yields a coded PA
    proof of its instance at *any* element of the carrier — in particular at
    a nonstandard one.  No metatheoretic recursion over the element occurs,
    and no standardness hypothesis appears in the statement. *)
Definition universalSelfEqualityFormula : formula :=
  pAll (pEq (tVar 0) (tVar 0)).

Lemma universalSelfEqualityFormula_sentence :
  Formula.Sentence universalSelfEqualityFormula.
Proof.
  intros n hn. cbn in hn. destruct hn as [hn | hn]; discriminate hn.
Qed.

Lemma PA_BProv_universalSelfEqualityFormula :
  Formula.BProv Formula.Ax_s [] universalSelfEqualityFormula.
Proof.
  apply PA_BProv_of_raw_valid.
  - exact universalSelfEqualityFormula_sentence.
  - intros M hPA e. cbn. intro x. reflexivity.
Qed.

Theorem raw_codedPAProofOf_selfEquality_at_arbitrary_element : forall
    (M : RawPAModel), RawPASatisfies M -> forall replacement instance : M,
  RawCodedFormulaSingleSubstitution M replacement
    (rawQuotedFormulaCode M (pEq (tVar 0) (tVar 0))) instance ->
  exists certificate : M, RawCodedPAProofOf M instance certificate.
Proof.
  intros M hPA replacement instance hsubstitution.
  exact (raw_codedPAProofOf_internalized_universal_instance M hPA
    (pEq (tVar 0) (tVar 0)) PA_BProv_universalSelfEqualityFormula
    replacement instance hsubstitution).
Qed.

(** ** Diagnosis: the engine applied to the dynamic-soundness source

    The nonstandard substitution certificate needed by the engine already
    exists for the dynamic-soundness source formula, at every numeral term
    code.  So the engine applies verbatim, and pins the missing ingredient to
    a single external premise.

    That premise is [PA |- forall n, DS(n)].  It is refutable: it entails
    consistency of PA, contradicting Goedel's second theorem.  The corollary
    is therefore recorded as a diagnosis of *which* external theorem the
    engine would need here, not as a reduction.  No file depends on it.

    The productive reading is the contrapositive of the design rule: apply
    this engine only to ingredients whose uniform version is not blocked —
    the Tarski, shift and substitution laws relative to a given truth
    predicate — and never to soundness itself. *)
Corollary raw_codedPAProofOf_dynamicSoundnessImplication_of_blocked_uniform_source
    : Formula.BProv Formula.Ax_s []
        (pAll restrictedPADynamicSoundnessSourceFormula) ->
  forall (M : RawPAModel), RawPASatisfies M -> forall numeralBound numeralCode,
  RawNumeralTermCodeAt M numeralBound numeralCode ->
  exists certificate : M,
    RawCodedPAProofOf M
      (rawRestrictedPADynamicSoundnessImplicationCode M numeralCode)
      certificate.
Proof.
  intros hblocked M hPA numeralBound numeralCode hnumeral.
  apply (raw_codedPAProofOf_internalized_universal_instance M hPA
    restrictedPADynamicSoundnessSourceFormula hblocked numeralCode).
  exact (raw_codedRestrictedPADynamicSoundnessSource_substitution
    M hPA numeralBound numeralCode hnumeral).
Qed.

End PABoundedRawCodedPAInternalizedUniversalInstance.
