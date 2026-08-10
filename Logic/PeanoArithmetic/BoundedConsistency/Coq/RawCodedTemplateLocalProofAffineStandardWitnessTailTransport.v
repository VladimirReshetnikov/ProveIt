(**
  Affine-context transport and composition for standard witnessed tails.

  Direct rule-case compilers all have the same metatheoretic shape: given an
  existing finite batch of standard-PA axiom witnesses, choose a finite suffix
  on which a represented local proof exists.  Independent compilers may choose
  different suffixes, so their outputs cannot simply be paired.  The first
  part of this module abstracts the common append-stability argument and gives
  generic conjunction and continuation combinators.

  The second part lifts the existing local-proof transport theorem through an
  arbitrary affine template-context constructor.  A client proves only

      contextAt (embed witnesses) = contextAt [] ++ embed witnesses,

  after which every represented proof of a fixed formula below [contextAt] is
  automatically append-stable.  This removes rule-specific copies of the
  witness-tail transport proof.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedPALocalProofExistential
  RawCodedPAAxiomWitnessPrefix
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedTemplateLocalProofStandardWitnessTailTransport.

Import ListNotations.

Module PABoundedRawCodedTemplateLocalProofAffineStandardWitnessTailTransport.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedCodedProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.

(** A predicate on witness batches is append-stable when already compiled
    evidence survives every later finite witness suffix. *)
Definition RawCoqStandardWitnessTailAppendStable
    (P : StandardPAAxiomWitnessPrefix -> Prop) : Prop :=
  forall witnesses suffix, P witnesses -> P (witnesses ++ suffix).

(** A tail compiler may inspect an arbitrary existing batch and choose one
    further finite suffix on which its target predicate holds. *)
Definition RawCoqStandardWitnessTailCompiler
    (P : StandardPAAxiomWitnessPrefix -> Prop) : Prop :=
  forall baseWitnesses,
  exists suffix, P (baseWitnesses ++ suffix).

Arguments RawCoqStandardWitnessTailAppendStable P : clear implicits.
Arguments RawCoqStandardWitnessTailCompiler P : clear implicits.

(** Append-stability is closed under conjunction.  This lets a synchronized
    batch of already compiled roots be transported as one continuation input. *)
Theorem raw_coqStandardWitnessTailAppendStable_and : forall P Q,
  RawCoqStandardWitnessTailAppendStable P ->
  RawCoqStandardWitnessTailAppendStable Q ->
  RawCoqStandardWitnessTailAppendStable
    (fun witnesses => P witnesses /\ Q witnesses).
Proof.
  intros P Q hP hQ witnesses suffix [hp hq].
  split.
  - exact (hP witnesses suffix hp).
  - exact (hQ witnesses suffix hq).
Qed.

(** Synchronize two independently chosen suffixes.  Only the earlier
    predicate needs append-stability: the second compiler is run after the
    first suffix has already been selected. *)
Theorem raw_coqStandardWitnessTailCompiler_and : forall P Q,
  RawCoqStandardWitnessTailAppendStable P ->
  RawCoqStandardWitnessTailCompiler P ->
  RawCoqStandardWitnessTailCompiler Q ->
  RawCoqStandardWitnessTailCompiler (fun witnesses => P witnesses /\ Q witnesses).
Proof.
  intros P Q hstable hP hQ baseWitnesses.
  destruct (hP baseWitnesses) as [pSuffix hp].
  destruct (hQ (baseWitnesses ++ pSuffix)) as [qSuffix hq].
  exists (pSuffix ++ qSuffix).
  rewrite app_assoc.
  split.
  - exact (hstable (baseWitnesses ++ pSuffix) qSuffix hp).
  - exact hq.
Qed.

(** Apply an independently compiled continuation after its input evidence.
    The input is transported across the continuation's newly chosen suffix;
    the continuation itself never needs to be transported. *)
Theorem raw_coqStandardWitnessTailCompiler_apply : forall P Q,
  RawCoqStandardWitnessTailAppendStable P ->
  RawCoqStandardWitnessTailCompiler P ->
  RawCoqStandardWitnessTailCompiler (fun witnesses => P witnesses -> Q witnesses) ->
  RawCoqStandardWitnessTailCompiler Q.
Proof.
  intros P Q hstable hP hcontinuation baseWitnesses.
  destruct (hP baseWitnesses) as [pSuffix hp].
  destruct (hcontinuation (baseWitnesses ++ pSuffix))
    as [continuationSuffix hcontinuationAt].
  exists (pSuffix ++ continuationSuffix).
  rewrite app_assoc.
  apply hcontinuationAt.
  exact
    (hstable (baseWitnesses ++ pSuffix) continuationSuffix hp).
Qed.

(** Transport a represented proof below any affine context constructor.  The
    conclusion is an arbitrary carrier formula code, so this theorem applies
    equally to template formulas and to explicitly constructed implication
    codes such as the equality-reflexivity residual. *)
Theorem raw_codedPALocalProof_standardWitnessTail_surround_under_affine_context :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall (contextAt : TemplateContext -> TemplateContext),
  (forall witnesses,
    contextAt (embedPAContext (map witnessedAxiom witnesses)) =
      contextAt [] ++ embedPAContext (map witnessedAxiom witnesses)) ->
  forall witnesses suffix conclusion root,
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation
      (contextAt (embedPAContext (map witnessedAxiom witnesses))))
    conclusion root ->
  exists transportedRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (contextAt
          (embedPAContext (map witnessedAxiom (witnesses ++ suffix)))))
      conclusion transportedRoot.
Proof.
  intros M hPA translation hagreement contextAt haffine
    witnesses suffix conclusion root hroot.
  rewrite haffine in hroot.
  destruct
    (raw_codedPALocalProof_standardWitnessTail_surround_under_prefix
      M hPA translation hagreement (contextAt []) [] witnesses suffix
      conclusion root hroot) as [transportedRoot htransported].
  exists transportedRoot.
  rewrite haffine.
  cbn [List.app] in htransported.
  exact htransported.
Qed.

(** Existentially packaged local-proof roots inherit append-stability from
    the affine context equation. *)
Theorem raw_codedPALocalProof_affine_context_root_append_stable : forall
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall (contextAt : TemplateContext -> TemplateContext),
  (forall witnesses,
    contextAt (embedPAContext (map witnessedAxiom witnesses)) =
      contextAt [] ++ embedPAContext (map witnessedAxiom witnesses)) ->
  forall conclusion,
  RawCoqStandardWitnessTailAppendStable
    (fun witnesses => exists root,
      RawCodedPALocalProofOf M
        (rawTemplateContextCode translation
          (contextAt (embedPAContext (map witnessedAxiom witnesses))))
        conclusion root).
Proof.
  intros M hPA translation hagreement contextAt haffine conclusion
    witnesses suffix [root hroot].
  exact
    (raw_codedPALocalProof_standardWitnessTail_surround_under_affine_context
      M hPA translation hagreement contextAt haffine
      witnesses suffix conclusion root hroot).
Qed.

End PABoundedRawCodedTemplateLocalProofAffineStandardWitnessTailTransport.
