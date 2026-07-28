(**
  Accumulating an ordinary represented PA proof into a witnessed context.

  An ordinary [RawCodedPAProofOf] certificate hides its finite PA-axiom list,
  literal proof context, and local proof root.  The staged truth-certificate
  successor, however, must use the current master roots and every previously
  produced successor root in one common context.  Merely opening two ordinary
  certificates therefore does not justify conjoining their conclusions.

  This module supplies the small, reusable bridge.  It opens the new
  certificate, merges its witnessed context with the caller's witnessed base,
  and uses the completed binder-safe weakening theorem to return

    * a witnessed merged context,
    * uniform transport for every root in the old base, and
    * a local proof of the new conclusion in that same merged context.

  A metatheoretic [Forall2] helper transports any fixed finite family of old
  roots together.  It does not recurse over a coded, potentially nonstandard
  object-language list; all nonstandard context work remains inside the
  represented prefix merge and weakening theorems.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPAProvability
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofWitnessedContextMergeTransportComplete.

Module PABoundedRawCodedPAOrdinaryProofWitnessedContextAccumulation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import
  PABoundedRawCodedPALocalProofWitnessedContextMergeTransportComplete.

(** A fixed metatheoretic family of conclusion/root pairs sharing one literal
    object-language context. *)
Definition RawCodedPALocalProofFamilyOn (M : RawPAModel) (context : M)
    (conclusions roots : list M) : Prop :=
  Forall2 (fun conclusion root =>
    RawCodedPALocalProofOf M context conclusion root) conclusions roots.

Arguments RawCodedPALocalProofFamilyOn M context conclusions roots
  : clear implicits.

(** Uniform context transport may be applied pointwise to a fixed family.
    The returned roots are allowed to change, but conclusions and the one
    target context remain literal. *)
Theorem raw_codedPALocalProofContextTransport_family : forall
    (M : RawPAModel) source target,
  RawCodedPALocalProofContextTransport M source target ->
  forall conclusions roots,
    RawCodedPALocalProofFamilyOn M source conclusions roots ->
    exists transportedRoots,
      RawCodedPALocalProofFamilyOn M target conclusions transportedRoots.
Proof.
  intros M source target htransport conclusions roots hfamily.
  induction hfamily as [| conclusion root conclusions roots
      hproof hfamily ih].
  - exists nil. constructor.
  - destruct (htransport conclusion root hproof) as
      [transportedRoot htransported].
    destruct ih as [transportedRoots htransportedFamily].
    exists (transportedRoot :: transportedRoots).
    constructor; assumption.
Qed.

(** Open one ordinary certificate and add it to a witnessed base.  The old
    context is preserved through a uniform transport relation, which is
    stronger and more useful than returning one arbitrarily selected old
    root. *)
Theorem raw_codedPAProofOf_add_to_witnessed_context_complete : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      newConclusion newCertificate baseWitnessList baseContext,
  RawCodedPAProofOf M newConclusion newCertificate ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists mergedWitnessList mergedContext transportedNewRoot : M,
    RawCodedPAAxiomWitnessContext M mergedWitnessList mergedContext /\
    RawCodedPALocalProofContextTransport M baseContext mergedContext /\
    RawCodedPALocalProofOf M
      mergedContext newConclusion transportedNewRoot.
Proof.
  intros M hPA newConclusion newCertificate
    baseWitnessList baseContext hnew hbase.
  destruct (raw_codedPAProofOf_witnessedLocal_fields
    M newConclusion newCertificate hnew) as
    (newWitnessList & newContext & newRoot &
      hnewWitnessed & hnewLocal).
  exact (raw_codedPALocalProof_addWitnessedContext_of_weakening
    M hPA
    (raw_codedPALocalProofWitnessedContextInclusionWeakening_complete
      M hPA)
    newWitnessList newContext newConclusion newRoot
    baseWitnessList baseContext
    hnewWitnessed hnewLocal hbase).
Qed.

(** Convenience form which moves a fixed family of old roots immediately.
    This is the shape used by dependency-ordered successor stages. *)
Theorem raw_codedPAProofOf_accumulate_local_family_complete : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      newConclusion newCertificate baseWitnessList baseContext
      conclusions roots,
  RawCodedPAProofOf M newConclusion newCertificate ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofFamilyOn M baseContext conclusions roots ->
  exists mergedWitnessList mergedContext transportedRoots
      transportedNewRoot,
    RawCodedPAAxiomWitnessContext M mergedWitnessList mergedContext /\
    RawCodedPALocalProofFamilyOn M
      mergedContext conclusions transportedRoots /\
    RawCodedPALocalProofOf M
      mergedContext newConclusion transportedNewRoot.
Proof.
  intros M hPA newConclusion newCertificate baseWitnessList baseContext
    conclusions roots hnew hbase hfamily.
  destruct (raw_codedPAProofOf_add_to_witnessed_context_complete
    M hPA newConclusion newCertificate baseWitnessList baseContext
    hnew hbase) as
    (mergedWitnessList & mergedContext & transportedNewRoot &
      hmerged & htransport & hnewLocal).
  destruct (raw_codedPALocalProofContextTransport_family
    M baseContext mergedContext htransport
    conclusions roots hfamily) as
    [transportedRoots htransportedFamily].
  exists mergedWitnessList, mergedContext,
    transportedRoots, transportedNewRoot.
  split; [exact hmerged |].
  split; [exact htransportedFamily | exact hnewLocal].
Qed.

End PABoundedRawCodedPAOrdinaryProofWitnessedContextAccumulation.
