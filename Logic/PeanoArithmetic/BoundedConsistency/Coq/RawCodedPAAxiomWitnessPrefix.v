(**
  Finite prefixes of standard PA-axiom witnesses over an arbitrary base.

  Independently compiled fixed templates may use different finite collections
  of PA axioms.  To place all of their proof roots in one literal coded
  context, choose one metatheoretic list of [PAAxiomWitness] values and prepend
  its witness/axiom pairs to a shared carrier-coded base.

  The two folds below are synchronized by construction:

    witness code :: ... :: base witness list
    quoted axiom :: ... :: base context.

  [raw_codedPAAxiomWitnessContext_standardPrefix] proves that synchronization
  semantically by iterating the honest one-row extension theorem.  The proof
  transplantation theorem needs less: a realizable base context and a local
  proof over that exact base.  It iterates guarded cons transplant from the
  tail of the prefix toward its head; every guard is discharged by atomic
  adequacy of an honestly quoted standard formula.

  The prefix length is metatheoretic and finite.  The base codes themselves
  remain arbitrary carrier elements and are never decoded.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedPAAxiomWitness
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessContextCons
  RawCodedProofAtomicAdequacyStandard
  RawCodedPALocalProofExistential
  RawCodedPALocalProofContextInsertUnconditional.

Import ListNotations.

Module PABoundedRawCodedPAAxiomWitnessPrefix.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedProof.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessContextCons.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofContextInsertUnconditional.

(** A prefix is deliberately an ordinary Rocq list.  Its entries are fixed
    syntactic PA-axiom witnesses; only the base and the resulting list codes
    may be nonstandard carrier values. *)
Definition StandardPAAxiomWitnessPrefix : Type := list PAAxiomWitness.

Definition standardPAAxiomWitnessPrefixEmpty
    : StandardPAAxiomWitnessPrefix := [].

Definition standardPAAxiomWitnessPrefixCons
    (witness : PAAxiomWitness)
    (tail : StandardPAAxiomWitnessPrefix)
    : StandardPAAxiomWitnessPrefix := witness :: tail.

(** The prefix folds from right to left, so list order agrees with the final
    coded context order. *)
Fixpoint rawStandardPAAxiomWitnessPrefixWitnessListCode
    (M : RawPAModel) (prefix : StandardPAAxiomWitnessPrefix)
    (baseWitnessList : M) : M :=
  match prefix with
  | [] => baseWitnessList
  | witness :: tail =>
      rawListNode M
        (rawNumeralValue M (axiomWitnessCode witness))
        (rawStandardPAAxiomWitnessPrefixWitnessListCode
          M tail baseWitnessList)
  end.

Arguments rawStandardPAAxiomWitnessPrefixWitnessListCode
  M prefix baseWitnessList : clear implicits.

Fixpoint rawStandardPAAxiomWitnessPrefixContextCode
    (M : RawPAModel) (prefix : StandardPAAxiomWitnessPrefix)
    (baseContext : M) : M :=
  match prefix with
  | [] => baseContext
  | witness :: tail =>
      rawListNode M
        (rawQuotedFormulaCode M (witnessedAxiom witness))
        (rawStandardPAAxiomWitnessPrefixContextCode
          M tail baseContext)
  end.

Arguments rawStandardPAAxiomWitnessPrefixContextCode
  M prefix baseContext : clear implicits.

(** Prefix concatenation corresponds literally to composing the two folds.
    This is useful when several compilers contribute independent finite
    witness batches. *)
Lemma rawStandardPAAxiomWitnessPrefixWitnessListCode_app : forall
    (M : RawPAModel) left right baseWitnessList,
  rawStandardPAAxiomWitnessPrefixWitnessListCode M
    (left ++ right) baseWitnessList =
  rawStandardPAAxiomWitnessPrefixWitnessListCode M left
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      right baseWitnessList).
Proof.
  intros M left.
  induction left as [| witness tail ih]; intros right baseWitnessList.
  - reflexivity.
  - change (rawListNode M
      (rawNumeralValue M (axiomWitnessCode witness))
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        (tail ++ right) baseWitnessList) =
      rawListNode M
        (rawNumeralValue M (axiomWitnessCode witness))
        (rawStandardPAAxiomWitnessPrefixWitnessListCode M tail
          (rawStandardPAAxiomWitnessPrefixWitnessListCode M
            right baseWitnessList))).
    rewrite ih. reflexivity.
Qed.

Lemma rawStandardPAAxiomWitnessPrefixContextCode_app : forall
    (M : RawPAModel) left right baseContext,
  rawStandardPAAxiomWitnessPrefixContextCode M
    (left ++ right) baseContext =
  rawStandardPAAxiomWitnessPrefixContextCode M left
    (rawStandardPAAxiomWitnessPrefixContextCode M right baseContext).
Proof.
  intros M left.
  induction left as [| witness tail ih]; intros right baseContext.
  - reflexivity.
  - change (rawListNode M
      (rawQuotedFormulaCode M (witnessedAxiom witness))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        (tail ++ right) baseContext) =
      rawListNode M
        (rawQuotedFormulaCode M (witnessedAxiom witness))
        (rawStandardPAAxiomWitnessPrefixContextCode M tail
          (rawStandardPAAxiomWitnessPrefixContextCode M
            right baseContext))).
    rewrite ih. reflexivity.
Qed.

(** ------------------------------------------------------------------
    Synchronized witnessed-context extension. *)

Theorem raw_codedPAAxiomWitnessContext_standardPrefix : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      prefix baseWitnessList baseContext,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPAAxiomWitnessContext M
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      prefix baseWitnessList)
    (rawStandardPAAxiomWitnessPrefixContextCode M
      prefix baseContext).
Proof.
  intros M hPA prefix.
  induction prefix as [| witness tail ih];
    intros baseWitnessList baseContext hbase.
  - exact hbase.
  - cbn [rawStandardPAAxiomWitnessPrefixWitnessListCode
      rawStandardPAAxiomWitnessPrefixContextCode].
    apply (raw_codedPAAxiomWitnessContext_cons M hPA).
    + exact (ih baseWitnessList baseContext hbase).
    + exact (raw_codedPAAxiomWitness_standard M hPA witness).
Qed.

(** The context half of a witnessed package exposes an honest traversal.  It
    is restated locally to keep this finite-prefix layer independent of any
    proof-certificate wrapper. *)
Lemma raw_codedPAAxiomWitnessPrefix_context_realizable_of_witnessed : forall
    (M : RawPAModel) witnessList context,
  RawCodedPAAxiomWitnessContext M witnessList context ->
  RawContextListRealizable M context.
Proof.
  intros M witnessList context
    (bound & witnessTailCode & witnessTailStep &
      witnessHeadCode & witnessHeadStep &
      axiomTailCode & axiomTailStep & axiomHeadCode & axiomHeadStep &
      hwitnessed).
  unfold RawCodedPAAxiomWitnessContextWithTables in hwitnessed.
  destruct hwitnessed as [_ [hcontext _]].
  exists bound, axiomTailCode, axiomTailStep, axiomHeadCode, axiomHeadStep.
  exact hcontext.
Qed.

Corollary raw_codedPAAxiomWitnessContext_standardPrefix_realizable : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      prefix baseWitnessList baseContext,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawContextListRealizable M
    (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext).
Proof.
  intros M hPA prefix baseWitnessList baseContext hbase.
  apply (raw_codedPAAxiomWitnessPrefix_context_realizable_of_witnessed
    M
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      prefix baseWitnessList)).
  exact (raw_codedPAAxiomWitnessContext_standardPrefix
    M hPA prefix baseWitnessList baseContext hbase).
Qed.

(** The same context-realizability fact needs no witness-list premise when a
    caller already has a traversal for the arbitrary base context. *)
Lemma raw_standardPAAxiomWitnessPrefix_context_realizable : forall
    (M : RawPAModel), RawPASatisfies M -> forall prefix baseContext,
  RawContextListRealizable M baseContext ->
  RawContextListRealizable M
    (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext).
Proof.
  intros M hPA prefix.
  induction prefix as [| witness tail ih]; intros baseContext hbase.
  - exact hbase.
  - cbn [rawStandardPAAxiomWitnessPrefixContextCode].
    exact (raw_contextList_cons_realizable M hPA
      (rawStandardPAAxiomWitnessPrefixContextCode M tail baseContext)
      (rawQuotedFormulaCode M (witnessedAxiom witness))
      (ih baseContext hbase)).
Qed.

(** ------------------------------------------------------------------
    Proof transplantation through the complete standard prefix. *)

Theorem raw_codedPALocalProofOf_standardPAAxiomWitnessPrefix : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      prefix baseContext conclusion root,
  RawContextListRealizable M baseContext ->
  RawCodedPALocalProofOf M baseContext conclusion root ->
  exists prefixedRoot,
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        prefix baseContext)
      conclusion prefixedRoot.
Proof.
  intros M hPA prefix.
  induction prefix as [| witness tail ih];
    intros baseContext conclusion root hbase hproof.
  - exists root. exact hproof.
  - cbn [rawStandardPAAxiomWitnessPrefixContextCode].
    destruct (ih baseContext conclusion root hbase hproof)
      as [tailRoot htailProof].
    apply (raw_codedPALocalProof_adequateConsTransplant
      M hPA
      (rawStandardPAAxiomWitnessPrefixContextCode M tail baseContext)
      (rawQuotedFormulaCode M (witnessedAxiom witness))
      conclusion tailRoot).
    + exact (raw_quotedFormula_atomically_adequate
        M hPA (witnessedAxiom witness)).
    + exact (raw_standardPAAxiomWitnessPrefix_context_realizable
        M hPA tail baseContext hbase).
    + exact htailProof.
Qed.

(** Strong combined endpoint for the common use case: the prefix remains a
    synchronized witnessed PA context, and the old proof is rebuilt over its
    exact context code. *)
Theorem raw_codedPAAxiomWitnessPrefix_sharedContext : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      prefix baseWitnessList baseContext conclusion root,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M baseContext conclusion root ->
  exists prefixedRoot,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        prefix baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        prefix baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        prefix baseContext)
      conclusion prefixedRoot.
Proof.
  intros M hPA prefix baseWitnessList baseContext conclusion root
    hbase hproof.
  destruct (raw_codedPALocalProofOf_standardPAAxiomWitnessPrefix
    M hPA prefix baseContext conclusion root
    (raw_codedPAAxiomWitnessPrefix_context_realizable_of_witnessed
      M baseWitnessList baseContext hbase)
    hproof) as [prefixedRoot hprefixedProof].
  exists prefixedRoot. split.
  - exact (raw_codedPAAxiomWitnessContext_standardPrefix
      M hPA prefix baseWitnessList baseContext hbase).
  - exact hprefixedProof.
Qed.

End PABoundedRawCodedPAAxiomWitnessPrefix.
