(**
  Model-internal induction for inserting one assumption into every context
  stored by a coded PA derivation.

  The insertion depth changes while descending through implication and
  existential elimination nodes, and a nonstandard proof may have
  nonstandard depth.  Consequently neither a Rocq [nat] recursion nor the
  root-only cons statement is an adequate induction hypothesis.  This file
  packages the correct depth-indexed statement as a PA formula and performs
  induction on a carrier-valued upper bound for proof codes.

  The inserted head is required to be atomically adequate.  This is not
  cosmetic: All-I and Ex-E shift the entire context below a binder, and the
  represented formula-shift graph is intentionally partial on malformed
  carrier elements.  Every head used by the dynamic-soundness producer is a
  genuine formula code, while an unguarded weakening theorem for arbitrary
  carrier values would be too strong for this proof encoding.

  The downstream root-step module performs the deliberately constructor-local
  remainder: at root [r], it assumes every strictly smaller proof code is
  transplantable, inspects the covered rule, and rebuilds all seventeen rule
  forms over the target context.  The only remaining input to that assembled
  theorem is formula-shift trace composition; no global proof-tree recursion
  remains.
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAdditionLaws
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedContextInsert
  RawCodedFixedLevelTruthTotality
  RawCodedProofEndpoints
  RawCodedProofRuleCoverage
  RawCodedProofAssumptionLeaf
  RawCodedPALocalProofExistential.

Module PABoundedRawCodedPALocalProofContextInsertInduction.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedAdditionLaws.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextInsert.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedPALocalProofExistential.

(** The conjunction is repeated locally rather than importing the later
    universal-closure compiler merely for its private spelling of the same
    represented local-proof package. *)
Definition codedPALocalProofForInsertTermAt
    (context target proof : term) : formula :=
  pAnd
    (proofRuleCoverageTermAt proof)
    (proofEndpointTermAt proof context target).

Lemma raw_sat_codedPALocalProofForInsertTermAt_iff : forall
    (M : RawPAModel) e context target proof,
  raw_formula_sat M e
    (codedPALocalProofForInsertTermAt context target proof) <->
  RawCodedPALocalProofOf M
    (raw_term_eval M e context)
    (raw_term_eval M e target)
    (raw_term_eval M e proof).
Proof.
  intros. unfold codedPALocalProofForInsertTermAt,
    RawCodedPALocalProofOf.
  cbn [raw_formula_sat].
  rewrite raw_sat_proofRuleCoverageTermAt_iff,
    raw_sat_proofEndpointTermAt_iff.
  reflexivity.
Qed.

(** A fixed proof root is transplantable at every represented insertion
    depth.  The insertion relation itself supplies realizability of both
    contexts, so no redundant traversal premise is stored in this invariant. *)
Definition RawCodedPALocalProofContextInsertAt
    (M : RawPAModel) (root : M) : Prop :=
  forall head depth source target conclusion : M,
    RawCodedFormulaAtomicallyAdequate M head ->
    RawContextInsertAt M head depth source target ->
    RawCodedPALocalProofOf M source conclusion root ->
    exists transplanted : M,
      RawCodedPALocalProofOf M target conclusion transplanted.

Arguments RawCodedPALocalProofContextInsertAt M root : clear implicits.

(** Binder order: inserted head, depth, source context, target context,
    conclusion. *)
Definition contextInsertAll5 (body : formula) : formula :=
  pAll (pAll (pAll (pAll (pAll body)))).

Definition contextInsertImp3
    (first second third conclusion : formula) : formula :=
  pImp first (pImp second (pImp third conclusion)).

Definition codedPALocalProofContextInsertAtTermAt
    (root : term) : formula :=
  contextInsertAll5
    (contextInsertImp3
      (codedFormulaAtomicallyAdequateTermAt (tVar 4))
      (contextInsertAtTermAt
        (tVar 4) (tVar 3) (tVar 2) (tVar 1))
      (codedPALocalProofForInsertTermAt
        (tVar 2) (tVar 0) (liftTerm 5 root))
      (pEx
        (codedPALocalProofForInsertTermAt
          (liftTerm 1 (tVar 1))
          (liftTerm 1 (tVar 0))
          (tVar 0)))).

Lemma raw_contextInsertProof_eval_liftTerm_five : forall
    (M : RawPAModel) a b c d f (e : nat -> M) t,
  raw_term_eval M
    (scons M a (scons M b (scons M c (scons M d (scons M f e)))))
    (liftTerm 5 t) = raw_term_eval M e t.
Proof.
  intros M a b c d f e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro i.
  replace (i + 5) with (S (S (S (S (S i))))) by lia.
  reflexivity.
Qed.

Lemma raw_contextInsertProof_eval_liftTerm_one : forall
    (M : RawPAModel) a (e : nat -> M) t,
  raw_term_eval M (scons M a e) (liftTerm 1 t) =
  raw_term_eval M e t.
Proof.
  intros M a e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro i.
  replace (i + 1) with (S i) by lia. reflexivity.
Qed.

Lemma raw_sat_codedPALocalProofContextInsertAtTermAt_iff : forall
    (M : RawPAModel) e root,
  raw_formula_sat M e
    (codedPALocalProofContextInsertAtTermAt root) <->
  RawCodedPALocalProofContextInsertAt M (raw_term_eval M e root).
Proof.
  intros M e root.
  unfold codedPALocalProofContextInsertAtTermAt,
    contextInsertAll5, contextInsertImp3,
    RawCodedPALocalProofContextInsertAt.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedFormulaAtomicallyAdequateTermAt_iff.
  setoid_rewrite raw_sat_contextInsertAtTermAt_iff.
  setoid_rewrite raw_sat_codedPALocalProofForInsertTermAt_iff.
  repeat setoid_rewrite raw_contextInsertProof_eval_liftTerm_five.
  repeat setoid_rewrite raw_contextInsertProof_eval_liftTerm_one.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** Every root below [bound] is transplantable.  Bounding the root rather
    than attempting structural recursion on its decoded tree is what makes
    PA's own induction applicable in arbitrary models. *)
Definition RawCodedPALocalProofContextInsertBelow
    (M : RawPAModel) (bound : M) : Prop :=
  forall root : M,
    rawLt M root bound ->
    RawCodedPALocalProofContextInsertAt M root.

Arguments RawCodedPALocalProofContextInsertBelow M bound : clear implicits.

Definition codedPALocalProofContextInsertBelowTermAt
    (bound : term) : formula :=
  pAll
    (pImp
      (Formula.ltTermAt (tVar 0) (liftTerm 1 bound))
      (codedPALocalProofContextInsertAtTermAt (tVar 0))).

Lemma raw_sat_codedPALocalProofContextInsertBelowTermAt_iff : forall
    (M : RawPAModel) e bound,
  raw_formula_sat M e
    (codedPALocalProofContextInsertBelowTermAt bound) <->
  RawCodedPALocalProofContextInsertBelow M
    (raw_term_eval M e bound).
Proof.
  intros M e bound.
  unfold codedPALocalProofContextInsertBelowTermAt,
    RawCodedPALocalProofContextInsertBelow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedPALocalProofContextInsertAtTermAt_iff.
  repeat setoid_rewrite raw_contextInsertProof_eval_liftTerm_one.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_codedPALocalProofContextInsertBelow_zero : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedPALocalProofContextInsertBelow M (raw_zero M).
Proof.
  intros M hPA root hroot.
  exfalso. exact (raw_not_lt_zero M hPA root hroot).
Qed.

(** The sole rule row that reads its context is already stable under an
    insertion at any model-internal depth.  The original assumption remains
    a member of the target context, and the canonical target-context leaf
    rebuilds both coverage and its exact endpoint. *)
Theorem raw_codedPALocalProof_contextInsert_assumption : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      head depth source target conclusion,
  RawContextInsertAt M head depth source target ->
  RawContextListMember M source conclusion ->
  RawCodedPALocalProofOf M target conclusion
    (rawProofAssumptionRoot M target conclusion).
Proof.
  intros M hPA head depth source target conclusion
    hinsertion hmember.
  assert (htargetMember : RawContextListMember M target conclusion).
  {
    exact (raw_contextInsertAt_source_member M hPA
      head depth source target conclusion hinsertion hmember).
  }
  split.
  - exact (raw_proofAssumption_ruleCoverage M hPA
      target conclusion htargetMember).
  - exact (raw_proofAssumption_endpoint M target conclusion).
Qed.

(** The only proof-specific input needed by the represented induction: a
    covered root can be rebuilt once all strictly smaller children can be
    rebuilt. *)
Definition RawCodedPALocalProofContextInsertRootStep
    (M : RawPAModel) : Prop :=
  forall root : M,
    RawCodedPALocalProofContextInsertBelow M root ->
    RawCodedPALocalProofContextInsertAt M root.

Arguments RawCodedPALocalProofContextInsertRootStep M : clear implicits.

Lemma raw_codedPALocalProofContextInsertBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedPALocalProofContextInsertRootStep M ->
  forall current,
    RawCodedPALocalProofContextInsertBelow M current ->
    RawCodedPALocalProofContextInsertBelow M (raw_succ M current).
Proof.
  intros M hPA hrootStep current hbelow root hroot.
  destruct (raw_lt_succ_cases M hPA root current hroot)
    as [hstrict | ->].
  - exact (hbelow root hstrict).
  - exact (hrootStep current hbelow).
Qed.

(** PA induction reaches nonstandard carrier bounds because the complete
    below-bound invariant above is represented by an arithmetic formula. *)
Theorem raw_codedPALocalProofContextInsertBelow_all : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedPALocalProofContextInsertRootStep M ->
  forall bound,
    RawCodedPALocalProofContextInsertBelow M bound.
Proof.
  intros M hPA hrootStep.
  set (parameterEnv := fun _ : nat => raw_zero M).
  set (phi := codedPALocalProofContextInsertBelowTermAt (tVar 0)).
  assert (hall : forall bound,
      raw_formula_sat M (scons M bound parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_codedPALocalProofContextInsertBelowTermAt_iff M
          (scons M (raw_zero M) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons].
      exact (raw_codedPALocalProofContextInsertBelow_zero M hPA).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_codedPALocalProofContextInsertBelowTermAt_iff M
          (scons M current parameterEnv) (tVar 0))
        hcurrentSat) as hcurrent.
      apply (proj2
        (raw_sat_codedPALocalProofContextInsertBelowTermAt_iff M
          (scons M (raw_succ M current) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons] in hcurrent |- *.
      exact (raw_codedPALocalProofContextInsertBelow_succ
        M hPA hrootStep current hcurrent).
  }
  intro bound. unfold phi in hall.
  pose proof (proj1
    (raw_sat_codedPALocalProofContextInsertBelowTermAt_iff M
      (scons M bound parameterEnv) (tVar 0))
    (hall bound)) as hbound.
  cbn [raw_term_eval scons] in hbound. exact hbound.
Qed.

Corollary raw_codedPALocalProofContextInsertAt_all : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedPALocalProofContextInsertRootStep M ->
  forall root,
    RawCodedPALocalProofContextInsertAt M root.
Proof.
  intros M hPA hrootStep root.
  exact (hrootStep root
    (raw_codedPALocalProofContextInsertBelow_all M hPA hrootStep root)).
Qed.

(** Position zero recovers the original single-cons transplant interface.
    This bridge is kept independent of the downstream producer module so the
    induction infrastructure has no circular dependency. *)
Corollary
    raw_codedPALocalProof_adequateConsTransplant_of_contextInsertRootStep :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawCodedPALocalProofContextInsertRootStep M ->
  forall context head conclusion root,
    RawCodedFormulaAtomicallyAdequate M head ->
    RawContextListRealizable M context ->
    RawCodedPALocalProofOf M context conclusion root ->
    exists transplanted : M,
      RawCodedPALocalProofOf M
        (rawListNode M head context) conclusion transplanted.
Proof.
  intros M hPA hrootStep context head conclusion root
    hhead hcontext hproof.
  pose proof (raw_contextInsertAt_zero M hPA context head hcontext)
    as hinsertion.
  exact (raw_codedPALocalProofContextInsertAt_all M hPA hrootStep root
    head (raw_zero M) context (rawListNode M head context)
    conclusion hhead hinsertion hproof).
Qed.

End PABoundedRawCodedPALocalProofContextInsertInduction.
