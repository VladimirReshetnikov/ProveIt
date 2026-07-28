(**
  Propagate ordinary substitution identity through a nonstandard universal
  closure.

  A closed formula code admits an ordinary represented substitution trace
  from itself to itself at every depth.  Unlike a diagonal trace, these
  traces may use different model-internal tables at different depths.  That
  weaker fact is nevertheless exactly what universal-closure opening needs.

  The all-depth identity is represented by an ordinary PA formula and used
  as an invariant for PA's definable induction on the (possibly nonstandard)
  closure count.  In the successor case, closure inversion exposes the
  previous prefix; constructor compositionality then adds one [all] row to
  the identity trace available at the successor depth.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedFormulaOperations RawCodedFormulaShiftTreeRealization
  RawCodedFormulaOperationCompositionality
  RawCodedPAUniversalClosureProofReduction.

Module PABoundedRawCodedUniversalClosureOrdinarySubstitution.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaShiftTreeRealization.
Import PABoundedRawCodedFormulaOperationCompositionality.
Import PABoundedRawCodedPAUniversalClosureProofReduction.

(** Ordinary substitution fixes [input] at every model-internal depth.  Each
    depth is allowed its own represented operation trace. *)
Definition RawCodedFormulaSubstitutionIdentityAtAllDepths
    (M : RawPAModel) (replacement input : M) : Prop :=
  forall depth : M,
    RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
      replacement depth input input.

Arguments RawCodedFormulaSubstitutionIdentityAtAllDepths
  M replacement input : clear implicits.

Definition codedFormulaSubstitutionIdentityAtAllDepthsTermAt
    (replacement input : term) : formula :=
  pAll
    (codedFormulaOperationTermAt codedFormulaSubstitutionAtomTermAt
      (liftTerm 1 replacement) (tVar 0)
      (liftTerm 1 input) (liftTerm 1 input)).

Lemma raw_sat_codedFormulaSubstitutionIdentityAtAllDepthsTermAt_iff : forall
    (M : RawPAModel) e replacement input,
  raw_formula_sat M e
    (codedFormulaSubstitutionIdentityAtAllDepthsTermAt replacement input) <->
  RawCodedFormulaSubstitutionIdentityAtAllDepths M
    (raw_term_eval M e replacement) (raw_term_eval M e input).
Proof.
  intros M e replacement input.
  unfold codedFormulaSubstitutionIdentityAtAllDepthsTermAt,
    RawCodedFormulaSubstitutionIdentityAtAllDepths.
  cbn [raw_formula_sat]. split.
  - intros h depth.
    pose proof (proj1
      (raw_sat_codedFormulaOperationTermAt_iff M
        (scons M depth e) codedFormulaSubstitutionAtomTermAt
        (RawCodedFormulaSubstitutionAtom M)
        (raw_sat_codedFormulaSubstitutionAtomTermAt_iff M)
        (liftTerm 1 replacement) (tVar 0)
        (liftTerm 1 input) (liftTerm 1 input)) (h depth)) as hdepth.
    rewrite (raw_operation_eval_liftTerm_one M depth e replacement)
      in hdepth.
    rewrite (raw_operation_eval_liftTerm_one M depth e input)
      in hdepth.
    cbn [raw_term_eval scons] in hdepth. exact hdepth.
  - intros h depth.
    apply (proj2
      (raw_sat_codedFormulaOperationTermAt_iff M
        (scons M depth e) codedFormulaSubstitutionAtomTermAt
        (RawCodedFormulaSubstitutionAtom M)
        (raw_sat_codedFormulaSubstitutionAtomTermAt_iff M)
        (liftTerm 1 replacement) (tVar 0)
        (liftTerm 1 input) (liftTerm 1 input))).
    rewrite (raw_operation_eval_liftTerm_one M depth e replacement).
    rewrite (raw_operation_eval_liftTerm_one M depth e input).
    cbn [raw_term_eval scons]. exact (h depth).
Qed.

(** Every prefix at [count] inherits the all-depth ordinary identity.  The
    universal quantification over prefixes makes this a represented PA
    invariant without relying on meta-level functionality of closure. *)
Definition RawCodedUniversalClosureSubstitutionIdentityAt
    (M : RawPAModel) (replacement body count : M) : Prop :=
  forall prefix : M,
    RawCodedUniversalClosure M count body prefix ->
    RawCodedFormulaSubstitutionIdentityAtAllDepths M replacement prefix.

Arguments RawCodedUniversalClosureSubstitutionIdentityAt
  M replacement body count : clear implicits.

Definition codedUniversalClosureSubstitutionIdentityAtTermAt
    (replacement body count : term) : formula :=
  pAll
    (pImp
      (codedUniversalClosureTermAt
        (liftTerm 1 count) (liftTerm 1 body) (tVar 0))
      (codedFormulaSubstitutionIdentityAtAllDepthsTermAt
        (liftTerm 1 replacement) (tVar 0))).

Lemma raw_sat_codedUniversalClosureSubstitutionIdentityAtTermAt_iff : forall
    (M : RawPAModel) e replacement body count,
  raw_formula_sat M e
    (codedUniversalClosureSubstitutionIdentityAtTermAt
      replacement body count) <->
  RawCodedUniversalClosureSubstitutionIdentityAt M
    (raw_term_eval M e replacement) (raw_term_eval M e body)
    (raw_term_eval M e count).
Proof.
  intros M e replacement body count.
  unfold codedUniversalClosureSubstitutionIdentityAtTermAt,
    RawCodedUniversalClosureSubstitutionIdentityAt.
  cbn [raw_formula_sat]. split.
  - intros h prefix hclosure.
    specialize (h prefix).
    pose proof (proj2 (raw_sat_codedUniversalClosureTermAt_iff M
      (scons M prefix e) (liftTerm 1 count) (liftTerm 1 body)
      (tVar 0))) as hclosureSat.
    rewrite (raw_operation_eval_liftTerm_one M prefix e count)
      in hclosureSat.
    rewrite (raw_operation_eval_liftTerm_one M prefix e body)
      in hclosureSat.
    cbn [raw_term_eval scons] in hclosureSat.
    pose proof (h (hclosureSat hclosure)) as hidentitySat.
    apply (proj1
      (raw_sat_codedFormulaSubstitutionIdentityAtAllDepthsTermAt_iff M
        (scons M prefix e) (liftTerm 1 replacement) (tVar 0)))
      in hidentitySat.
    rewrite (raw_operation_eval_liftTerm_one M prefix e replacement)
      in hidentitySat.
    cbn [raw_term_eval scons] in hidentitySat. exact hidentitySat.
  - intros h prefix hclosureSat.
    apply (proj2
      (raw_sat_codedFormulaSubstitutionIdentityAtAllDepthsTermAt_iff M
        (scons M prefix e) (liftTerm 1 replacement) (tVar 0))).
    rewrite (raw_operation_eval_liftTerm_one M prefix e replacement).
    cbn [raw_term_eval scons]. apply h.
    apply (proj1 (raw_sat_codedUniversalClosureTermAt_iff M
      (scons M prefix e) (liftTerm 1 count) (liftTerm 1 body)
      (tVar 0))) in hclosureSat.
    rewrite (raw_operation_eval_liftTerm_one M prefix e count)
      in hclosureSat.
    rewrite (raw_operation_eval_liftTerm_one M prefix e body)
      in hclosureSat.
    cbn [raw_term_eval scons] in hclosureSat. exact hclosureSat.
Qed.

(** PA-definable induction reaches arbitrary, including nonstandard, closure
    counts.  At a successor, the identity at depth [S d] for the previous
    prefix is lifted through the newly added universal constructor at depth
    [d]. *)
Theorem raw_codedUniversalClosureSubstitutionIdentityAt_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall replacement body,
  RawCodedFormulaSubstitutionIdentityAtAllDepths M replacement body ->
  forall count,
    RawCodedUniversalClosureSubstitutionIdentityAt
      M replacement body count.
Proof.
  intros M hPA replacement body hbody.
  set (parameterEnv := fun n : nat =>
    match n with
    | 0 => replacement
    | _ => body
    end).
  set (phi := codedUniversalClosureSubstitutionIdentityAtTermAt
    (tVar 1) (tVar 2) (tVar 0)).
  assert (hall : forall count,
      raw_formula_sat M (scons M count parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_codedUniversalClosureSubstitutionIdentityAtTermAt_iff M
          (scons M (raw_zero M) parameterEnv)
          (tVar 1) (tVar 2) (tVar 0))).
      unfold parameterEnv. cbn [raw_term_eval scons].
      intros prefix hprefix.
      pose proof (raw_codedUniversalClosure_zero M hPA
        body prefix hprefix) as hprefixEq.
      subst prefix. exact hbody.
    - intros count hcountSat.
      unfold phi in hcountSat |- *.
      pose proof (proj1
        (raw_sat_codedUniversalClosureSubstitutionIdentityAtTermAt_iff M
          (scons M count parameterEnv)
          (tVar 1) (tVar 2) (tVar 0)) hcountSat) as hcount.
      apply (proj2
        (raw_sat_codedUniversalClosureSubstitutionIdentityAtTermAt_iff M
          (scons M (raw_succ M count) parameterEnv)
          (tVar 1) (tVar 2) (tVar 0))).
      unfold parameterEnv in hcount |- *.
      cbn [raw_term_eval scons] in hcount |- *.
      intros prefix hprefix.
      destruct (raw_codedUniversalClosure_succ_inversion M hPA
        count body prefix hprefix) as
        [previous [hprevious hprefixEq]].
      subst prefix. intro depth.
      exact (raw_codedFormulaSubstitution_unary_composition M hPA
        replacement RFSUAll depth previous previous
        (hcount previous hprevious (raw_succ M depth))).
  }
  intro count. unfold phi in hall.
  pose proof (proj1
    (raw_sat_codedUniversalClosureSubstitutionIdentityAtTermAt_iff M
      (scons M count parameterEnv)
      (tVar 1) (tVar 2) (tVar 0)) (hall count)) as hresult.
  unfold parameterEnv in hresult.
  cbn [raw_term_eval scons] in hresult. exact hresult.
Qed.

(** The proof-reduction consumer asks only for depth-zero self-substitution
    of strict prefixes.  It is an immediate projection of the invariant; the
    strict-bound hypothesis is intentionally unused. *)
Corollary
    raw_codedUniversalClosureSelfInstantiationThrough_of_identity : forall
    (M : RawPAModel), RawPASatisfies M -> forall replacement body limit,
  RawCodedFormulaSubstitutionIdentityAtAllDepths M replacement body ->
  RawCodedUniversalClosureSelfInstantiationThrough M
    replacement body limit.
Proof.
  intros M hPA replacement body limit hbody count prefix _ hprefix.
  pose proof (raw_codedUniversalClosureSubstitutionIdentityAt_all
    M hPA replacement body hbody count prefix hprefix) as hidentity.
  exact (hidentity (raw_zero M)).
Qed.

End PABoundedRawCodedUniversalClosureOrdinarySubstitution.
