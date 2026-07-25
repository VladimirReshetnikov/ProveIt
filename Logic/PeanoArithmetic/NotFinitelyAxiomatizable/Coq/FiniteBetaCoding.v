(**
  External finite Goedel-beta coding in raw models of PA.

  The carrier is the deliberately weak [RawPAModel] from the hierarchy
  reduction: arithmetic laws are obtained only from semantic validity of the
  sealed PA axioms.  In particular, no meta-level induction principle is
  added to a possibly nonstandard model.
*)

From Stdlib Require Import List Arith Lia Classical Factorial.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import HierarchyReduction
  FiniteSkolemHull CanonicalSelector CanonicalSelectorPA.

Import ListNotations.
Import PAHierarchyReduction.
Import PAFiniteSkolemHull.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.

Module PAFiniteBetaCoding.

(** The value of an external standard numeral in a raw PA algebra. *)
Fixpoint rawNumeralValue (M : RawPAModel) (n : nat) : M :=
  match n with
  | 0 => raw_zero M
  | S k => raw_succ M (rawNumeralValue M k)
  end.

Lemma raw_term_eval_numeral : forall (M : RawPAModel)
    (e : nat -> M) n,
  raw_term_eval M e (PA.Term.numeral n) = rawNumeralValue M n.
Proof.
  intros M e n. induction n; simpl; congruence.
Qed.

Lemma raw_term_eval_rename_succ : forall (M : RawPAModel)
    (t : PA.term) (e : nat -> M) d,
  raw_term_eval M (scons M d e) (PA.Term.rename S t) =
  raw_term_eval M e t.
Proof.
  intros M t e d.
  rewrite raw_term_eval_rename.
  apply raw_term_eval_ext.
  intros [|n]; reflexivity.
Qed.

Lemma raw_term_eval_rename_two_scons : forall (M : RawPAModel)
    (t : PA.term) (e : nat -> M) x y,
  raw_term_eval M (scons M x (scons M y e))
      (PA.Term.rename (fun n => n + 2) t) =
  raw_term_eval M e t.
Proof.
  intros M t e x y.
  rewrite raw_term_eval_rename.
  apply raw_term_eval_ext.
  intro n. replace (n + 2) with (S (S n)) by lia. reflexivity.
Qed.

(** Raw semantic beta entry.  The witnesses are the beta modulus and the
    quotient in the bounded remainder equation. *)
Definition RawBetaEntry (M : RawPAModel)
    (out code step idx : M) : Prop :=
  exists modulus : M,
    modulus = raw_succ M (raw_mul M (raw_succ M idx) step) /\
    exists quotient : M,
      rawLt M out modulus /\
      code = raw_add M (raw_mul M quotient modulus) out.

Lemma raw_sat_betaTermTermAt_iff : forall (M : RawPAModel)
    (out code step idx : PA.term) (e : nat -> M),
  raw_formula_sat M e
      (PA.Formula.betaTermTermAt out code step idx) <->
  RawBetaEntry M
    (raw_term_eval M e out) (raw_term_eval M e code)
    (raw_term_eval M e step) (raw_term_eval M e idx).
Proof.
  intros M out code step idx e.
  unfold PA.Formula.betaTermTermAt, PA.Formula.betaModTermTerm,
    PA.Formula.remTermTermAt, PA.Formula.ltTermAt,
    RawBetaEntry, rawLt.
  cbn [raw_formula_sat raw_term_eval].
  split.
  - intros [modulus [hmod [quotient [[d hlt] hcode]]]].
    repeat rewrite raw_term_eval_rename_succ in hmod.
    repeat rewrite raw_term_eval_rename_succ in hlt.
    repeat rewrite raw_term_eval_rename_succ in hcode.
    cbn [raw_term_eval scons] in hmod, hlt, hcode.
    exists modulus. split; [exact hmod |].
    exists quotient. split.
    + exists d. exact hlt.
    + exact hcode.
  - intros [modulus [hmod [quotient [[d hlt] hcode]]]].
    exists modulus. split.
    + repeat rewrite raw_term_eval_rename_succ.
      cbn [raw_term_eval scons]. exact hmod.
    + exists quotient. split.
      * exists d.
        repeat rewrite raw_term_eval_rename_succ.
        cbn [raw_term_eval scons]. exact hlt.
      * repeat rewrite raw_term_eval_rename_succ.
        cbn [raw_term_eval scons]. exact hcode.
Qed.

Lemma raw_sat_betaTermTermAt_vars_iff : forall (M : RawPAModel)
    (out code step idx : M) (e : nat -> M),
  raw_formula_sat M
      (scons M out (scons M code (scons M step (scons M idx e))))
      (PA.Formula.betaTermTermAt
        (PA.tVar 0) (PA.tVar 1) (PA.tVar 2) (PA.tVar 3)) <->
  RawBetaEntry M out code step idx.
Proof.
  intros M out code step idx e.
  rewrite raw_sat_betaTermTermAt_iff. simpl. reflexivity.
Qed.

Lemma raw_sat_ltTermAt_iff : forall (M : RawPAModel)
    (a b : PA.term) (e : nat -> M),
  raw_formula_sat M e (PA.Formula.ltTermAt a b) <->
  rawLt M (raw_term_eval M e a) (raw_term_eval M e b).
Proof.
  intros M a b e.
  unfold PA.Formula.ltTermAt, rawLt.
  cbn [raw_formula_sat raw_term_eval].
  split.
  - intros [d h]. exists d.
    repeat rewrite raw_term_eval_rename_succ in h.
    cbn [raw_term_eval scons] in h. exact h.
  - intros [d h]. exists d.
    repeat rewrite raw_term_eval_rename_succ.
    cbn [raw_term_eval scons]. exact h.
Qed.

(** Coq's PAHF syntax predates the Lean name for this formula.  Defining it
    here exposes exactly the same strict-prefix availability assertion. *)
Definition betaEntryExistsTermAt
    (code step idx : PA.term) : PA.formula :=
  PA.pEx (PA.Formula.betaTermTermAt
    (PA.tVar 0)
    (PA.Term.rename S code)
    (PA.Term.rename S step)
    (PA.Term.rename S idx)).

Definition betaEntryExistsPrefixTermAt
    (code step bound : PA.term) : PA.formula :=
  PA.pAll (PA.pImp
    (PA.Formula.ltTermAt (PA.tVar 0) (PA.Term.rename S bound))
    (betaEntryExistsTermAt
      (PA.Term.rename S code) (PA.Term.rename S step) (PA.tVar 0))).

Lemma raw_sat_betaEntryExistsPrefixTermAt_iff :
  forall (M : RawPAModel) (code step bound : PA.term) (e : nat -> M),
  raw_formula_sat M e (betaEntryExistsPrefixTermAt code step bound) <->
  forall idx,
    rawLt M idx (raw_term_eval M e bound) ->
    exists out,
      RawBetaEntry M out
        (raw_term_eval M e code) (raw_term_eval M e step) idx.
Proof.
  intros M code step bound e.
  unfold betaEntryExistsPrefixTermAt, betaEntryExistsTermAt.
  cbn [raw_formula_sat].
  split.
  - intros h idx hlt.
    assert (hltSat : raw_formula_sat M (scons M idx e)
        (PA.Formula.ltTermAt
          (PA.tVar 0) (PA.Term.rename S bound))).
    {
      apply (proj2 (raw_sat_ltTermAt_iff M _ _ _)).
      cbn [raw_term_eval scons].
      rewrite raw_term_eval_rename_succ.
      exact hlt.
    }
    destruct (h idx hltSat) as [out hout].
    exists out.
    pose proof (proj1 (raw_sat_betaTermTermAt_iff M
      (PA.tVar 0) (PA.Term.rename S (PA.Term.rename S code))
      (PA.Term.rename S (PA.Term.rename S step))
      (PA.Term.rename S (PA.tVar 0))
      (scons M out (scons M idx e))) hout) as hraw.
    repeat rewrite raw_term_eval_rename_succ in hraw.
    cbn [raw_term_eval scons] in hraw.
    exact hraw.
  - intros h idx hlt.
    pose proof (proj1 (raw_sat_ltTermAt_iff M
      (PA.tVar 0) (PA.Term.rename S bound) (scons M idx e)) hlt)
      as hltRaw.
    cbn [raw_term_eval scons] in hltRaw.
    rewrite raw_term_eval_rename_succ in hltRaw.
    destruct (h idx hltRaw) as [out hout].
    exists out.
    apply (proj2 (raw_sat_betaTermTermAt_iff M
      (PA.tVar 0) (PA.Term.rename S (PA.Term.rename S code))
      (PA.Term.rename S (PA.Term.rename S step))
      (PA.Term.rename S (PA.tVar 0))
      (scons M out (scons M idx e)))).
    repeat rewrite raw_term_eval_rename_succ.
    cbn [raw_term_eval scons].
    exact hout.
Qed.

(** Semantic shape of beta prepend: [head] is placed at zero and every
    available source entry below [bound] is shifted by one. *)
Lemma raw_sat_betaPrependExistsTermAt_iff :
  forall (M : RawPAModel)
    (sourceCode sourceStep head bound : PA.term) (e : nat -> M),
  raw_formula_sat M e
      (PA.Formula.betaPrependExistsTermAt
        sourceCode sourceStep head bound) <->
  exists targetStep targetCode : M,
    RawBetaEntry M (raw_term_eval M e head)
      targetCode targetStep (raw_zero M) /\
    forall idx,
      rawLt M idx (raw_term_eval M e bound) ->
      forall out,
        RawBetaEntry M out
          (raw_term_eval M e sourceCode)
          (raw_term_eval M e sourceStep) idx ->
        RawBetaEntry M out targetCode targetStep (raw_succ M idx).
Proof.
  intros M sourceCode sourceStep head bound e.
  unfold PA.Formula.betaPrependExistsTermAt,
    PA.Formula.betaPrependPrefixCodeExistsTermAt,
    PA.Formula.betaPrependPrefixTermAt,
    PA.Formula.betaUnshiftPrefixTermAt.
  cbn [raw_formula_sat].
  split.
  - intros [targetStep [targetCode [hhead hshift]]].
    exists targetStep, targetCode. split.
    + pose proof (proj1 (raw_sat_betaTermTermAt_iff M _ _ _ _ _) hhead)
        as hheadRaw.
      repeat rewrite raw_term_eval_rename_two_scons in hheadRaw.
      repeat rewrite raw_term_eval_rename_succ in hheadRaw.
      cbn [raw_term_eval scons] in hheadRaw.
      exact hheadRaw.
    + intros idx hlt out hsource.
      assert (hltSat : raw_formula_sat M
          (scons M idx (scons M targetCode (scons M targetStep e)))
          (PA.Formula.ltTermAt (PA.tVar 0)
            (PA.Term.rename S
              (PA.Term.rename S (PA.Term.rename S bound))))).
      {
        apply (proj2 (raw_sat_ltTermAt_iff M _ _ _)).
        repeat rewrite raw_term_eval_rename_succ.
        cbn [raw_term_eval scons]. exact hlt.
      }
      assert (hsourceSat : raw_formula_sat M
          (scons M out
            (scons M idx (scons M targetCode (scons M targetStep e))))
          (PA.Formula.betaTermTermAt (PA.tVar 0)
            (PA.Term.rename (fun n => n + 2)
              (PA.Term.rename S (PA.Term.rename S sourceCode)))
            (PA.Term.rename (fun n => n + 2)
              (PA.Term.rename S (PA.Term.rename S sourceStep)))
            (PA.tVar 1))).
      {
        apply (proj2 (raw_sat_betaTermTermAt_iff M _ _ _ _ _)).
        repeat rewrite raw_term_eval_rename_two_scons.
        repeat rewrite raw_term_eval_rename_succ.
        cbn [raw_term_eval scons]. exact hsource.
      }
      pose proof (hshift idx hltSat out hsourceSat) as htargetSat.
      pose proof (proj1 (raw_sat_betaTermTermAt_iff M _ _ _ _ _)
        htargetSat) as htargetRaw.
      repeat rewrite raw_term_eval_rename_two_scons in htargetRaw.
      repeat rewrite raw_term_eval_rename_succ in htargetRaw.
      cbn [raw_term_eval scons] in htargetRaw.
      exact htargetRaw.
  - intros [targetStep [targetCode [hhead hshift]]].
    exists targetStep, targetCode. split.
    + apply (proj2 (raw_sat_betaTermTermAt_iff M _ _ _ _ _)).
      repeat rewrite raw_term_eval_rename_two_scons.
      repeat rewrite raw_term_eval_rename_succ.
      cbn [raw_term_eval scons]. exact hhead.
    + intros idx hltSat out hsourceSat.
      pose proof (proj1 (raw_sat_ltTermAt_iff M _ _ _) hltSat)
        as hltRaw.
      repeat rewrite raw_term_eval_rename_succ in hltRaw.
      cbn [raw_term_eval scons] in hltRaw.
      pose proof (proj1 (raw_sat_betaTermTermAt_iff M _ _ _ _ _)
        hsourceSat) as hsourceRaw.
      repeat rewrite raw_term_eval_rename_two_scons in hsourceRaw.
      repeat rewrite raw_term_eval_rename_succ in hsourceRaw.
      cbn [raw_term_eval scons] in hsourceRaw.
      pose proof (hshift idx hltRaw out hsourceRaw) as htargetRaw.
      apply (proj2 (raw_sat_betaTermTermAt_iff M _ _ _ _ _)).
      repeat rewrite raw_term_eval_rename_two_scons.
      repeat rewrite raw_term_eval_rename_succ.
      cbn [raw_term_eval scons]. exact htargetRaw.
Qed.

Definition rawBetaModulus (M : RawPAModel) (step idx : M) : M :=
  raw_succ M (raw_mul M (raw_succ M idx) step).

Definition RawDvd (M : RawPAModel) (divisor value : M) : Prop :=
  exists factor : M, raw_mul M divisor factor = value.

Definition RawCommonMultipleThrough (M : RawPAModel)
    (bound multiple : M) : Prop :=
  forall idx, rawLt M idx bound -> RawDvd M (raw_succ M idx) multiple.

Definition RawBetaPrefixDivides (M : RawPAModel)
    (step bound product : M) : Prop :=
  forall idx, rawLt M idx bound ->
    RawDvd M (rawBetaModulus M step idx) product.

Definition RawCRTInverse (M : RawPAModel)
    (product modulus : M) : Prop :=
  exists inverse quotient : M,
    raw_mul M product inverse =
      raw_succ M (raw_mul M modulus quotient).

Lemma raw_term_eval_betaModTermTerm : forall (M : RawPAModel)
    (step idx : PA.term) (e : nat -> M),
  raw_term_eval M e (PA.Formula.betaModTermTerm step idx) =
  rawBetaModulus M (raw_term_eval M e step) (raw_term_eval M e idx).
Proof. reflexivity. Qed.

Lemma raw_sat_dvdTermTermAt_iff : forall (M : RawPAModel)
    (divisor value : PA.term) (e : nat -> M),
  raw_formula_sat M e
      (PA.Formula.dvdTermTermAt divisor value) <->
  RawDvd M (raw_term_eval M e divisor) (raw_term_eval M e value).
Proof.
  intros M divisor value e.
  unfold PA.Formula.dvdTermTermAt, RawDvd.
  cbn [raw_formula_sat raw_term_eval]. split.
  - intros [factor h]. exists factor.
    repeat rewrite raw_term_eval_rename_succ in h.
    cbn [raw_term_eval scons] in h. exact h.
  - intros [factor h]. exists factor.
    repeat rewrite raw_term_eval_rename_succ.
    cbn [raw_term_eval scons]. exact h.
Qed.

Lemma raw_sat_commonMultipleThroughTermAt_iff :
  forall (M : RawPAModel) (bound multiple : PA.term) (e : nat -> M),
  raw_formula_sat M e
      (PA.Formula.commonMultipleThroughTermAt bound multiple) <->
  RawCommonMultipleThrough M
    (raw_term_eval M e bound) (raw_term_eval M e multiple).
Proof.
  intros M bound multiple e.
  unfold PA.Formula.commonMultipleThroughTermAt.
  cbn [raw_formula_sat]. split.
  - intros h idx hlt.
    assert (hltSat : raw_formula_sat M (scons M idx e)
        (PA.Formula.ltTermAt
          (PA.tVar 0) (PA.Term.rename S bound))).
    {
      apply (proj2 (raw_sat_ltTermAt_iff M _ _ _)).
      rewrite raw_term_eval_rename_succ.
      cbn [raw_term_eval scons]. exact hlt.
    }
    pose proof (h idx hltSat) as hdvdSat.
    pose proof (proj1 (raw_sat_dvdTermTermAt_iff M _ _ _)
      hdvdSat) as hdvd.
    repeat rewrite raw_term_eval_rename_succ in hdvd.
    cbn [raw_term_eval scons] in hdvd.
    exact hdvd.
  - intros h idx hltSat.
    pose proof (proj1 (raw_sat_ltTermAt_iff M _ _ _) hltSat)
      as hlt.
    rewrite raw_term_eval_rename_succ in hlt.
    cbn [raw_term_eval scons] in hlt.
    pose proof (h idx hlt) as hdvd.
    apply (proj2 (raw_sat_dvdTermTermAt_iff M _ _ _)).
    repeat rewrite raw_term_eval_rename_succ.
    cbn [raw_term_eval scons]. exact hdvd.
Qed.

Lemma raw_sat_betaPrefixDividesTermAt_iff :
  forall (M : RawPAModel) (step bound product : PA.term) (e : nat -> M),
  raw_formula_sat M e
      (PA.Formula.betaPrefixDividesTermAt step bound product) <->
  RawBetaPrefixDivides M
    (raw_term_eval M e step) (raw_term_eval M e bound)
    (raw_term_eval M e product).
Proof.
  intros M step bound product e.
  unfold PA.Formula.betaPrefixDividesTermAt.
  cbn [raw_formula_sat]. split.
  - intros h idx hlt.
    assert (hltSat : raw_formula_sat M (scons M idx e)
        (PA.Formula.ltTermAt
          (PA.tVar 0) (PA.Term.rename S bound))).
    {
      apply (proj2 (raw_sat_ltTermAt_iff M _ _ _)).
      rewrite raw_term_eval_rename_succ.
      cbn [raw_term_eval scons]. exact hlt.
    }
    pose proof (h idx hltSat) as hdvdSat.
    pose proof (proj1 (raw_sat_dvdTermTermAt_iff M _ _ _)
      hdvdSat) as hdvd.
    rewrite raw_term_eval_betaModTermTerm in hdvd.
    repeat rewrite raw_term_eval_rename_succ in hdvd.
    cbn [raw_term_eval scons] in hdvd.
    exact hdvd.
  - intros h idx hltSat.
    pose proof (proj1 (raw_sat_ltTermAt_iff M _ _ _) hltSat)
      as hlt.
    rewrite raw_term_eval_rename_succ in hlt.
    cbn [raw_term_eval scons] in hlt.
    pose proof (h idx hlt) as hdvd.
    apply (proj2 (raw_sat_dvdTermTermAt_iff M _ _ _)).
    rewrite raw_term_eval_betaModTermTerm.
    repeat rewrite raw_term_eval_rename_succ.
    cbn [raw_term_eval scons]. exact hdvd.
Qed.

Lemma raw_sat_crtInverseExistsTermAt_iff :
  forall (M : RawPAModel) (product modulus : PA.term) (e : nat -> M),
  raw_formula_sat M e
      (PA.Formula.crtInverseExistsTermAt product modulus) <->
  RawCRTInverse M
    (raw_term_eval M e product) (raw_term_eval M e modulus).
Proof.
  intros M product modulus e.
  unfold PA.Formula.crtInverseExistsTermAt,
    PA.Formula.crtInverseTermAt, RawCRTInverse.
  cbn [raw_formula_sat raw_term_eval]. split.
  - intros [inverse [quotient h]]. exists inverse, quotient.
    repeat rewrite raw_term_eval_rename_two_scons in h.
    cbn [raw_term_eval scons] in h. exact h.
  - intros [inverse [quotient h]]. exists inverse, quotient.
    repeat rewrite raw_term_eval_rename_two_scons.
    cbn [raw_term_eval scons]. exact h.
Qed.

Lemma raw_sat_betaPrefixCRTAccumulatorTermAt_iff :
  forall (M : RawPAModel) (step target bound product : PA.term)
      (e : nat -> M),
  raw_formula_sat M e
      (PA.Formula.betaPrefixCRTAccumulatorTermAt
        step target bound product) <->
  RawBetaPrefixDivides M
    (raw_term_eval M e step) (raw_term_eval M e bound)
    (raw_term_eval M e product) /\
  RawCRTInverse M (raw_term_eval M e product)
    (rawBetaModulus M
      (raw_term_eval M e step) (raw_term_eval M e target)).
Proof.
  intros M step target bound product e.
  unfold PA.Formula.betaPrefixCRTAccumulatorTermAt.
  cbn [raw_formula_sat].
  rewrite raw_sat_betaPrefixDividesTermAt_iff.
  rewrite raw_sat_crtInverseExistsTermAt_iff.
  rewrite raw_term_eval_betaModTermTerm.
  reflexivity.
Qed.

Theorem raw_betaPrefixCRTAccumulator_self : forall (M : RawPAModel),
  RawPASatisfies M -> forall step target : M,
  RawCommonMultipleThrough M target step ->
  exists product : M,
    RawBetaPrefixDivides M step target product /\
    RawCRTInverse M product (rawBetaModulus M step target).
Proof.
  intros M hPA step target hcommon.
  set (commonFormula := PA.Formula.commonMultipleThroughTermAt
    (PA.tVar 0) (PA.tVar 1)).
  set (G := [commonFormula] : list PA.formula).
  assert (hass : PA.Formula.BProv PA.Formula.Ax_s G commonFormula).
  { apply PA.Formula.BProv_ass. unfold G. simpl. left. reflexivity. }
  pose proof
    (PA.Formula.BProv_Ax_s_betaPrefixCRTAccumulatorExistsTermAt_self
      G (PA.tVar 1) (PA.tVar 0) hass) as haccProof.
  set (e := fun _ : nat => raw_zero M).
  set (v := scons M target (scons M step e)).
  assert (hcommonSat : raw_formula_sat M v commonFormula).
  {
    unfold commonFormula.
    apply (proj2 (raw_sat_commonMultipleThroughTermAt_iff M _ _ _)).
    unfold v. cbn [raw_term_eval scons]. exact hcommon.
  }
  pose proof (raw_sat_of_BProv_axs_context M G _ hPA haccProof v)
    as hsound.
  assert (haccSat : raw_formula_sat M v
      (PA.Formula.betaPrefixCRTAccumulatorExistsTermAt
        (PA.tVar 1) (PA.tVar 0) (PA.tVar 0))).
  {
    apply hsound. intros g hg.
    unfold G in hg. simpl in hg.
    destruct hg as [hg | []]. subst g. exact hcommonSat.
  }
  unfold PA.Formula.betaPrefixCRTAccumulatorExistsTermAt in haccSat.
  cbn [raw_formula_sat] in haccSat.
  destruct haccSat as [product hproduct].
  pose proof (proj1 (raw_sat_betaPrefixCRTAccumulatorTermAt_iff
    M _ _ _ _ _) hproduct) as hraw.
  repeat rewrite raw_term_eval_rename_succ in hraw.
  unfold v in hraw. cbn [raw_term_eval scons] in hraw.
  exists product. exact hraw.
Qed.

Lemma raw_mul_comm : forall (M : RawPAModel),
  RawPASatisfies M -> forall x y : M,
  raw_mul M x y = raw_mul M y x.
Proof.
  intros M hPA x y.
  set (e := scons M x (scons M y (fun _ : nat => raw_zero M))).
  pose proof (PA.Formula.BProv_Ax_s_mul_comm_terms []
    (PA.tVar 0) (PA.tVar 1)) as hp.
  pose proof (raw_sat_of_BProv_axs M _ hPA hp e) as hs.
  unfold e in hs. cbn [raw_formula_sat raw_term_eval scons] in hs.
  exact hs.
Qed.

(** The generic Coq PAHF port stops just before the subtraction-free
    successor correction used by one-entry CRT extension.  The following
    small bridge is the missing algebraic tail; it uses only the already
    checked semiring and bounded-remainder lemmas. *)
Definition crtSuccessorCorrectionTerm
    (oldCode modulusPred newRem : PA.term) : PA.term :=
  PA.tAdd (PA.tMul modulusPred oldCode) newRem.

Lemma BProv_Ax_s_crtExtendCodeTerm_new_decomposition_of_code :
  forall G oldCode product inverse delta modulus inverseQuot
      correctionQuot newRem,
  PA.Formula.BProv PA.Formula.Ax_s G
    (PA.pEq (PA.tMul product inverse)
      (PA.tSucc (PA.tMul modulus inverseQuot))) ->
  PA.Formula.BProv PA.Formula.Ax_s G
    (PA.pEq (PA.tAdd oldCode delta)
      (PA.tAdd (PA.tMul correctionQuot modulus) newRem)) ->
  PA.Formula.BProv PA.Formula.Ax_s G
    (PA.pEq
      (PA.Formula.crtExtendCodeTerm oldCode product inverse delta)
      (PA.tAdd
        (PA.tMul
          (PA.tAdd (PA.tMul inverseQuot delta) correctionQuot)
          modulus)
        newRem)).
Proof.
  intros G oldCode product inverse delta modulus inverseQuot
    correctionQuot newRem hInverse hDelta.
  set (increment := PA.tMul inverse delta).
  set (inverseContribution := PA.tMul inverseQuot delta).
  set (addedBase := PA.tMul inverseContribution modulus).
  set (correctionBase := PA.tMul correctionQuot modulus).
  assert (hincrementAssoc : PA.Formula.BProv PA.Formula.Ax_s G
      (PA.pEq (PA.tMul product increment)
        (PA.tMul (PA.tMul product inverse) delta))).
  {
    unfold increment.
    apply PA.Formula.BProv_eqSym.
    apply PA.Formula.BProv_Ax_s_mul_assoc_terms.
  }
  assert (hinverseCong : PA.Formula.BProv PA.Formula.Ax_s G
      (PA.pEq (PA.tMul (PA.tMul product inverse) delta)
        (PA.tMul
          (PA.tSucc (PA.tMul modulus inverseQuot)) delta))).
  {
    exact (PA.Formula.BProv_eq_congr_mul_left PA.Formula.Ax_s G
      (PA.tMul product inverse)
      (PA.tSucc (PA.tMul modulus inverseQuot)) delta hInverse).
  }
  assert (hsuccMul : PA.Formula.BProv PA.Formula.Ax_s G
      (PA.pEq
        (PA.tMul (PA.tSucc (PA.tMul modulus inverseQuot)) delta)
        (PA.tAdd (PA.tMul (PA.tMul modulus inverseQuot) delta) delta))).
  { apply PA.Formula.BProv_Ax_s_succ_mul_terms. }
  assert (hbaseAssoc : PA.Formula.BProv PA.Formula.Ax_s G
      (PA.pEq (PA.tMul (PA.tMul modulus inverseQuot) delta)
        (PA.tMul modulus inverseContribution))).
  {
    unfold inverseContribution.
    apply PA.Formula.BProv_Ax_s_mul_assoc_terms.
  }
  assert (hbaseComm : PA.Formula.BProv PA.Formula.Ax_s G
      (PA.pEq (PA.tMul modulus inverseContribution) addedBase)).
  {
    unfold addedBase.
    apply PA.Formula.BProv_Ax_s_mul_comm_terms.
  }
  assert (hbase : PA.Formula.BProv PA.Formula.Ax_s G
      (PA.pEq (PA.tMul (PA.tMul modulus inverseQuot) delta) addedBase)).
  {
    exact (PA.Formula.BProv_eqTrans PA.Formula.Ax_s G _ _ _
      hbaseAssoc hbaseComm).
  }
  assert (hbaseCong : PA.Formula.BProv PA.Formula.Ax_s G
      (PA.pEq
        (PA.tAdd (PA.tMul (PA.tMul modulus inverseQuot) delta) delta)
        (PA.tAdd addedBase delta))).
  {
    exact (PA.Formula.BProv_eq_congr_add_left PA.Formula.Ax_s G
      _ _ delta hbase).
  }
  assert (hincrement : PA.Formula.BProv PA.Formula.Ax_s G
      (PA.pEq (PA.tMul product increment)
        (PA.tAdd addedBase delta))).
  {
    exact (PA.Formula.BProv_eqTrans PA.Formula.Ax_s G _ _ _
      hincrementAssoc
      (PA.Formula.BProv_eqTrans PA.Formula.Ax_s G _ _ _
        hinverseCong
        (PA.Formula.BProv_eqTrans PA.Formula.Ax_s G _ _ _
          hsuccMul hbaseCong))).
  }
  assert (hcode : PA.Formula.BProv PA.Formula.Ax_s G
      (PA.pEq
        (PA.Formula.crtExtendCodeTerm oldCode product inverse delta)
        (PA.tAdd oldCode (PA.tAdd addedBase delta)))).
  {
    unfold PA.Formula.crtExtendCodeTerm, increment in *.
    exact (PA.Formula.BProv_eq_congr_add_right PA.Formula.Ax_s G
      oldCode _ _ hincrement).
  }
  assert (hregroup1 : PA.Formula.BProv PA.Formula.Ax_s G
      (PA.pEq (PA.tAdd oldCode (PA.tAdd addedBase delta))
        (PA.tAdd (PA.tAdd oldCode addedBase) delta))).
  {
    apply PA.Formula.BProv_eqSym.
    apply PA.Formula.BProv_Ax_s_add_assoc_terms.
  }
  assert (hcomm : PA.Formula.BProv PA.Formula.Ax_s G
      (PA.pEq (PA.tAdd oldCode addedBase)
        (PA.tAdd addedBase oldCode))).
  { apply PA.Formula.BProv_Ax_s_add_comm_terms. }
  assert (hcommCong : PA.Formula.BProv PA.Formula.Ax_s G
      (PA.pEq (PA.tAdd (PA.tAdd oldCode addedBase) delta)
        (PA.tAdd (PA.tAdd addedBase oldCode) delta))).
  {
    exact (PA.Formula.BProv_eq_congr_add_left PA.Formula.Ax_s G
      _ _ delta hcomm).
  }
  assert (hregroup2 : PA.Formula.BProv PA.Formula.Ax_s G
      (PA.pEq (PA.tAdd (PA.tAdd addedBase oldCode) delta)
        (PA.tAdd addedBase (PA.tAdd oldCode delta)))).
  { apply PA.Formula.BProv_Ax_s_add_assoc_terms. }
  assert (hdeltaCong : PA.Formula.BProv PA.Formula.Ax_s G
      (PA.pEq (PA.tAdd addedBase (PA.tAdd oldCode delta))
        (PA.tAdd addedBase (PA.tAdd correctionBase newRem)))).
  {
    unfold correctionBase.
    exact (PA.Formula.BProv_eq_congr_add_right PA.Formula.Ax_s G
      addedBase _ _ hDelta).
  }
  assert (hregroup3 : PA.Formula.BProv PA.Formula.Ax_s G
      (PA.pEq (PA.tAdd addedBase (PA.tAdd correctionBase newRem))
        (PA.tAdd (PA.tAdd addedBase correctionBase) newRem))).
  {
    apply PA.Formula.BProv_eqSym.
    apply PA.Formula.BProv_Ax_s_add_assoc_terms.
  }
  assert (hquotMul : PA.Formula.BProv PA.Formula.Ax_s G
      (PA.pEq
        (PA.tMul (PA.tAdd inverseContribution correctionQuot) modulus)
        (PA.tAdd addedBase correctionBase))).
  {
    unfold addedBase, correctionBase.
    apply PA.Formula.BProv_Ax_s_add_mul_terms.
  }
  assert (hquotCong : PA.Formula.BProv PA.Formula.Ax_s G
      (PA.pEq (PA.tAdd (PA.tAdd addedBase correctionBase) newRem)
        (PA.tAdd
          (PA.tMul (PA.tAdd inverseContribution correctionQuot) modulus)
          newRem))).
  {
    exact (PA.Formula.BProv_eq_congr_add_left PA.Formula.Ax_s G
      _ _ newRem
      (PA.Formula.BProv_eqSym PA.Formula.Ax_s G _ _ hquotMul)).
  }
  unfold inverseContribution.
  exact (PA.Formula.BProv_eqTrans PA.Formula.Ax_s G _ _ _ hcode
    (PA.Formula.BProv_eqTrans PA.Formula.Ax_s G _ _ _ hregroup1
      (PA.Formula.BProv_eqTrans PA.Formula.Ax_s G _ _ _ hcommCong
        (PA.Formula.BProv_eqTrans PA.Formula.Ax_s G _ _ _ hregroup2
          (PA.Formula.BProv_eqTrans PA.Formula.Ax_s G _ _ _ hdeltaCong
            (PA.Formula.BProv_eqTrans PA.Formula.Ax_s G _ _ _
              hregroup3 hquotCong)))))).
Qed.

Lemma BProv_Ax_s_crtSuccessorCorrectionTerm : forall G
    oldCode modulusPred newRem,
  PA.Formula.BProv PA.Formula.Ax_s G
    (PA.pEq
      (PA.tAdd oldCode
        (crtSuccessorCorrectionTerm oldCode modulusPred newRem))
      (PA.tAdd (PA.tMul oldCode (PA.tSucc modulusPred)) newRem)).
Proof.
  intros G oldCode modulusPred newRem.
  assert (hassoc : PA.Formula.BProv PA.Formula.Ax_s G
      (PA.pEq
        (PA.tAdd oldCode
          (PA.tAdd (PA.tMul modulusPred oldCode) newRem))
        (PA.tAdd
          (PA.tAdd oldCode (PA.tMul modulusPred oldCode)) newRem))).
  {
    apply PA.Formula.BProv_eqSym.
    apply PA.Formula.BProv_Ax_s_add_assoc_terms.
  }
  assert (hmulComm : PA.Formula.BProv PA.Formula.Ax_s G
      (PA.pEq (PA.tMul modulusPred oldCode)
        (PA.tMul oldCode modulusPred))).
  { apply PA.Formula.BProv_Ax_s_mul_comm_terms. }
  assert (hinnerComm1 : PA.Formula.BProv PA.Formula.Ax_s G
      (PA.pEq (PA.tAdd oldCode (PA.tMul modulusPred oldCode))
        (PA.tAdd oldCode (PA.tMul oldCode modulusPred)))).
  {
    exact (PA.Formula.BProv_eq_congr_add_right PA.Formula.Ax_s G
      oldCode _ _ hmulComm).
  }
  assert (hinnerComm2 : PA.Formula.BProv PA.Formula.Ax_s G
      (PA.pEq (PA.tAdd oldCode (PA.tMul oldCode modulusPred))
        (PA.tAdd (PA.tMul oldCode modulusPred) oldCode))).
  { apply PA.Formula.BProv_Ax_s_add_comm_terms. }
  assert (hmulSucc : PA.Formula.BProv PA.Formula.Ax_s G
      (PA.pEq (PA.tMul oldCode (PA.tSucc modulusPred))
        (PA.tAdd (PA.tMul oldCode modulusPred) oldCode))).
  {
    apply PA.Formula.BProv_weaken_nil.
    apply PA.Formula.BProv_Ax_s_mulSucc_terms.
  }
  assert (hinner : PA.Formula.BProv PA.Formula.Ax_s G
      (PA.pEq (PA.tAdd oldCode (PA.tMul modulusPred oldCode))
        (PA.tMul oldCode (PA.tSucc modulusPred)))).
  {
    exact (PA.Formula.BProv_eqTrans PA.Formula.Ax_s G _ _ _
      hinnerComm1
      (PA.Formula.BProv_eqTrans PA.Formula.Ax_s G _ _ _
        hinnerComm2
        (PA.Formula.BProv_eqSym PA.Formula.Ax_s G _ _ hmulSucc))).
  }
  assert (hinnerCong : PA.Formula.BProv PA.Formula.Ax_s G
      (PA.pEq
        (PA.tAdd (PA.tAdd oldCode (PA.tMul modulusPred oldCode)) newRem)
        (PA.tAdd (PA.tMul oldCode (PA.tSucc modulusPred)) newRem))).
  {
    exact (PA.Formula.BProv_eq_congr_add_left PA.Formula.Ax_s G
      _ _ newRem hinner).
  }
  unfold crtSuccessorCorrectionTerm.
  exact (PA.Formula.BProv_eqTrans PA.Formula.Ax_s G _ _ _
    hassoc hinnerCong).
Qed.

Lemma BProv_Ax_s_remTermTermAt_crtExtend_successor_new :
  forall G oldCode product inverse modulusPred inverseQuot newRem,
  PA.Formula.BProv PA.Formula.Ax_s G
    (PA.pEq (PA.tMul product inverse)
      (PA.tSucc (PA.tMul (PA.tSucc modulusPred) inverseQuot))) ->
  PA.Formula.BProv PA.Formula.Ax_s G
    (PA.Formula.ltTermAt newRem (PA.tSucc modulusPred)) ->
  PA.Formula.BProv PA.Formula.Ax_s G
    (PA.Formula.remTermTermAt newRem
      (PA.Formula.crtExtendCodeTerm oldCode product inverse
        (crtSuccessorCorrectionTerm oldCode modulusPred newRem))
      (PA.tSucc modulusPred)).
Proof.
  intros G oldCode product inverse modulusPred inverseQuot newRem
    hInverse hBound.
  set (delta := crtSuccessorCorrectionTerm oldCode modulusPred newRem).
  set (quotient := PA.tAdd (PA.tMul inverseQuot delta) oldCode).
  assert (hDelta : PA.Formula.BProv PA.Formula.Ax_s G
      (PA.pEq (PA.tAdd oldCode delta)
        (PA.tAdd (PA.tMul oldCode (PA.tSucc modulusPred)) newRem))).
  {
    unfold delta.
    apply BProv_Ax_s_crtSuccessorCorrectionTerm.
  }
  assert (hdecomp : PA.Formula.BProv PA.Formula.Ax_s G
      (PA.pEq
        (PA.Formula.crtExtendCodeTerm oldCode product inverse delta)
        (PA.tAdd (PA.tMul quotient (PA.tSucc modulusPred)) newRem))).
  {
    unfold quotient.
    exact (BProv_Ax_s_crtExtendCodeTerm_new_decomposition_of_code
      G oldCode product inverse delta (PA.tSucc modulusPred)
      inverseQuot oldCode newRem hInverse hDelta).
  }
  exact (PA.Formula.BProv_Ax_s_remTermTermAt_of_eq_add_mul_terms
    G newRem
    (PA.Formula.crtExtendCodeTerm oldCode product inverse delta)
    (PA.tSucc modulusPred) quotient hBound hdecomp).
Qed.

Lemma BProv_Ax_s_betaTermTermAt_crtExtend_successor_new :
  forall G oldCode product inverse step idx inverseQuot newOut,
  PA.Formula.BProv PA.Formula.Ax_s G
    (PA.pEq (PA.tMul product inverse)
      (PA.tSucc
        (PA.tMul (PA.Formula.betaModTermTerm step idx) inverseQuot))) ->
  PA.Formula.BProv PA.Formula.Ax_s G
    (PA.Formula.ltTermAt newOut
      (PA.Formula.betaModTermTerm step idx)) ->
  PA.Formula.BProv PA.Formula.Ax_s G
    (PA.Formula.betaTermTermAt newOut
      (PA.Formula.crtExtendCodeTerm oldCode product inverse
        (crtSuccessorCorrectionTerm oldCode
          (PA.tMul (PA.tSucc idx) step) newOut))
      step idx).
Proof.
  intros G oldCode product inverse step idx inverseQuot newOut
    hInverse hBound.
  set (modulusPred := PA.tMul (PA.tSucc idx) step).
  set (delta := crtSuccessorCorrectionTerm oldCode modulusPred newOut).
  assert (hrem : PA.Formula.BProv PA.Formula.Ax_s G
      (PA.Formula.remTermTermAt newOut
        (PA.Formula.crtExtendCodeTerm oldCode product inverse delta)
        (PA.tSucc modulusPred))).
  {
    apply (BProv_Ax_s_remTermTermAt_crtExtend_successor_new G
      oldCode product inverse modulusPred inverseQuot newOut).
    - unfold modulusPred in *.
      exact hInverse.
    - unfold modulusPred in *.
      exact hBound.
  }
  apply (PA.Formula.BProv_Ax_s_betaTermTermAt_of_rem G newOut
    (PA.Formula.crtExtendCodeTerm oldCode product inverse delta)
    step idx (PA.tSucc modulusPred)).
  - unfold modulusPred, PA.Formula.betaModTermTerm.
    apply PA.Formula.BProv_eqRefl.
  - exact hrem.
Qed.

Definition rawCrtExtendCode (M : RawPAModel)
    (oldCode product inverse delta : M) : M :=
  raw_add M oldCode (raw_mul M product (raw_mul M inverse delta)).

Definition rawCrtSuccessorCorrection (M : RawPAModel)
    (oldCode modulusPred newRem : M) : M :=
  raw_add M (raw_mul M modulusPred oldCode) newRem.

Lemma raw_term_eval_crtExtendCodeTerm : forall (M : RawPAModel)
    (oldCode product inverse delta : PA.term) (e : nat -> M),
  raw_term_eval M e
      (PA.Formula.crtExtendCodeTerm oldCode product inverse delta) =
  rawCrtExtendCode M
    (raw_term_eval M e oldCode) (raw_term_eval M e product)
    (raw_term_eval M e inverse) (raw_term_eval M e delta).
Proof. reflexivity. Qed.

Lemma raw_term_eval_crtSuccessorCorrectionTerm :
  forall (M : RawPAModel) (oldCode modulusPred newRem : PA.term)
      (e : nat -> M),
  raw_term_eval M e
      (crtSuccessorCorrectionTerm oldCode modulusPred newRem) =
  rawCrtSuccessorCorrection M
    (raw_term_eval M e oldCode) (raw_term_eval M e modulusPred)
    (raw_term_eval M e newRem).
Proof. reflexivity. Qed.

Theorem raw_betaEntry_crtExtend_preserve : forall (M : RawPAModel),
  RawPASatisfies M ->
  forall out oldCode product inverse delta step idx factor : M,
  RawBetaEntry M out oldCode step idx ->
  product = raw_mul M factor (rawBetaModulus M step idx) ->
  RawBetaEntry M out
    (rawCrtExtendCode M oldCode product inverse delta) step idx.
Proof.
  intros M hPA out oldCode product inverse delta step idx factor
    hentry hproduct.
  set (fentry := PA.Formula.betaTermTermAt
    (PA.tVar 0) (PA.tVar 1) (PA.tVar 5) (PA.tVar 6)).
  set (fproduct := PA.pEq (PA.tVar 2)
    (PA.tMul (PA.tVar 7)
      (PA.Formula.betaModTermTerm (PA.tVar 5) (PA.tVar 6)))).
  set (G := [fentry; fproduct] : list PA.formula).
  assert (hassEntry : PA.Formula.BProv PA.Formula.Ax_s G fentry).
  { apply PA.Formula.BProv_ass. unfold G. simpl. left. reflexivity. }
  assert (hassProduct : PA.Formula.BProv PA.Formula.Ax_s G fproduct).
  {
    apply PA.Formula.BProv_ass. unfold G. simpl. right. left. reflexivity.
  }
  pose proof (PA.Formula.BProv_Ax_s_betaTermTermAt_crtExtend_preserve
    G (PA.tVar 0) (PA.tVar 1) (PA.tVar 2) (PA.tVar 3)
    (PA.tVar 4) (PA.tVar 5) (PA.tVar 6) (PA.tVar 7)
    hassEntry hassProduct) as hp.
  set (e := fun _ : nat => raw_zero M).
  set (v := scons M out (scons M oldCode (scons M product
    (scons M inverse (scons M delta (scons M step
      (scons M idx (scons M factor e)))))))).
  assert (hsatEntry : raw_formula_sat M v fentry).
  {
    unfold fentry.
    apply (proj2 (raw_sat_betaTermTermAt_iff M _ _ _ _ _)).
    unfold v. cbn [raw_term_eval scons]. exact hentry.
  }
  assert (hsatProduct : raw_formula_sat M v fproduct).
  {
    unfold fproduct, v.
    cbn [raw_formula_sat raw_term_eval scons]. exact hproduct.
  }
  pose proof (raw_sat_of_BProv_axs_context M G _ hPA hp v)
    as hsound.
  assert (hsat : raw_formula_sat M v
      (PA.Formula.betaTermTermAt (PA.tVar 0)
        (PA.Formula.crtExtendCodeTerm (PA.tVar 1) (PA.tVar 2)
          (PA.tVar 3) (PA.tVar 4))
        (PA.tVar 5) (PA.tVar 6))).
  {
    apply hsound. intros g hg.
    unfold G in hg. simpl in hg.
    destruct hg as [hg | [hg | []]]; subst g; assumption.
  }
  pose proof (proj1 (raw_sat_betaTermTermAt_iff M _ _ _ _ _) hsat)
    as hraw.
  unfold v in hraw.
  cbn [raw_term_eval scons PA.Formula.crtExtendCodeTerm
    rawCrtExtendCode] in hraw.
  exact hraw.
Qed.

Theorem raw_betaEntry_crtExtend_successor_new :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall oldCode product inverse step idx inverseQuot newOut : M,
  raw_mul M product inverse =
    raw_succ M
      (raw_mul M (rawBetaModulus M step idx) inverseQuot) ->
  rawLt M newOut (rawBetaModulus M step idx) ->
  let modulusPred := raw_mul M (raw_succ M idx) step in
  let delta := rawCrtSuccessorCorrection M oldCode modulusPred newOut in
  RawBetaEntry M newOut
    (rawCrtExtendCode M oldCode product inverse delta) step idx.
Proof.
  intros M hPA oldCode product inverse step idx inverseQuot newOut
    hInverse hBound modulusPred delta.
  set (fInverse := PA.pEq
    (PA.tMul (PA.tVar 1) (PA.tVar 2))
    (PA.tSucc (PA.tMul
      (PA.Formula.betaModTermTerm (PA.tVar 3) (PA.tVar 4))
      (PA.tVar 5)))).
  set (fBound := PA.Formula.ltTermAt (PA.tVar 6)
    (PA.Formula.betaModTermTerm (PA.tVar 3) (PA.tVar 4))).
  set (G := [fInverse; fBound] : list PA.formula).
  assert (hassInverse : PA.Formula.BProv PA.Formula.Ax_s G fInverse).
  { apply PA.Formula.BProv_ass. unfold G. simpl. left. reflexivity. }
  assert (hassBound : PA.Formula.BProv PA.Formula.Ax_s G fBound).
  {
    apply PA.Formula.BProv_ass. unfold G. simpl. right. left. reflexivity.
  }
  pose proof (BProv_Ax_s_betaTermTermAt_crtExtend_successor_new
    G (PA.tVar 0) (PA.tVar 1) (PA.tVar 2) (PA.tVar 3)
    (PA.tVar 4) (PA.tVar 5) (PA.tVar 6)
    hassInverse hassBound) as hp.
  set (e := fun _ : nat => raw_zero M).
  set (v := scons M oldCode (scons M product (scons M inverse
    (scons M step (scons M idx (scons M inverseQuot
      (scons M newOut e))))))).
  assert (hsatInverse : raw_formula_sat M v fInverse).
  {
    unfold fInverse, v.
    cbn [raw_formula_sat raw_term_eval scons]. exact hInverse.
  }
  assert (hsatBound : raw_formula_sat M v fBound).
  {
    unfold fBound.
    apply (proj2 (raw_sat_ltTermAt_iff M _ _ _)).
    unfold v. cbn [raw_term_eval scons]. exact hBound.
  }
  pose proof (raw_sat_of_BProv_axs_context M G _ hPA hp v)
    as hsound.
  assert (hsat : raw_formula_sat M v
      (PA.Formula.betaTermTermAt (PA.tVar 6)
        (PA.Formula.crtExtendCodeTerm (PA.tVar 0) (PA.tVar 1)
          (PA.tVar 2)
          (crtSuccessorCorrectionTerm (PA.tVar 0)
            (PA.tMul (PA.tSucc (PA.tVar 4)) (PA.tVar 3))
            (PA.tVar 6)))
        (PA.tVar 3) (PA.tVar 4))).
  {
    apply hsound. intros g hg.
    unfold G in hg. simpl in hg.
    destruct hg as [hg | [hg | []]]; subst g; assumption.
  }
  pose proof (proj1 (raw_sat_betaTermTermAt_iff M _ _ _ _ _) hsat)
    as hraw.
  unfold v in hraw.
  cbn [raw_term_eval scons PA.Formula.crtExtendCodeTerm
    crtSuccessorCorrectionTerm rawCrtExtendCode
    rawCrtSuccessorCorrection] in hraw.
  exact hraw.
Qed.

Definition RawBetaCodeExtension (M : RawPAModel)
    (oldCode step target newOut newCode : M) : Prop :=
  (forall idx, rawLt M idx target -> forall out,
    RawBetaEntry M out oldCode step idx ->
    RawBetaEntry M out newCode step idx) /\
  RawBetaEntry M newOut newCode step target.

Definition betaPrefixAgreementTermAt
    (oldCode newCode step bound : PA.term) : PA.formula :=
  PA.pAll (PA.pImp
    (PA.Formula.ltTermAt (PA.tVar 0) (PA.Term.rename S bound))
    (PA.pAll (PA.pImp
      (PA.Formula.betaTermTermAt (PA.tVar 0)
        (PA.Term.rename (fun n => n + 2) oldCode)
        (PA.Term.rename (fun n => n + 2) step)
        (PA.tVar 1))
      (PA.Formula.betaTermTermAt (PA.tVar 0)
        (PA.Term.rename (fun n => n + 2) newCode)
        (PA.Term.rename (fun n => n + 2) step)
        (PA.tVar 1))))).

Definition betaCodeExtensionTermAt
    (oldCode step target newOut newCode : PA.term) : PA.formula :=
  PA.pAnd (betaPrefixAgreementTermAt oldCode newCode step target)
    (PA.Formula.betaTermTermAt newOut newCode step target).

(** Output variable 0; parameters 1--4 are old code, step, target, output. *)
Definition betaCodeExtensionSelectorBody : PA.formula :=
  betaCodeExtensionTermAt
    (PA.tVar 1) (PA.tVar 2) (PA.tVar 3) (PA.tVar 4) (PA.tVar 0).

Lemma raw_sat_betaPrefixAgreementTermAt_iff :
  forall (M : RawPAModel) (oldCode newCode step bound : PA.term)
      (e : nat -> M),
  raw_formula_sat M e
      (betaPrefixAgreementTermAt oldCode newCode step bound) <->
  forall idx, rawLt M idx (raw_term_eval M e bound) -> forall out,
    RawBetaEntry M out (raw_term_eval M e oldCode)
      (raw_term_eval M e step) idx ->
    RawBetaEntry M out (raw_term_eval M e newCode)
      (raw_term_eval M e step) idx.
Proof.
  intros M oldCode newCode step bound e.
  unfold betaPrefixAgreementTermAt.
  cbn [raw_formula_sat]. split.
  - intros h idx hlt out hold.
    assert (hltSat : raw_formula_sat M (scons M idx e)
        (PA.Formula.ltTermAt
          (PA.tVar 0) (PA.Term.rename S bound))).
    {
      apply (proj2 (raw_sat_ltTermAt_iff M _ _ _)).
      rewrite raw_term_eval_rename_succ.
      cbn [raw_term_eval scons]. exact hlt.
    }
    assert (holdSat : raw_formula_sat M
        (scons M out (scons M idx e))
        (PA.Formula.betaTermTermAt (PA.tVar 0)
          (PA.Term.rename (fun n => n + 2) oldCode)
          (PA.Term.rename (fun n => n + 2) step)
          (PA.tVar 1))).
    {
      apply (proj2 (raw_sat_betaTermTermAt_iff M _ _ _ _ _)).
      repeat rewrite raw_term_eval_rename_two_scons.
      cbn [raw_term_eval scons]. exact hold.
    }
    pose proof (h idx hltSat out holdSat) as hnewSat.
    pose proof (proj1 (raw_sat_betaTermTermAt_iff M _ _ _ _ _)
      hnewSat) as hnew.
    repeat rewrite raw_term_eval_rename_two_scons in hnew.
    cbn [raw_term_eval scons] in hnew. exact hnew.
  - intros h idx hltSat out holdSat.
    pose proof (proj1 (raw_sat_ltTermAt_iff M _ _ _) hltSat)
      as hlt.
    rewrite raw_term_eval_rename_succ in hlt.
    cbn [raw_term_eval scons] in hlt.
    pose proof (proj1 (raw_sat_betaTermTermAt_iff M _ _ _ _ _)
      holdSat) as hold.
    repeat rewrite raw_term_eval_rename_two_scons in hold.
    cbn [raw_term_eval scons] in hold.
    pose proof (h idx hlt out hold) as hnew.
    apply (proj2 (raw_sat_betaTermTermAt_iff M _ _ _ _ _)).
    repeat rewrite raw_term_eval_rename_two_scons.
    cbn [raw_term_eval scons]. exact hnew.
Qed.

Lemma raw_sat_betaCodeExtensionTermAt_iff :
  forall (M : RawPAModel) (oldCode step target newOut newCode : PA.term)
      (e : nat -> M),
  raw_formula_sat M e
      (betaCodeExtensionTermAt oldCode step target newOut newCode) <->
  RawBetaCodeExtension M
    (raw_term_eval M e oldCode) (raw_term_eval M e step)
    (raw_term_eval M e target) (raw_term_eval M e newOut)
    (raw_term_eval M e newCode).
Proof.
  intros M oldCode step target newOut newCode e.
  unfold betaCodeExtensionTermAt, RawBetaCodeExtension.
  cbn [raw_formula_sat].
  rewrite raw_sat_betaPrefixAgreementTermAt_iff.
  rewrite raw_sat_betaTermTermAt_iff.
  reflexivity.
Qed.

Lemma raw_sat_betaCodeExtensionSelectorBody_iff :
  forall (M : RawPAModel) oldCode step target newOut newCode
      (e : nat -> M),
  raw_formula_sat M
    (scons M newCode
      (scons M oldCode (scons M step (scons M target
        (scons M newOut e)))))
    betaCodeExtensionSelectorBody <->
  RawBetaCodeExtension M oldCode step target newOut newCode.
Proof.
  intros M oldCode step target newOut newCode e.
  unfold betaCodeExtensionSelectorBody.
  rewrite raw_sat_betaCodeExtensionTermAt_iff.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Theorem raw_betaCodeExtension_exists : forall (M : RawPAModel),
  RawPASatisfies M ->
  forall oldCode step target newOut : M,
  RawCommonMultipleThrough M target step ->
  rawLt M newOut (rawBetaModulus M step target) ->
  exists newCode, RawBetaCodeExtension M
    oldCode step target newOut newCode.
Proof.
  intros M hPA oldCode step target newOut hcommon hBound.
  destruct (raw_betaPrefixCRTAccumulator_self M hPA step target hcommon)
    as [product [hprefix [inverse [inverseQuot hInverse]]]].
  set (modulusPred := raw_mul M (raw_succ M target) step).
  set (delta := rawCrtSuccessorCorrection M
    oldCode modulusPred newOut).
  set (newCode := rawCrtExtendCode M oldCode product inverse delta).
  exists newCode. split.
  - intros idx hlt out hentry.
    destruct (hprefix idx hlt) as [factor hfactor].
    assert (hproduct : product =
        raw_mul M factor (rawBetaModulus M step idx)).
    {
      rewrite <- hfactor.
      apply raw_mul_comm. exact hPA.
    }
    unfold newCode.
    exact (raw_betaEntry_crtExtend_preserve M hPA out oldCode
      product inverse delta step idx factor hentry hproduct).
  - unfold newCode, delta, modulusPred.
    exact (raw_betaEntry_crtExtend_successor_new M hPA oldCode
      product inverse step target inverseQuot newOut
      hInverse hBound).
Qed.

Definition rawCanonicalBetaExtensionCode (M : RawPAModel)
    (oldCode step target newOut : M) : M :=
  rawCanonicalSelector M betaCodeExtensionSelectorBody
    (scons M oldCode (scons M step
      (scons M target (scons M newOut
        (fun _ : nat => raw_zero M))))).

Theorem rawCanonicalBetaExtensionCode_spec : forall (M : RawPAModel),
  RawPASatisfies M -> forall oldCode step target newOut : M,
  RawCommonMultipleThrough M target step ->
  rawLt M newOut (rawBetaModulus M step target) ->
  RawBetaCodeExtension M oldCode step target newOut
    (rawCanonicalBetaExtensionCode M oldCode step target newOut).
Proof.
  intros M hPA oldCode step target newOut hcommon hBound.
  destruct (raw_betaCodeExtension_exists M hPA oldCode step target
    newOut hcommon hBound) as [newCode hext].
  set (env := scons M oldCode (scons M step
    (scons M target (scons M newOut
      (fun _ : nat => raw_zero M))))).
  assert (hex : exists d,
      raw_formula_sat M (scons M d env)
        betaCodeExtensionSelectorBody).
  {
    exists newCode. unfold env.
    apply (proj2 (raw_sat_betaCodeExtensionSelectorBody_iff
      M oldCode step target newOut newCode
      (fun _ : nat => raw_zero M))).
    exact hext.
  }
  pose proof (rawCanonicalSelector_witnesses M
    (raw_definable_least_number_of_pa M hPA)
    betaCodeExtensionSelectorBody env hex) as hselected.
  unfold rawCanonicalBetaExtensionCode, env in *.
  apply (proj1 (raw_sat_betaCodeExtensionSelectorBody_iff
    M oldCode step target newOut
    (rawCanonicalSelector M betaCodeExtensionSelectorBody
      (scons M oldCode (scons M step
        (scons M target (scons M newOut
          (fun _ : nat => raw_zero M))))))
    (fun _ : nat => raw_zero M))).
  exact hselected.
Qed.

Lemma raw_eq_of_closed_bprov : forall (M : RawPAModel),
  RawPASatisfies M -> forall (a b : PA.term) (e : nat -> M),
  PA.Formula.BProv PA.Formula.Ax_s [] (PA.pEq a b) ->
  raw_term_eval M e a = raw_term_eval M e b.
Proof.
  intros M hPA a b e hp.
  exact (raw_sat_of_BProv_axs M (PA.pEq a b) hPA hp e).
Qed.

Lemma raw_add_assoc : forall (M : RawPAModel),
  RawPASatisfies M -> forall x y z : M,
  raw_add M (raw_add M x y) z = raw_add M x (raw_add M y z).
Proof.
  intros M hPA x y z.
  set (e := scons M x (scons M y
    (scons M z (fun _ : nat => raw_zero M)))).
  pose proof (raw_eq_of_closed_bprov M hPA
    (PA.tAdd (PA.tAdd (PA.tVar 0) (PA.tVar 1)) (PA.tVar 2))
    (PA.tAdd (PA.tVar 0) (PA.tAdd (PA.tVar 1) (PA.tVar 2))) e
    (PA.Formula.BProv_Ax_s_add_assoc_terms []
      (PA.tVar 0) (PA.tVar 1) (PA.tVar 2))) as h.
  unfold e in h. cbn [raw_term_eval scons] in h. exact h.
Qed.

Lemma raw_add_comm : forall (M : RawPAModel),
  RawPASatisfies M -> forall x y : M,
  raw_add M x y = raw_add M y x.
Proof.
  intros M hPA x y.
  set (e := scons M x (scons M y (fun _ : nat => raw_zero M))).
  pose proof (raw_eq_of_closed_bprov M hPA
    (PA.tAdd (PA.tVar 0) (PA.tVar 1))
    (PA.tAdd (PA.tVar 1) (PA.tVar 0)) e
    (PA.Formula.BProv_Ax_s_add_comm_terms []
      (PA.tVar 0) (PA.tVar 1))) as h.
  unfold e in h. cbn [raw_term_eval scons] in h. exact h.
Qed.

Lemma raw_add_succ : forall (M : RawPAModel),
  RawPASatisfies M -> forall x y : M,
  raw_add M x (raw_succ M y) = raw_succ M (raw_add M x y).
Proof.
  intros M hPA x y.
  set (e := scons M x (scons M y (fun _ : nat => raw_zero M))).
  pose proof (raw_eq_of_closed_bprov M hPA
    (PA.tAdd (PA.tVar 0) (PA.tSucc (PA.tVar 1)))
    (PA.tSucc (PA.tAdd (PA.tVar 0) (PA.tVar 1))) e
    (PA.Formula.BProv_Ax_s_addSucc_terms nil
      (PA.tVar 0) (PA.tVar 1))) as h.
  unfold e in h. cbn [raw_term_eval scons] in h. exact h.
Qed.

Lemma raw_mul_assoc : forall (M : RawPAModel),
  RawPASatisfies M -> forall x y z : M,
  raw_mul M (raw_mul M x y) z = raw_mul M x (raw_mul M y z).
Proof.
  intros M hPA x y z.
  set (e := scons M x (scons M y
    (scons M z (fun _ : nat => raw_zero M)))).
  pose proof (raw_eq_of_closed_bprov M hPA
    (PA.tMul (PA.tMul (PA.tVar 0) (PA.tVar 1)) (PA.tVar 2))
    (PA.tMul (PA.tVar 0) (PA.tMul (PA.tVar 1) (PA.tVar 2))) e
    (PA.Formula.BProv_Ax_s_mul_assoc_terms []
      (PA.tVar 0) (PA.tVar 1) (PA.tVar 2))) as h.
  unfold e in h. cbn [raw_term_eval scons] in h. exact h.
Qed.

Lemma raw_succ_mul : forall (M : RawPAModel),
  RawPASatisfies M -> forall x y : M,
  raw_mul M (raw_succ M x) y =
    raw_add M (raw_mul M x y) y.
Proof.
  intros M hPA x y.
  set (e := scons M x (scons M y (fun _ : nat => raw_zero M))).
  pose proof (raw_eq_of_closed_bprov M hPA
    (PA.tMul (PA.tSucc (PA.tVar 0)) (PA.tVar 1))
    (PA.tAdd (PA.tMul (PA.tVar 0) (PA.tVar 1)) (PA.tVar 1)) e
    (PA.Formula.BProv_Ax_s_succ_mul_terms []
      (PA.tVar 0) (PA.tVar 1))) as h.
  unfold e in h. cbn [raw_term_eval scons] in h. exact h.
Qed.

Lemma raw_mul_numeral_values : forall (M : RawPAModel),
  RawPASatisfies M -> forall m n,
  raw_mul M (rawNumeralValue M m) (rawNumeralValue M n) =
    rawNumeralValue M (m * n).
Proof.
  intros M hPA m n.
  set (e := fun _ : nat => raw_zero M).
  pose proof (raw_eq_of_closed_bprov M hPA
    (PA.tMul (PA.Term.numeral m) (PA.Term.numeral n))
    (PA.Term.numeral (m * n)) e
    (PA.Formula.BProv_Ax_s_mulNumerals nil m n)) as h.
  cbn [raw_term_eval] in h.
  rewrite !raw_term_eval_numeral in h. exact h.
Qed.

Lemma raw_le_trans : forall (M : RawPAModel),
  RawPASatisfies M -> forall x y z : M,
  rawLe M x y -> rawLe M y z -> rawLe M x z.
Proof.
  intros M hPA x y z [a ha] [b hb].
  exists (raw_add M a b).
  rewrite <- raw_add_assoc by exact hPA.
  rewrite ha. exact hb.
Qed.

Lemma raw_lt_to_le : forall (M : RawPAModel),
  forall x y : M, rawLt M x y -> rawLe M x y.
Proof.
  intros M x y [d hd]. exists (raw_succ M d). exact hd.
Qed.

Lemma raw_lt_succ_of_le : forall (M : RawPAModel),
  RawPASatisfies M -> forall x y : M,
  rawLe M x y -> rawLt M x (raw_succ M y).
Proof.
  intros M hPA x y [d hd]. exists d.
  rewrite raw_add_succ by exact hPA.
  now rewrite hd.
Qed.

Fixpoint rawListSum (M : RawPAModel) (xs : list M) : M :=
  match xs with
  | [] => raw_zero M
  | x :: tail => raw_add M x (rawListSum M tail)
  end.

Lemma rawListSum_nth_decompose : forall (M : RawPAModel),
  RawPASatisfies M -> forall (xs : list M) i x,
  nth_error xs i = Some x ->
  exists rest, raw_add M x rest = rawListSum M xs.
Proof.
  intros M hPA xs. induction xs as [|head tail IH]; intros i x hnth.
  - destruct i; discriminate.
  - destruct i as [|i].
    + simpl in hnth. inversion hnth; subst x.
      exists (rawListSum M tail). reflexivity.
    + simpl in hnth.
      destruct (IH i x hnth) as [rest hrest].
      exists (raw_add M head rest).
      rewrite <- raw_add_assoc by exact hPA.
      rewrite (raw_add_comm M hPA x head).
      rewrite raw_add_assoc by exact hPA.
      now rewrite hrest.
Qed.

Lemma fact_divides_through : forall n k,
  1 <= k -> k <= n -> exists q, k * q = fact n.
Proof.
  induction n as [|n IH]; intros k hk1 hkn.
  - lia.
  - destruct (Nat.eq_dec k (S n)) as [-> | hne].
    + exists (fact n). simpl. reflexivity.
    + assert (hk : k <= n) by lia.
      destruct (IH k hk1 hk) as [q hq].
      exists (q * S n). simpl. nia.
Qed.

Definition rawFiniteCodingStep (M : RawPAModel) (xs : list M) : M :=
  raw_mul M (rawNumeralValue M (fact (length xs)))
    (raw_succ M (rawListSum M xs)).

Lemma raw_lt_numeralValue_cases_for_coding : forall (M : RawPAModel),
  RawPASatisfies M -> forall (x : M) n,
  rawLt M x (rawNumeralValue M n) ->
  exists k, k < n /\ x = rawNumeralValue M k.
Proof.
  intros M hPA x n. revert x.
  induction n as [|n IH]; intros x hlt.
  - cbn [rawNumeralValue] in hlt.
    exfalso. exact (raw_not_lt_zero M hPA x hlt).
  - cbn [rawNumeralValue] in hlt.
    destruct (raw_lt_succ_cases M hPA x (rawNumeralValue M n) hlt)
      as [hprev | heq].
    + destruct (IH x hprev) as [k [hk hx]].
      exists k. split; [lia | exact hx].
    + exists n. split; [lia | exact heq].
Qed.

Lemma rawFiniteCodingStep_common : forall (M : RawPAModel),
  RawPASatisfies M -> forall (xs : list M) i,
  i <= length xs ->
  RawCommonMultipleThrough M (rawNumeralValue M i)
    (rawFiniteCodingStep M xs).
Proof.
  intros M hPA xs i hi idx hidx.
  destruct (raw_lt_numeralValue_cases_for_coding M hPA idx i hidx)
    as [k [hki hidxEq]].
  subst idx.
  destruct (fact_divides_through (length xs) (S k))
    as [q hq]; [lia | lia |].
  exists (raw_mul M (rawNumeralValue M q)
    (raw_succ M (rawListSum M xs))).
  unfold rawFiniteCodingStep.
  change (raw_mul M (rawNumeralValue M (S k))
    (raw_mul M (rawNumeralValue M q)
      (raw_succ M (rawListSum M xs))) =
    raw_mul M (rawNumeralValue M (fact (length xs)))
      (raw_succ M (rawListSum M xs))).
  rewrite <- raw_mul_assoc by exact hPA.
  rewrite raw_mul_numeral_values by exact hPA.
  now rewrite hq.
Qed.

Lemma rawFiniteCodingStep_entry_bound : forall (M : RawPAModel),
  RawPASatisfies M -> forall (xs : list M) i x,
  nth_error xs i = Some x ->
  rawLt M x
    (rawBetaModulus M (rawFiniteCodingStep M xs)
      (rawNumeralValue M i)).
Proof.
  intros M hPA xs i x hnth.
  destruct (rawListSum_nth_decompose M hPA xs i x hnth)
    as [rest hsum].
  assert (hleXSum : rawLe M x (rawListSum M xs)).
  { exists rest. exact hsum. }
  pose proof (raw_lt_succ_of_le M hPA x (rawListSum M xs) hleXSum)
    as hltXSuccSum.
  assert (hfact : fact (length xs) <> 0).
  { apply fact_neq_0. }
  destruct (fact (length xs)) as [|c] eqn:hfactEq.
  { contradiction. }
  assert (hleSuccSumStep : rawLe M
      (raw_succ M (rawListSum M xs)) (rawFiniteCodingStep M xs)).
  {
    exists (raw_mul M (rawNumeralValue M c)
      (raw_succ M (rawListSum M xs))).
    unfold rawFiniteCodingStep. rewrite hfactEq. simpl.
    rewrite raw_succ_mul by exact hPA.
    apply raw_add_comm. exact hPA.
  }
  assert (hleStepPred : rawLe M (rawFiniteCodingStep M xs)
      (raw_mul M (raw_succ M (rawNumeralValue M i))
        (rawFiniteCodingStep M xs))).
  {
    exists (raw_mul M (rawNumeralValue M i)
      (rawFiniteCodingStep M xs)).
    rewrite raw_succ_mul by exact hPA.
    apply raw_add_comm. exact hPA.
  }
  pose proof (raw_lt_to_le M x
    (raw_succ M (rawListSum M xs)) hltXSuccSum) as hleXSuccSum.
  pose proof (raw_le_trans M hPA _ _ _ hleXSuccSum hleSuccSumStep)
    as hleXStep.
  pose proof (raw_le_trans M hPA _ _ _ hleXStep hleStepPred)
    as hleXPred.
  unfold rawBetaModulus.
  exact (raw_lt_succ_of_le M hPA _ _ hleXPred).
Qed.

Lemma raw_lt_numeralValue_of_lt_for_coding : forall (M : RawPAModel),
  RawPASatisfies M -> forall m n, m < n ->
  rawLt M (rawNumeralValue M m) (rawNumeralValue M n).
Proof.
  intros M hPA m n hmn.
  assert (hp : PA.Formula.BProv PA.Formula.Ax_s []
      (PA.Formula.ltTermAt
        (PA.Term.numeral m) (PA.Term.numeral n))).
  {
    unfold PA.Formula.ltTermAt.
    repeat rewrite PA.Term.rename_numeral.
    exact (PA.Formula.BProv_Ax_s_ltConst_closed [] m n hmn).
  }
  set (e := fun _ : nat => raw_zero M).
  pose proof (raw_sat_of_BProv_axs M _ hPA hp e) as hs.
  pose proof (proj1 (raw_sat_ltTermAt_iff M _ _ _) hs) as hlt.
  rewrite !raw_term_eval_numeral in hlt. exact hlt.
Qed.

Definition RawBetaCodesList (M : RawPAModel) (xs : list M)
    (code step : M) : Prop :=
  forall i x, nth_error xs i = Some x ->
    RawBetaEntry M x code step (rawNumeralValue M i).

Fixpoint rawCanonicalBetaCodePrefix (M : RawPAModel)
    (xs : list M) (k : nat) : M :=
  match k with
  | 0 => raw_zero M
  | S j =>
      rawCanonicalBetaExtensionCode M
        (rawCanonicalBetaCodePrefix M xs j)
        (rawFiniteCodingStep M xs)
        (rawNumeralValue M j)
        (nth j xs (raw_zero M))
  end.

Definition rawCanonicalFiniteBetaCode (M : RawPAModel)
    (xs : list M) : M :=
  rawCanonicalBetaCodePrefix M xs (length xs).

Lemma rawCanonicalBetaCodePrefix_spec : forall (M : RawPAModel),
  RawPASatisfies M -> forall (xs : list M) k,
  k <= length xs ->
  forall i x, i < k -> nth_error xs i = Some x ->
  RawBetaEntry M x (rawCanonicalBetaCodePrefix M xs k)
    (rawFiniteCodingStep M xs) (rawNumeralValue M i).
Proof.
  intros M hPA xs k. induction k as [|k IH]; intros hk i x hi hnthI.
  - lia.
  - cbn [rawCanonicalBetaCodePrefix].
    assert (hkLen : k < length xs) by lia.
    pose proof (nth_error_nth' xs (n := k) (raw_zero M) hkLen) as hnthK.
    set (newOut := nth k xs (raw_zero M)) in *.
    assert (hcommon : RawCommonMultipleThrough M
        (rawNumeralValue M k) (rawFiniteCodingStep M xs)).
    { apply rawFiniteCodingStep_common. exact hPA. lia. }
    assert (hBound : rawLt M newOut
        (rawBetaModulus M (rawFiniteCodingStep M xs)
          (rawNumeralValue M k))).
    { exact (rawFiniteCodingStep_entry_bound M hPA xs k newOut hnthK). }
    pose proof (rawCanonicalBetaExtensionCode_spec M hPA
      (rawCanonicalBetaCodePrefix M xs k)
      (rawFiniteCodingStep M xs) (rawNumeralValue M k) newOut
      hcommon hBound) as hext.
    destruct hext as [hpreserve hnew].
    destruct (Nat.eq_dec i k) as [hik | hik].
    + subst i. rewrite hnthI in hnthK. inversion hnthK. subst x.
      exact hnew.
    + assert (hiklt : i < k) by lia.
      apply (hpreserve (rawNumeralValue M i)).
      * exact (raw_lt_numeralValue_of_lt_for_coding M hPA i k hiklt).
      * exact (IH (Nat.le_trans _ _ _ (Nat.le_succ_diag_r k) hk)
          i x hiklt hnthI).
Qed.

Theorem rawCanonicalFiniteBetaCode_spec : forall (M : RawPAModel),
  RawPASatisfies M -> forall xs : list M,
  RawBetaCodesList M xs (rawCanonicalFiniteBetaCode M xs)
    (rawFiniteCodingStep M xs).
Proof.
  intros M hPA xs i x hnth.
  unfold rawCanonicalFiniteBetaCode.
  apply (rawCanonicalBetaCodePrefix_spec M hPA xs (length xs)
    (Nat.le_refl _) i x).
  - apply (proj1 (nth_error_Some xs i)). rewrite hnth. discriminate.
  - exact hnth.
Qed.

(** Program-level realization of the canonical fixed-step construction.
    This is the closure bridge: when the entries are already represented by
    Skolem programs, both the common step and every successive selected code
    are represented by Skolem programs as well. *)
Fixpoint spNumeral (n : nat) : SkolemProgram :=
  match n with
  | 0 => spZero
  | S k => spSucc (spNumeral k)
  end.

Fixpoint spListSum (ps : list SkolemProgram) : SkolemProgram :=
  match ps with
  | [] => spZero
  | p :: tail => spAdd p (spListSum tail)
  end.

Definition spFiniteCodingStep (ps : list SkolemProgram) : SkolemProgram :=
  spMul (spNumeral (fact (length ps))) (spSucc (spListSum ps)).

Fixpoint spCanonicalBetaCodePrefix
    (extensionSelectorIndex : nat) (ps : list SkolemProgram) (k : nat)
    : SkolemProgram :=
  match k with
  | 0 => spZero
  | S j =>
      let oldCode := spCanonicalBetaCodePrefix extensionSelectorIndex ps j in
      spChoose extensionSelectorIndex
        (spaCons oldCode
          (spaCons (spFiniteCodingStep ps)
            (spaCons (spNumeral j)
              (spaCons (nth j ps spZero) spaNil))))
  end.

Definition spCanonicalFiniteBetaCode
    (extensionSelectorIndex : nat) (ps : list SkolemProgram)
    : SkolemProgram :=
  spCanonicalBetaCodePrefix extensionSelectorIndex ps (length ps).

Lemma spNumeral_eval : forall (M : RawPAModel) seed selectorRank selector n,
  skolemProgramEval M seed selectorRank selector (spNumeral n) =
  rawNumeralValue M n.
Proof.
  intros M seed selectorRank selector n.
  induction n; simpl; congruence.
Qed.

Lemma spListSum_eval : forall (M : RawPAModel) seed selectorRank selector ps,
  skolemProgramEval M seed selectorRank selector (spListSum ps) =
  rawListSum M
    (map (skolemProgramEval M seed selectorRank selector) ps).
Proof.
  intros M seed selectorRank selector ps.
  induction ps; simpl; congruence.
Qed.

Lemma spFiniteCodingStep_eval :
  forall (M : RawPAModel) seed selectorRank selector ps,
  skolemProgramEval M seed selectorRank selector
      (spFiniteCodingStep ps) =
  rawFiniteCodingStep M
    (map (skolemProgramEval M seed selectorRank selector) ps).
Proof.
  intros M seed selectorRank selector ps.
  unfold spFiniteCodingStep, rawFiniteCodingStep.
  simpl. rewrite spNumeral_eval, spListSum_eval, length_map.
  reflexivity.
Qed.

Lemma spCanonicalBetaCodePrefix_eval :
  forall (M : RawPAModel) seed selectorRank extensionSelectorIndex ps,
  selectorBody selectorRank extensionSelectorIndex =
    betaCodeExtensionSelectorBody ->
  forall k,
  skolemProgramEval M seed selectorRank (rawCanonicalSelector M)
      (spCanonicalBetaCodePrefix extensionSelectorIndex ps k) =
  rawCanonicalBetaCodePrefix M
    (map (skolemProgramEval M seed selectorRank
      (rawCanonicalSelector M)) ps) k.
Proof.
  intros M seed selectorRank extensionSelectorIndex ps hselector k.
  induction k as [|k IH]; simpl.
  - reflexivity.
  - rewrite hselector, IH, !spNumeral_eval, spListSum_eval.
    rewrite <- (map_nth
      (skolemProgramEval M seed selectorRank (rawCanonicalSelector M))
      ps spZero k).
    unfold rawCanonicalBetaExtensionCode, rawFiniteCodingStep.
    rewrite length_map.
    f_equal.
Qed.

Theorem canonicalFiniteBetaPrograms :
  forall (M : RawPAModel) seed selectorRank,
  formula_rank betaCodeExtensionSelectorBody <= selectorRank ->
  forall ps : list SkolemProgram,
  exists codeProgram stepProgram,
    skolemProgramEval M seed selectorRank (rawCanonicalSelector M)
        codeProgram =
      rawCanonicalFiniteBetaCode M
        (map (skolemProgramEval M seed selectorRank
          (rawCanonicalSelector M)) ps) /\
    skolemProgramEval M seed selectorRank (rawCanonicalSelector M)
        stepProgram =
      rawFiniteCodingStep M
        (map (skolemProgramEval M seed selectorRank
          (rawCanonicalSelector M)) ps).
Proof.
  intros M seed selectorRank hrank ps.
  destruct (selectorBody_complete selectorRank
    betaCodeExtensionSelectorBody hrank) as [extensionIndex hindex].
  exists (spCanonicalFiniteBetaCode extensionIndex ps),
    (spFiniteCodingStep ps). split.
  - unfold spCanonicalFiniteBetaCode, rawCanonicalFiniteBetaCode.
    rewrite spCanonicalBetaCodePrefix_eval by exact hindex.
    now rewrite length_map.
  - apply spFiniteCodingStep_eval.
Qed.

Theorem finite_beta_code_in_canonical_skolem_hull :
  forall (M : RawPAModel) seed selectorRank,
  RawPASatisfies M ->
  formula_rank betaCodeExtensionSelectorBody <= selectorRank ->
  forall ps : list SkolemProgram,
  exists codeProgram stepProgram,
    RawBetaCodesList M
      (map (skolemProgramEval M seed selectorRank
        (rawCanonicalSelector M)) ps)
      (skolemProgramEval M seed selectorRank
        (rawCanonicalSelector M) codeProgram)
      (skolemProgramEval M seed selectorRank
        (rawCanonicalSelector M) stepProgram).
Proof.
  intros M seed selectorRank hPA hrank ps.
  destruct (canonicalFiniteBetaPrograms M seed selectorRank hrank ps)
    as [codeProgram [stepProgram [hcode hstep]]].
  exists codeProgram, stepProgram.
  rewrite hcode, hstep.
  apply rawCanonicalFiniteBetaCode_spec. exact hPA.
Qed.

Lemma finite_list_beta_code_prefix : forall (M : RawPAModel),
  RawPASatisfies M -> forall (xs : list M) k,
  k <= length xs ->
  exists code,
    forall i x, i < k -> nth_error xs i = Some x ->
      RawBetaEntry M x code (rawFiniteCodingStep M xs)
        (rawNumeralValue M i).
Proof.
  intros M hPA xs k. induction k as [|k IH]; intros hk.
  - exists (raw_zero M). intros i x hi. lia.
  - assert (hkLen : k <= length xs) by lia.
    destruct (IH hkLen) as [oldCode hold].
    destruct (nth_error xs k) as [newOut |] eqn:hnth.
    2: {
      apply nth_error_None in hnth. lia.
    }
    assert (hcommon : RawCommonMultipleThrough M
        (rawNumeralValue M k) (rawFiniteCodingStep M xs)).
    { apply rawFiniteCodingStep_common. exact hPA. lia. }
    assert (hBound : rawLt M newOut
        (rawBetaModulus M (rawFiniteCodingStep M xs)
          (rawNumeralValue M k))).
    { exact (rawFiniteCodingStep_entry_bound M hPA xs k newOut hnth). }
    destruct (raw_betaCodeExtension_exists M hPA oldCode
      (rawFiniteCodingStep M xs) (rawNumeralValue M k) newOut
      hcommon hBound) as [newCode [hpreserve hnew]].
    exists newCode. intros i x hi hnthI.
    destruct (Nat.eq_dec i k) as [hik | hik].
    + subst i. rewrite hnthI in hnth. inversion hnth. subst x.
      exact hnew.
    + assert (hiklt : i < k) by lia.
      apply (hpreserve (rawNumeralValue M i)).
      * exact (raw_lt_numeralValue_of_lt_for_coding M hPA i k hiklt).
      * exact (hold i x hiklt hnthI).
Qed.

Theorem finite_list_beta_code : forall (M : RawPAModel),
  RawPASatisfies M -> forall xs : list M,
  exists code step, RawBetaCodesList M xs code step.
Proof.
  intros M hPA xs.
  destruct (finite_list_beta_code_prefix M hPA xs (length xs)
    (Nat.le_refl _)) as [code hcode].
  exists code, (rawFiniteCodingStep M xs).
  intros i x hnth.
  apply hcode; [|exact hnth].
  apply (proj1 (nth_error_Some xs i)).
  rewrite hnth. discriminate.
Qed.

(** Function-valued vectors avoid the proof-irrelevance friction of
    [Vector.t] while retaining the usual finite-index statement. *)
Theorem finite_vector_beta_code : forall (M : RawPAModel),
  RawPASatisfies M -> forall n (v : nat -> M),
  exists code step, forall i, i < n ->
    RawBetaEntry M (v i) code step (rawNumeralValue M i).
Proof.
  intros M hPA n v.
  set (xs := map v (seq 0 n)).
  destruct (finite_list_beta_code M hPA xs)
    as [code [step hcode]].
  exists code, step. intros i hi.
  apply (hcode i (v i)).
  unfold xs. rewrite nth_error_map, nth_error_seq.
  assert (hltb : (i <? n) = true).
  { apply Nat.ltb_lt. exact hi. }
  rewrite hltb. reflexivity.
Qed.

(** A standard bound has exactly its externally standard predecessors. *)
Theorem raw_lt_numeralValue_cases : forall (M : RawPAModel),
  RawPASatisfies M ->
  forall (x : M) n,
    rawLt M x (rawNumeralValue M n) ->
    exists k, k < n /\ x = rawNumeralValue M k.
Proof.
  intros M hPA x n. revert x.
  induction n as [|n IH]; intros x hlt.
  - cbn [rawNumeralValue] in hlt.
    exfalso. exact (raw_not_lt_zero M hPA x hlt).
  - cbn [rawNumeralValue] in hlt.
    destruct (raw_lt_succ_cases M hPA x (rawNumeralValue M n) hlt)
      as [hprev | heq].
    + destruct (IH x hprev) as [k [hk hx]].
      exists k. split; [lia | exact hx].
    + exists n. split; [lia | exact heq].
Qed.

Theorem raw_lt_numeralValue_of_lt : forall (M : RawPAModel),
  RawPASatisfies M ->
  forall m n, m < n ->
    rawLt M (rawNumeralValue M m) (rawNumeralValue M n).
Proof.
  intros M hPA m n hmn.
  assert (hproof : PA.Formula.BProv PA.Formula.Ax_s []
      (PA.Formula.ltTermAt
        (PA.Term.numeral m) (PA.Term.numeral n))).
  {
    unfold PA.Formula.ltTermAt.
    repeat rewrite PA.Term.rename_numeral.
    exact (PA.Formula.BProv_Ax_s_ltConst_closed [] m n hmn).
  }
  set (e := fun _ : nat => raw_zero M).
  pose proof (raw_sat_of_BProv_axs M _ hPA hproof e) as hsat.
  pose proof (proj1 (raw_sat_ltTermAt_iff M
    (PA.Term.numeral m) (PA.Term.numeral n) e) hsat) as hlt.
  rewrite !raw_term_eval_numeral in hlt.
  exact hlt.
Qed.

(** A fixed code and step have at most one output at each index. *)
Theorem rawBetaEntry_functional : forall (M : RawPAModel),
  RawPASatisfies M ->
  forall x y code step idx : M,
    RawBetaEntry M x code step idx ->
    RawBetaEntry M y code step idx ->
    x = y.
Proof.
  intros M hPA x y code step idx hx hy.
  set (f1 := PA.Formula.betaTermTermAt
    (PA.tVar 0) (PA.tVar 2) (PA.tVar 3) (PA.tVar 4)).
  set (f2 := PA.Formula.betaTermTermAt
    (PA.tVar 1) (PA.tVar 2) (PA.tVar 3) (PA.tVar 4)).
  set (G := [f1; f2] : list PA.formula).
  assert (hass1 : PA.Formula.BProv PA.Formula.Ax_s G f1).
  {
    apply PA.Formula.BProv_ass. unfold G. simpl. left. reflexivity.
  }
  assert (hass2 : PA.Formula.BProv PA.Formula.Ax_s G f2).
  {
    apply PA.Formula.BProv_ass. unfold G. simpl. right. left. reflexivity.
  }
  pose proof
    (PA.Formula.BProv_Ax_s_eq_of_betaTermTermAt_betaTermTermAt_same_index
      G (PA.tVar 0) (PA.tVar 1) (PA.tVar 2) (PA.tVar 3)
      (PA.tVar 4) hass1 hass2) as heq.
  set (e := fun _ : nat => raw_zero M).
  set (v := scons M x
    (scons M y (scons M code (scons M step (scons M idx e))))).
  assert (hsat1 : raw_formula_sat M v f1).
  {
    unfold f1.
    apply (proj2 (raw_sat_betaTermTermAt_iff M _ _ _ _ _)).
    unfold v. cbn [raw_term_eval scons]. exact hx.
  }
  assert (hsat2 : raw_formula_sat M v f2).
  {
    unfold f2.
    apply (proj2 (raw_sat_betaTermTermAt_iff M _ _ _ _ _)).
    unfold v. cbn [raw_term_eval scons]. exact hy.
  }
  pose proof (raw_sat_of_BProv_axs_context M G _ hPA heq v)
    as hsound.
  assert (hsatEq : raw_formula_sat M v
      (PA.pEq (PA.tVar 1) (PA.tVar 0))).
  {
    apply hsound. intros g hg.
    unfold G in hg. simpl in hg.
    destruct hg as [hg | [hg | []]]; subst g; assumption.
  }
  unfold v in hsatEq. cbn [raw_formula_sat raw_term_eval scons] in hsatEq.
  symmetry. exact hsatEq.
Qed.

Theorem raw_not_lt_self : forall (M : RawPAModel),
  RawPASatisfies M -> forall x : M, ~ rawLt M x x.
Proof.
  intros M hPA x hlt.
  set (f := PA.Formula.ltTermAt (PA.tVar 0) (PA.tVar 0)).
  set (G := [f] : list PA.formula).
  assert (hass : PA.Formula.BProv PA.Formula.Ax_s G f).
  { apply PA.Formula.BProv_ass. unfold G. simpl. left. reflexivity. }
  pose proof (PA.Formula.BProv_Ax_s_leTermAt_refl G (PA.tVar 0))
    as hrefl.
  pose proof (PA.Formula.BProv_Ax_s_ltTermAt_leTermAt_bot
    G (PA.tVar 0) (PA.tVar 0) hass hrefl) as hbot.
  set (e := fun _ : nat => raw_zero M).
  assert (hsat : raw_formula_sat M (scons M x e) f).
  {
    unfold f. apply (proj2 (raw_sat_ltTermAt_iff M _ _ _)).
    cbn [raw_term_eval scons]. exact hlt.
  }
  apply (raw_sat_of_BProv_axs_context M G PA.pBot hPA hbot
    (scons M x e)).
  intros g hg. unfold G in hg. simpl in hg.
  destruct hg as [hg | []]. subst g. exact hsat.
Qed.

Theorem rawNumeralValue_injective : forall (M : RawPAModel),
  RawPASatisfies M ->
  forall m n, rawNumeralValue M m = rawNumeralValue M n -> m = n.
Proof.
  intros M hPA m n hvalue.
  destruct (Nat.lt_trichotomy m n) as [hlt | [heq | hgt]].
  - pose proof (raw_lt_numeralValue_of_lt M hPA m n hlt) as hraw.
    rewrite hvalue in hraw. exfalso. exact (raw_not_lt_self M hPA _ hraw).
  - exact heq.
  - pose proof (raw_lt_numeralValue_of_lt M hPA n m hgt) as hraw.
    rewrite hvalue in hraw. exfalso. exact (raw_not_lt_self M hPA _ hraw).
Qed.

(** Every element is standard or is above every standard numeral. *)
Theorem raw_standard_or_above : forall (M : RawPAModel),
  RawPASatisfies M -> forall x : M,
  (exists n, x = rawNumeralValue M n) \/
  (forall n, rawLt M (rawNumeralValue M n) x).
Proof.
  intros M hPA x.
  destruct (classic (exists n, x = rawNumeralValue M n))
    as [hstandard | hnonstandard].
  - left. exact hstandard.
  - right. intro n.
    destruct (raw_le_or_gt M hPA x (rawNumeralValue M n))
      as [hxle | hnlt].
    + destruct (raw_le_or_gt M hPA (rawNumeralValue M n) x)
        as [hnle | hxlt].
      * exfalso. apply hnonstandard. exists n.
        exact (raw_le_antisymm M hPA x (rawNumeralValue M n) hxle hnle).
      * destruct (raw_lt_numeralValue_cases M hPA x n hxlt)
          as [k [_ hx]].
        exfalso. apply hnonstandard. exists k. exact hx.
    + exact hnlt.
Qed.

Corollary raw_above_of_nonstandard : forall (M : RawPAModel),
  RawPASatisfies M -> forall x : M,
  ~ (exists n, x = rawNumeralValue M n) ->
  forall n, rawLt M (rawNumeralValue M n) x.
Proof.
  intros M hPA x hnonstandard.
  destruct (raw_standard_or_above M hPA x) as [hs | ha].
  - contradiction.
  - exact ha.
Qed.

End PAFiniteBetaCoding.
