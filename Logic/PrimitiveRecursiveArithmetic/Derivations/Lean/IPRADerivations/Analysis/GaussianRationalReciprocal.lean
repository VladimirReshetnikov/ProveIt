import IPRADerivations.Analysis.GaussianRationalMetric
import IPRADerivations.Analysis.GaussianRationalL1

/-!
# Actual Gaussian-rational reciprocals and Euclidean power bounds

Support for source04's monic residual-radius estimate. The reciprocal is an
actual normalizing program on the original independently denominated point.
Its nonzero norm and inverse bound are derived from an original rational
lower-norm comparison; no inverse identity or desired radius is supplied.
Euclidean product and power bounds preserve their exact rational budgets.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalReciprocal

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (re im code scale normSq normSq_eval oneCode)
open LeanProofs.IPRA.Analysis.GaussianRootAlgebra
  (equal equal_of_values equal_re equal_im re_mul im_mul re_scale im_scale re_one im_one)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
  (represents ofGaussian qmul qmul_represents qmul_canonical canonical canonical_unique
    positive_product represents_congr represents_rescale)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def conjugate (a : PTm n) : PTm n := code (re a) (-(im a))
def normNumerator (q : PTm n) : PTm n := normSq (rawGaussian q)
def inverseNumerator (q : PTm n) : PTm n := scale (rawDen q) (conjugate (rawGaussian q))
/-- A positive total denominator; it is exactly the norm at nonzero points. -/
def inverseDenominator (q : PTm n) : PTm n := succ (pred (normNumerator q))
def reciprocal (q : PTm n) : PTm n := ofGaussian (inverseNumerator q) (inverseDenominator q)
def qone : PTm n := ofGaussian oneCode one

@[simp] theorem subst_conjugate {m : ℕ} (σ : Fin n → PTm m) (a : PTm n) :
    Syn.subst σ (conjugate a) = conjugate (Syn.subst σ a) := by simp [conjugate]
@[simp] theorem subst_normNumerator {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (normNumerator q) = normNumerator (Syn.subst σ q) := by simp [normNumerator]
@[simp] theorem subst_inverseNumerator {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (inverseNumerator q) = inverseNumerator (Syn.subst σ q) := by simp [inverseNumerator]
@[simp] theorem subst_inverseDenominator {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (inverseDenominator q) = inverseDenominator (Syn.subst σ q) := by simp [inverseDenominator]
@[simp] theorem subst_reciprocal {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (reciprocal q) = reciprocal (Syn.subst σ q) := by simp [reciprocal]
@[simp] theorem subst_qone {m : ℕ} (σ : Fin n → PTm m) : Syn.subst σ (qone : PTm n) = (qone : PTm m) := by simp [qone]

@[simp] theorem re_conjugate (a : PTm n) : ZT.toZ Γ (re (conjugate a)) = ZT.toZ Γ (re a) := by
  rw [conjugate,ComplexLogarithmRemainder.eval_re_code]
@[simp] theorem im_conjugate (a : PTm n) : ZT.toZ Γ (im (conjugate a)) = -ZT.toZ Γ (im a) := by
  rw [conjugate,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_neg]

theorem norm_conjugate (a : PTm n) : Γ ⊢[PRAAx] normSq (conjugate a) ≐ normSq a := by
  apply deriveNat
  rw [normSq_eval,normSq_eval,re_conjugate,im_conjugate]
  ring

theorem scaled_conjugate_product (a E : PTm n) : Γ ⊢[PRAAx]
    equal (ComplexLogarithmRemainder.mul a (scale E (conjugate a))) (scale (E*normSq a) oneCode) := by
  apply equal_of_values
  · simp only [re_mul,re_scale,im_scale,re_conjugate,im_conjugate,re_one]
    rw [Q.mk_mul,map_mul,normSq_eval]
    ring
  · simp only [im_mul,re_scale,im_scale,re_conjugate,im_conjugate,im_one]
    ring

theorem reciprocal_canonical (q : PTm n) : Γ ⊢[PRAAx] canonical (reciprocal q) :=
  GaussianRationalHorner.ofGaussian_canonical _ _ (zero_lt_succ _)

theorem reciprocal_represents (q : PTm n) (hN : Γ ⊢[PRAAx] le one (normNumerator q)) : Γ ⊢[PRAAx]
    represents (reciprocal q) (inverseNumerator q) (normNumerator q) :=
  represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _) (RationalIntegerNormalization.positive_form hN).eqSymm
    (GaussianRationalHorner.ofGaussian_represents _ _ (zero_lt_succ _))

theorem qone_represents_scaled (E : PTm n) : Γ ⊢[PRAAx] represents qone (scale E oneCode) E :=
  represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _) (one_mul E)
    (represents_rescale qone oneCode one E (GaussianRationalHorner.ofGaussian_represents _ _ (le_refl _)))

/-- The actual normalized product is literally the canonical code one. -/
theorem reciprocal_identity (q : PTm n) (hN : Γ ⊢[PRAAx] le one (normNumerator q)) : Γ ⊢[PRAAx]
    qmul q (reciprocal q) ≐ qone := by
  have product := qmul_represents q (reciprocal q) (rawGaussian q) (inverseNumerator q) (rawDen q) (normNumerator q)
    (raw_den_positive q) hN (raw_represents q) (reciprocal_represents q hN)
  have value := represents_congr (.eqRefl _) (scaled_conjugate_product (rawGaussian q) (rawDen q)) (.eqRefl _) product
  exact canonical_unique _ _ _ _ (qmul_canonical _ _) (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl _))
    (positive_product _ _ (raw_den_positive q) hN) value (qone_represents_scaled _)

def normLower (q R : PTm n) : Fm PTm n := RationalArgmin.rationalLE
  (GaussianRationalMetric.squaredTolerance R one) (GaussianRationalMetric.qnormSq q)

@[simp] theorem subst_normLower {m : ℕ} (σ : Fin n → PTm m) (q R : PTm n) :
    (normLower q R).subst σ = normLower (Syn.subst σ q) (Syn.subst σ R) := by simp [normLower]

theorem lower_to_cleared (q R : PTm n) (h : Γ ⊢[PRAAx] normLower q R) : Γ ⊢[PRAAx]
    le ((R*R)*(rawDen q*rawDen q)) (normNumerator q) := by
  have left := GaussianRationalMetric.squared_tolerance_represents (Γ := Γ) R one (le_refl _)
  have right := GaussianRationalMetric.qnormSq_represents (Γ := Γ) q (rawGaussian q) (rawDen q) (raw_den_positive q) (raw_represents q)
  have bound := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _ left right h
  change Γ ⊢[PRAAx] le ((rawDen q*rawDen q)*(R*R)) (normNumerator q*(one*one)) at bound
  exact le_congr (mul_comm _ _) (by ipra_ring) bound

/-- The norm is proved positive from the genuine original lower comparison. -/
theorem norm_positive (q R : PTm n) (hR : Γ ⊢[PRAAx] le one R) (h : Γ ⊢[PRAAx] normLower q R) :
    Γ ⊢[PRAAx] le one (normNumerator q) :=
  le_trans (positive_product _ _ (positive_product _ _ hR hR)
    (positive_product _ _ (raw_den_positive q) (raw_den_positive q))) (lower_to_cleared q R h)

/-- |q|≥R≥1 gives |1/q|≤1/R, in the actual rational squared-norm syntax. -/
theorem inverse_bound (q R : PTm n) (hR : Γ ⊢[PRAAx] le one R) (h : Γ ⊢[PRAAx] normLower q R) :
    Γ ⊢[PRAAx] GaussianRationalMetric.bounded (reciprocal q) one R := by
  have positive := norm_positive q R hR h
  apply (GaussianRationalMetric.bounded_iff _ _ _ _ _ positive hR (reciprocal_represents q positive)).iffMpr
  have raw := mul_le_mul_right (normNumerator q) (lower_to_cleared q R h)
  have norm := (ComplexLogarithmRemainder.normSq_scale (Γ := Γ) (rawDen q) (conjugate (rawGaussian q))).eqTrans
    (congrMul (.eqRefl _) (norm_conjugate _))
  have left : Γ ⊢[PRAAx] ((R*R)*(rawDen q*rawDen q))*normNumerator q ≐ (R*R)*normSq (inverseNumerator q) := by
    have n := natEq norm
    apply deriveNat; unfold inverseNumerator normNumerator; ipra_simps; rw [n]; ring
  exact le_congr left (by ipra_ring) raw

theorem bound_congr {q q' A A' B B' : PTm n} (hq : Γ ⊢[PRAAx] q ≐ q')
    (hA : Γ ⊢[PRAAx] A ≐ A') (hB : Γ ⊢[PRAAx] B ≐ B')
    (h : Γ ⊢[PRAAx] GaussianRationalMetric.bounded q A B) : Γ ⊢[PRAAx] GaussianRationalMetric.bounded q' A' B' := by
  have e := Prf.eqSubst (Ax := PRAAx) (Γ := Γ) (GaussianRationalMetric.bounded (var 0) (var 1) (var 2) : Fm PTm 3)
    ![q,A,B] ![q',A',B'] (fun i => by fin_cases i; exact hq; exact hA; exact hB) (by simpa using h)
  simpa using e

/-- Exact Euclidean product bounds with independent radius denominators. -/
theorem bounded_product (q r A B C D : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hq : Γ ⊢[PRAAx] GaussianRationalMetric.bounded q A B)
    (hr : Γ ⊢[PRAAx] GaussianRationalMetric.bounded r C D) : Γ ⊢[PRAAx]
    GaussianRationalMetric.bounded (qmul q r) (A*C) (B*D) := by
  have qBound := (GaussianRationalMetric.bounded_iff q (rawGaussian q) (rawDen q) A B (raw_den_positive q) hB (raw_represents q)).iffMp hq
  have rBound := (GaussianRationalMetric.bounded_iff r (rawGaussian r) (rawDen r) C D (raw_den_positive r) hD (raw_represents r)).iffMp hr
  have product := le_mul_mono qBound rBound
  have rep := qmul_represents (Γ := Γ) q r (rawGaussian q) (rawGaussian r) (rawDen q) (rawDen r)
    (raw_den_positive q) (raw_den_positive r) (raw_represents q) (raw_represents r)
  apply (GaussianRationalMetric.bounded_iff _ _ _ _ _
    (positive_product _ _ (raw_den_positive q) (raw_den_positive r)) (positive_product _ _ hB hD) rep).iffMpr
  have left : Γ ⊢[PRAAx] ((B*B)*normSq (rawGaussian q))*((D*D)*normSq (rawGaussian r)) ≐
      ((B*D)*(B*D))*normSq (ComplexLogarithmRemainder.mul (rawGaussian q) (rawGaussian r)) := by
    have p := natEq (ComplexLogarithmRemainder.normSq_mul (Γ := Γ) (rawGaussian q) (rawGaussian r))
    apply deriveNat; ipra_simps; rw [p]; ring
  exact le_congr left (by ipra_ring) product

theorem cleared_bound (q A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hq : Γ ⊢[PRAAx] GaussianRationalMetric.bounded q A B) : Γ ⊢[PRAAx]
    ComplexLogarithmRemainder.bounded (scale B (rawGaussian q)) (A*rawDen q) :=
  le_congr (ComplexLogarithmRemainder.normSq_scale _ _).eqSymm (by ipra_ring)
    ((GaussianRationalMetric.bounded_iff _ _ _ _ _ (raw_den_positive q) hB (raw_represents q)).iffMp hq)

/-- The exact rational Euclidean triangle estimate. Independent point and
radius denominators are retained, with no L1 factor introduced. -/
theorem bounded_sum (q r A B C D : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hq : Γ ⊢[PRAAx] GaussianRationalMetric.bounded q A B)
    (hr : Γ ⊢[PRAAx] GaussianRationalMetric.bounded r C D) : Γ ⊢[PRAAx]
    GaussianRationalMetric.bounded (GaussianRationalHorner.qadd q r) (A*D+C*B) (B*D) := by
  have eq := raw_den_positive (Γ := Γ) q
  have er := raw_den_positive (Γ := Γ) r
  have qRep := represents_rescale q (rawGaussian q) (rawDen q) (rawDen r) (raw_represents (Γ := Γ) q)
  have rRep := represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _)
    (mul_comm (rawDen r) (rawDen q))
    (represents_rescale r (rawGaussian r) (rawDen r) (rawDen q) (raw_represents (Γ := Γ) r))
  have sumRep := GaussianRationalHorner.qadd_represents q r _ _ _ (positive_product _ _ eq er) qRep rRep
  have first := ComplexLogarithmRemainder.bounded_scale (D*rawDen r) (cleared_bound q A B hB hq)
  have second := ComplexLogarithmRemainder.bounded_scale (B*rawDen q) (cleared_bound r C D hD hr)
  have sum := ComplexLogarithmRemainder.bounded_add first second
  let s := ComplexLogarithmRemainder.add (scale (rawDen r) (rawGaussian q)) (scale (rawDen q) (rawGaussian r))
  have same : Γ ⊢[PRAAx] equal (scale (B*D) s)
      (ComplexLogarithmRemainder.add (scale (D*rawDen r) (scale B (rawGaussian q)))
        (scale (B*rawDen q) (scale D (rawGaussian r)))) := by
    apply equal_of_values <;>
      simp only [s,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,re_scale,im_scale] <;> ipra_simps <;> ring
  have scaled : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (scale (B*D) s)
      ((rawDen q*rawDen r)*(A*D+C*B)) :=
    le_congr (GaussianRootAlgebra.normSq_equal same).eqSymm (by ipra_ring) sum
  apply (GaussianRationalMetric.bounded_iff _ s _ _ _ (positive_product _ _ eq er)
    (positive_product _ _ hB hD) sumRep).iffMpr
  exact le_congr (ComplexLogarithmRemainder.normSq_scale _ _) (by ipra_ring) scaled

theorem bounded_negative (q A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hq : Γ ⊢[PRAAx] GaussianRationalMetric.bounded q A B) : Γ ⊢[PRAAx]
    GaussianRationalMetric.bounded (GaussianRationalMetric.qnegative q) A B := by
  have rep := GaussianRationalMetric.qnegative_represents q (rawGaussian q) (rawDen q) (raw_represents (Γ := Γ) q)
  have bound := (GaussianRationalMetric.bounded_iff q (rawGaussian q) (rawDen q) A B (raw_den_positive q) hB (raw_represents q)).iffMp hq
  exact (GaussianRationalMetric.bounded_iff _ _ _ _ _ (raw_den_positive q) hB rep).iffMpr
    (le_congr (congrMul (.eqRefl _) (ComplexLogarithmRemainder.normSq_neg _)).eqSymm (.eqRefl _) bound)

theorem bounded_difference (q r A B C D : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hq : Γ ⊢[PRAAx] GaussianRationalMetric.bounded q A B)
    (hr : Γ ⊢[PRAAx] GaussianRationalMetric.bounded r C D) : Γ ⊢[PRAAx]
    GaussianRationalMetric.bounded (GaussianRationalMetric.qsub q r) (A*D+C*B) (B*D) :=
  bounded_sum _ _ _ _ _ _ hB hD hq (bounded_negative r C D hD hr)

theorem qone_bounded : Γ ⊢[PRAAx] GaussianRationalMetric.bounded (qone : PTm n) one one := by
  apply (GaussianRationalMetric.bounded_iff qone oneCode one one one (le_refl _) (le_refl _)
    (GaussianRationalHorner.ofGaussian_represents _ _ (le_refl _))).iffMpr
  exact le_congr ((congrMul (one_mul one) ComplexLogarithmRemainder.normSq_one).eqTrans (one_mul one)).eqSymm
    (by ipra_ring) (le_refl one)

def powerStep : PTm 3 := qmul (var 1) (var 2)
def powerF : PR 2 := rec2 qone powerStep
def power (q k : PTm n) : PTm n := ap2 powerF k q

@[simp] theorem subst_power {m : ℕ} (σ : Fin n → PTm m) (q k : PTm n) :
    Syn.subst σ (power q k) = power (Syn.subst σ q) (Syn.subst σ k) := by simp [power]

theorem power_zero (q : PTm n) : Γ ⊢[PRAAx] power q zero ≐ qone := by
  simpa [power,powerF] using rec2_zero (Γ := Γ) qone powerStep q
theorem power_succ (q k : PTm n) : Γ ⊢[PRAAx] power q (succ k) ≐ qmul (power q k) q := by
  simpa [power,powerF,powerStep] using rec2_succ (Γ := Γ) qone powerStep k q

theorem power_canonical (q k : PTm n) : Γ ⊢[PRAAx] canonical (power q k) := by
  refine .orE (zero_or_succ k) ?_ ?_
  · exact GaussianRationalHorner.canonical_congr
      ((congrAp2 powerF Prf.hyp0 (.eqRefl q)).eqTrans (power_zero q))
      (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl _))
  · exact GaussianRationalHorner.canonical_congr
      ((congrAp2 powerF Prf.hyp0 (.eqRefl q)).eqTrans (power_succ q _))
      (qmul_canonical _ _)

/-- Actual runtime powers satisfy the exact Euclidean rational power bound. -/
theorem bounded_power (q A B k : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hq : Γ ⊢[PRAAx] GaussianRationalMetric.bounded q A B) : Γ ⊢[PRAAx]
    GaussianRationalMetric.bounded (power q k) (pw A k) (pw B k) := by
  have bShift : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Syn.shift] using hB.shift
  have qShift : Γ.map Fm.shift ⊢[PRAAx] GaussianRationalMetric.bounded (Syn.shift q) (Syn.shift A) (Syn.shift B) := by
    simpa only [Fm.shift,GaussianRationalMetric.subst_bounded,Syn.shift] using hq.shift
  have all : Γ ⊢[PRAAx] .all (GaussianRationalMetric.bounded (power (Syn.shift q) (var 0))
      (pw (Syn.shift A) (var 0)) (pw (Syn.shift B) (var 0))) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [GaussianRationalMetric.subst_bounded,subst_power,subst_ap2,
        Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact bound_congr (power_zero q).eqSymm (pw_zero A).eqSymm (pw_zero B).eqSymm qone_bounded
    · simp only [GaussianRationalMetric.subst_bounded,subst_power,subst_ap2,
        Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      let I := GaussianRationalMetric.bounded (power (Syn.shift q) (var 0))
        (pw (Syn.shift A) (var 0)) (pw (Syn.shift B) (var 0))
      let Δ := I :: Γ.map Fm.shift
      have positive : Δ ⊢[PRAAx] le one (pw (Syn.shift B) (var 0)) :=
        GaussianPolynomialPerturbation.power_positive _ _ bShift.wk
      have product := bounded_product _ _ _ _ _ _ positive bShift.wk Prf.hyp0 qShift.wk
      exact bound_congr (power_succ _ _).eqSymm (pw_succ _ _).eqSymm (pw_succ _ _).eqSymm product
  simpa only [GaussianRationalMetric.subst_bounded,subst_power,subst_ap2,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE k all

theorem reciprocal_power_bound (q R k : PTm n) (hR : Γ ⊢[PRAAx] le one R)
    (h : Γ ⊢[PRAAx] normLower q R) : Γ ⊢[PRAAx]
    GaussianRationalMetric.bounded (power (reciprocal q) k) one (pw R k) :=
  bound_congr (.eqRefl _) (GaussianPolynomialPerturbation.one_power k) (.eqRefl _)
    (bounded_power _ _ _ _ hR (inverse_bound q R hR h))

theorem reciprocal_correct (q R : PTm n) (hR : Γ ⊢[PRAAx] le one R) (h : Γ ⊢[PRAAx] normLower q R) : Γ ⊢[PRAAx]
    canonical (reciprocal q) ⋏ ((qmul q (reciprocal q) ≐ qone) ⋏ GaussianRationalMetric.bounded (reciprocal q) one R) :=
  .andI (reciprocal_canonical q) (.andI (reciprocal_identity q (norm_positive q R hR h)) (inverse_bound q R hR h))

def reciprocalF : PR 1 := PTm.toPR (reciprocal (var 0))
theorem reciprocal_program (q : PTm n) : Γ ⊢[PRAAx] ap1 reciprocalF q ≐ reciprocal q := by
  simpa [reciprocalF,ap1] using toPR_eq (Γ := Γ) (reciprocal (var 0) : PTm 1) ![q]

theorem rational_inverse_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ normLower (var 0) (var 1) ⟶
      (canonical (reciprocal (var 0)) ⋏
        ((qmul (var 0) (reciprocal (var 0)) ≐ qone) ⋏ GaussianRationalMetric.bounded (reciprocal (var 0)) one (var 1)))) :=
  closeUniv 2 (.impI (.impI (reciprocal_correct _ _ Prf.hyp1 Prf.hyp0)))

theorem rational_product_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 3) ⟶ le one (var 5) ⟶ GaussianRationalMetric.bounded (var 0) (var 2) (var 3) ⟶
      GaussianRationalMetric.bounded (var 1) (var 4) (var 5) ⟶
      GaussianRationalMetric.bounded (qmul (var 0) (var 1)) (var 2*var 4) (var 3*var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (bounded_product _ _ _ _ _ _ hyp2.wk hyp2 Prf.hyp1 Prf.hyp0)))))

theorem rational_triangle_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 3) ⟶ le one (var 5) ⟶ GaussianRationalMetric.bounded (var 0) (var 2) (var 3) ⟶
      GaussianRationalMetric.bounded (var 1) (var 4) (var 5) ⟶
      GaussianRationalMetric.bounded (GaussianRationalHorner.qadd (var 0) (var 1))
        (var 2*var 5+var 4*var 3) (var 3*var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (bounded_sum _ _ _ _ _ _ hyp2.wk hyp2 Prf.hyp1 Prf.hyp0)))))

theorem rational_power_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ GaussianRationalMetric.bounded (var 0) (var 1) (var 2) ⟶
      GaussianRationalMetric.bounded (power (var 0) (var 3)) (pw (var 1) (var 3)) (pw (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (bounded_power _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem reciprocal_power_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ normLower (var 0) (var 1) ⟶
      GaussianRationalMetric.bounded (power (reciprocal (var 0)) (var 2)) one (pw (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (reciprocal_power_bound _ _ _ Prf.hyp1 Prf.hyp0)))

theorem reciprocal_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (ap1 reciprocalF (var 0) ≐ reciprocal (var 0)) := closeUniv 1 (reciprocal_program _)

end LeanProofs.IPRA.Analysis.GaussianRationalReciprocal
