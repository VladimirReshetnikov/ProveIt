import IPRADerivations.Analysis.Logarithm.DyadicComplexLogarithm

/-!
# A canonical local power-series logarithm name

The first two terms are the exact constant `B/C`, with
`B = 2Nz - z²`, `C = 2N²`. They are independent of the Taylor truncation.
The actual dyadic observation symbol rounds this constant at denominator
`2^(p+4)` and adds the already constructed degree-three Taylor-tail observation.

For arbitrary internal ordered precisions `p≤q`, the cleared discrepancy is
bounded by `9·2^(q-p)`: four units come from rounding one fixed rational
constant, and five from the Taylor tail. Thus the dyadic rational values
differ by at most `9·2^(-p-4) < 2^(-p)`.
The underlying finite rational samples are explicitly
`B/C + G_L/D_L = z/N - z²/(2N²) + G_L/D_L`.

This constructs a canonical local complex power-series log name on
`|z|≤R`, `2R≤N`, `N≥1`. Identification with an analytic logarithm,
derivatives and functional laws are not asserted.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.ComplexLogarithmName

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Analysis.LogarithmRemainder (denominator denominator_positive)
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder
  (re im add mul scale normSq bounded series bounded_scale bounded_add bounded_neg
    bounded_mono normSq_eval eval_re_code eval_im_code)
open LeanProofs.IPRA.Analysis.ComplexLogarithmCauchy (eval_re_congr eval_im_congr power_positive)
open LeanProofs.IPRA.Analysis.DyadicComplexLogarithm
  (rounded roundingError rounding_bound roundedDifference cancel_bounded_scale
    precision unit unit_add congr_add congr_scale congr_neg congr_rounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## One fixed rational constant has only two rounding errors -/

def constantErrors (c D A B : PTm n) : PTm n :=
  add (roundingError c D (A * B))
    (ComplexLogarithmRemainder.neg (scale B (roundingError c D A)))

theorem constant_comparison_identity (c D A B : PTm n) :
    Γ ⊢[PRAAx] normSq (scale D (roundedDifference c c D D A B)) ≐
      normSq (constantErrors c D A B) := by
  apply deriveNat
  rw [normSq_eval, normSq_eval]
  simp only [constantErrors, roundedDifference, roundingError, add, scale,
    ComplexLogarithmRemainder.neg, eval_re_code, eval_im_code,
    ZT.toZ_add, ZT.toZ_neg, ZT.toZ_mul, ZT.toZ_ofNat, Q.mk_mul, map_mul]
  ring

theorem constant_comparison (c D A B : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] bounded (roundedDifference c c D D A B) (two + two * B) := by
  have first := rounding_bound c D (A * B) hD
  have second := bounded_neg (bounded_scale B (rounding_bound c D A hD))
  have total : Γ ⊢[PRAAx] bounded (scale D (roundedDifference c c D D A B))
      (D * (two + two * B)) :=
    le_congr (constant_comparison_identity _ _ _ _).eqSymm (by ipra_ring)
      (bounded_add first second)
  exact cancel_bounded_scale hD total

theorem constant_dyadic_comparison (c D A k : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] bounded (roundedDifference c c D D A (pw two k)) (num 4 * pw two k) := by
  have h12 : Γ ⊢[PRAAx] le one two := le_of_eq_add (d := one) (by ipra_ring)
  refine bounded_mono (constant_comparison c D A (pw two k) hD) ?_
  refine le_of_eq_add (d := two * monus (pw two k) one) ?_
  ipra_lc 2 * natEq (eq_add_of_le (power_positive two k h12))

/-! ## The exact first two Taylor terms and finite rational samples -/

def baseNumerator (z N : PTm n) : PTm n :=
  add (scale (two * N) z) (ComplexLogarithmRemainder.neg (mul z z))

def baseDenominator (N : PTm n) : PTm n := two * N * N

def finiteNumerator (z N L : PTm n) : PTm n :=
  add (scale (denominator N L) (baseNumerator z N))
    (scale (baseDenominator N) (series z N L))

def finiteDenominator (N L : PTm n) : PTm n := baseDenominator N * denominator N L

theorem base_positive (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] le one (baseDenominator N) := by
  have square : Γ ⊢[PRAAx] le one (N * N) :=
    le_congr (one_mul one) (.eqRefl _) (le_mul_mono hN hN)
  exact le_trans square (le_of_eq_add (d := N * N) (by unfold baseDenominator; ipra_ring))

theorem finite_positive (N L : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] le one (finiteDenominator N L) :=
  le_congr (one_mul one) (.eqRefl _) (le_mul_mono (base_positive N hN) (denominator_positive N L hN))

theorem base_re (z N : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (re (baseNumerator z N))
      (ZT.ofNat (two * N) * re z - (ZT.sq (re z) - ZT.sq (im z))) := by
  ipra_lc [baseNumerator, add, scale, mul, ComplexLogarithmRemainder.neg, eval_re_code]

theorem base_im (z N : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (im (baseNumerator z N))
      (ZT.ofNat (two * N) * im z - ZT.ofNat two * re z * im z) := by
  ipra_lc [baseNumerator, add, scale, mul, ComplexLogarithmRemainder.neg, eval_im_code]

/-- Exact rational addition `H/(CD) = B/C + G/D`, cleared in each Gaussian coordinate. -/
theorem finite_rational_connection_re (z N L : PTm n) :
    Γ ⊢[PRAAx] ZT.eq
      (ZT.ofNat (baseDenominator N * denominator N L) * re (finiteNumerator z N L))
      (ZT.ofNat (finiteDenominator N L * denominator N L) * re (baseNumerator z N) +
        ZT.ofNat (finiteDenominator N L * baseDenominator N) * re (series z N L)) := by
  ipra_lc [finiteNumerator, finiteDenominator, add, scale, eval_re_code]

theorem finite_rational_connection_im (z N L : PTm n) :
    Γ ⊢[PRAAx] ZT.eq
      (ZT.ofNat (baseDenominator N * denominator N L) * im (finiteNumerator z N L))
      (ZT.ofNat (finiteDenominator N L * denominator N L) * im (baseNumerator z N) +
        ZT.ofNat (finiteDenominator N L * baseDenominator N) * im (series z N L)) := by
  ipra_lc [finiteNumerator, finiteDenominator, add, scale, eval_im_code]

/-! ## The full local power-series observation symbol -/

def observationTerm (p z R N : PTm n) : PTm n :=
  add (rounded (baseNumerator z N) (baseDenominator N) (unit p))
    (DyadicComplexLogarithm.observation p z R N)

def observationF : PR 4 := PTm.toPR (observationTerm (var 0) (var 1) (var 2) (var 3))

def observation (p z R N : PTm n) : PTm n :=
  ComplexLogarithmCauchy.ap4 observationF p z R N

ipra_subst baseNumerator
ipra_subst baseDenominator
ipra_subst observationTerm
ipra_subst observation

theorem observation_compute (p z R N : PTm n) :
    Γ ⊢[PRAAx] observation p z R N ≐ observationTerm p z R N := by
  have h := toPR_eq (Γ := Γ) (observationTerm (var 0) (var 1) (var 2) (var 3)) ![p, z, R, N]
  simpa [observation, observationF, ComplexLogarithmCauchy.ap4] using h

theorem observation_later (p k z R N : PTm n) :
    Γ ⊢[PRAAx] observation (p + k) z R N ≐
      add (rounded (baseNumerator z N) (baseDenominator N) (unit p * pw two k))
        (DyadicComplexLogarithm.observation (p + k) z R N) :=
  (observation_compute _ _ _ _).eqTrans
    (congr_add (congr_rounded (.eqRefl _) (.eqRefl _) (unit_add p k)) (.eqRefl _))

def discrepancy (p k z R N : PTm n) : PTm n :=
  add (observation (p + k) z R N)
    (ComplexLogarithmRemainder.neg (scale (pw two k) (observation p z R N)))

theorem discrepancy_identity (p k z R N : PTm n) :
    Γ ⊢[PRAAx] normSq (discrepancy p k z R N) ≐
      normSq (add
        (roundedDifference (baseNumerator z N) (baseNumerator z N)
          (baseDenominator N) (baseDenominator N) (unit p) (pw two k))
        (DyadicComplexLogarithm.discrepancy p k z R N)) := by
  have pr := eval_re_congr (observation_compute (Γ := Γ) p z R N)
  have pi := eval_im_congr (observation_compute (Γ := Γ) p z R N)
  have qr := eval_re_congr (observation_later (Γ := Γ) p k z R N)
  have qi := eval_im_congr (observation_later (Γ := Γ) p k z R N)
  simp only [observationTerm, add, eval_re_code, eval_im_code, ZT.toZ_add] at pr pi qr qi
  apply deriveNat
  rw [normSq_eval, normSq_eval]
  simp only [discrepancy, roundedDifference, DyadicComplexLogarithm.discrepancy,
    add, scale, ComplexLogarithmRemainder.neg, eval_re_code, eval_im_code,
    ZT.toZ_add, ZT.toZ_neg, ZT.toZ_mul, ZT.toZ_ofNat]
  rw [pr, pi, qr, qi]
  ring

theorem regular_bound (p k z R N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hz : Γ ⊢[PRAAx] bounded z R) (hR : Γ ⊢[PRAAx] le (two * R) N) :
    Γ ⊢[PRAAx] bounded (discrepancy p k z R N) (num 9 * pw two k) := by
  have constant := constant_dyadic_comparison (baseNumerator z N) (baseDenominator N) (unit p) k
    (base_positive N hN)
  have tail := DyadicComplexLogarithm.regular_dyadic_bound p k z R N hN hz hR
  exact le_congr (discrepancy_identity _ _ _ _ _).eqSymm (by ipra_ring) (bounded_add constant tail)

#print axioms regular_bound

/-! ## Arbitrary ordered precisions -/

theorem congr_observation {p q : PTm n} (z R N : PTm n) (h : Γ ⊢[PRAAx] p ≐ q) :
    Γ ⊢[PRAAx] observation p z R N ≐ observation q z R N := by
  apply congrApp observationF
  intro i
  fin_cases i
  · exact h
  · exact .eqRefl _
  · exact .eqRefl _
  · exact .eqRefl _

def endpointDifference (p q z R N : PTm n) : PTm n :=
  add (observation q z R N)
    (ComplexLogarithmRemainder.neg (scale (pw two (monus q p)) (observation p z R N)))

theorem regular_endpoints (p q z R N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hz : Γ ⊢[PRAAx] bounded z R) (hR : Γ ⊢[PRAAx] le (two * R) N)
    (order : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] bounded (endpointDifference p q z R N) (num 9 * pw two (monus q p)) := by
  have e : Γ ⊢[PRAAx] endpointDifference p q z R N ≐ discrepancy p (monus q p) z R N :=
    congr_add (congr_observation z R N (eq_add_of_le order)) (.eqRefl _)
  exact le_congr (ComplexLogarithmRemainder.congr_normSq e).eqSymm (.eqRefl _)
    (regular_bound p (monus q p) z R N hN hz hR)

/-! ## Closed object-theory endpoints -/

/-- Variables `0=c`, `1=D`, `2=A`, `3=k`. -/
def constantFormula : Fm PTm 4 :=
  le one (var 1) ⟶
    bounded (roundedDifference (var 0) (var 0) (var 1) (var 1) (var 2) (pw two (var 3)))
      (num 4 * pw two (var 3))

theorem fixed_rational_dyadic_rounding :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 constantFormula :=
  closeUniv 4 (.impI (constant_dyadic_comparison _ _ _ _ Prf.hyp0))

def firstTermsFormula (z N : PTm n) : Fm PTm n :=
  ZT.eq (re (baseNumerator z N))
    (ZT.ofNat (two * N) * re z - (ZT.sq (re z) - ZT.sq (im z))) ⋏
  ZT.eq (im (baseNumerator z N))
    (ZT.ofNat (two * N) * im z - ZT.ofNat two * re z * im z)

/-- Variables `0=z`, `1=N`: the Gaussian numerator is exactly `2Nz−z²`. -/
theorem first_two_logarithm_terms :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (firstTermsFormula (var 0) (var 1)) :=
  closeUniv 2 (.andI (base_re _ _) (base_im _ _))

def finiteConnectionFormula (z N L : PTm n) : Fm PTm n :=
  ZT.eq
    (ZT.ofNat (baseDenominator N * denominator N L) * re (finiteNumerator z N L))
    (ZT.ofNat (finiteDenominator N L * denominator N L) * re (baseNumerator z N) +
      ZT.ofNat (finiteDenominator N L * baseDenominator N) * re (series z N L)) ⋏
  ZT.eq
    (ZT.ofNat (baseDenominator N * denominator N L) * im (finiteNumerator z N L))
    (ZT.ofNat (finiteDenominator N L * denominator N L) * im (baseNumerator z N) +
      ZT.ofNat (finiteDenominator N L * baseDenominator N) * im (series z N L))

/-- Variables `0=L`, `1=z`, `2=N`. -/
def finiteSampleFormula : Fm PTm 3 :=
  le one (var 2) ⟶
    (le one (baseDenominator (var 2)) ⋏
      (le one (finiteDenominator (var 2) (var 0)) ⋏
        finiteConnectionFormula (var 1) (var 2) (var 0)))

theorem finite_logarithm_sample :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 finiteSampleFormula :=
  closeUniv 3 (.impI (.andI (base_positive _ Prf.hyp0)
    (.andI (finite_positive _ _ Prf.hyp0)
      (.andI (finite_rational_connection_re _ _ _) (finite_rational_connection_im _ _ _)))))

/-- Variables `0=p`, `1=z`, `2=R`, `3=N`. -/
def observationFormula : Fm PTm 4 :=
  observation (var 0) (var 1) (var 2) (var 3) ≐
    add (rounded (baseNumerator (var 1) (var 3)) (baseDenominator (var 3)) (unit (var 0)))
      (DyadicComplexLogarithm.observation (var 0) (var 1) (var 2) (var 3))

theorem local_power_series_observation_definition :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 observationFormula :=
  closeUniv 4 (observation_compute _ _ _ _)

/-- Variables `0=p`, `1=k`, `2=z`, `3=R`, `4=N`. -/
def nameFormula : Fm PTm 5 :=
  le one (var 4) ⟶ bounded (var 2) (var 3) ⟶ le (two * var 3) (var 4) ⟶
    (le one (baseDenominator (var 4)) ⋏
      (le one (finiteDenominator (var 4) (precision (var 0))) ⋏
        bounded (discrepancy (var 0) (var 1) (var 2) (var 3) (var 4)) (num 9 * pw two (var 1))))

theorem canonical_local_power_series_log_name :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5 nameFormula := by
  refine closeUniv 5 (.impI (.impI (.impI ?_)))
  exact .andI (base_positive _ hyp2) (.andI (finite_positive _ _ hyp2)
    (regular_bound _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))

/-- Variables `0=p`, `1=q`, `2=z`, `3=R`, `4=N`. -/
def endpointsFormula : Fm PTm 5 :=
  le one (var 4) ⟶ bounded (var 2) (var 3) ⟶ le (two * var 3) (var 4) ⟶ le (var 0) (var 1) ⟶
    (le one (baseDenominator (var 4)) ⋏
      (le one (finiteDenominator (var 4) (precision (var 0))) ⋏
        (le one (finiteDenominator (var 4) (precision (var 1))) ⋏
          bounded (endpointDifference (var 0) (var 1) (var 2) (var 3) (var 4))
            (num 9 * pw two (monus (var 1) (var 0))))))

theorem canonical_local_power_series_log_endpoints :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5 endpointsFormula := by
  refine closeUniv 5 (.impI (.impI (.impI (.impI ?_))))
  exact .andI (base_positive _ hyp2.wk) (.andI (finite_positive _ _ hyp2.wk)
    (.andI (finite_positive _ _ hyp2.wk) (regular_endpoints _ _ _ _ _ hyp2.wk hyp2 Prf.hyp1 Prf.hyp0)))

/-! ## Direct observation-to-finite-sample correctness -/

def observationError (p z R N : PTm n) : PTm n :=
  add (scale (finiteDenominator N (precision p)) (observation p z R N))
    (ComplexLogarithmRemainder.neg (scale (unit p) (finiteNumerator z N (precision p))))

def sampleErrors (p z R N : PTm n) : PTm n :=
  add (scale (denominator N (precision p))
      (roundingError (baseNumerator z N) (baseDenominator N) (unit p)))
    (scale (baseDenominator N) (DyadicComplexLogarithm.observationError p z R N))

theorem observation_error_identity (p z R N : PTm n) :
    Γ ⊢[PRAAx] normSq (observationError p z R N) ≐ normSq (sampleErrors p z R N) := by
  have pr := eval_re_congr (observation_compute (Γ := Γ) p z R N)
  have pi := eval_im_congr (observation_compute (Γ := Γ) p z R N)
  simp only [observationTerm, add, eval_re_code, eval_im_code, ZT.toZ_add] at pr pi
  apply deriveNat
  rw [normSq_eval, normSq_eval]
  simp only [observationError, sampleErrors, finiteNumerator, finiteDenominator,
    DyadicComplexLogarithm.observationError, roundingError, add, scale,
    ComplexLogarithmRemainder.neg, eval_re_code, eval_im_code,
    ZT.toZ_add, ZT.toZ_neg, ZT.toZ_mul, ZT.toZ_ofNat, Q.mk_mul, map_mul]
  rw [pr, pi]
  ring

theorem observation_error_bound (p z R N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] bounded (observationError p z R N) (num 4 * finiteDenominator N (precision p)) := by
  have first := bounded_scale (denominator N (precision p))
    (rounding_bound (baseNumerator z N) (baseDenominator N) (unit p) (base_positive N hN))
  have second := bounded_scale (baseDenominator N)
    (DyadicComplexLogarithm.observation_rounding p z R N hN)
  exact le_congr (observation_error_identity _ _ _ _).eqSymm
    (by unfold finiteDenominator; ipra_ring) (bounded_add first second)

/-- Variables `0=p`, `1=z`, `2=R`, `3=N`. -/
def observationErrorFormula : Fm PTm 4 :=
  le one (var 3) ⟶
    (le one (finiteDenominator (var 3) (precision (var 0))) ⋏
      bounded (observationError (var 0) (var 1) (var 2) (var 3))
        (num 4 * finiteDenominator (var 3) (precision (var 0))))

theorem local_power_series_observation_error :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 observationErrorFormula :=
  closeUniv 4 (.impI (.andI (finite_positive _ _ Prf.hyp0)
    (observation_error_bound _ _ _ _ Prf.hyp0)))

#print axioms fixed_rational_dyadic_rounding
#print axioms first_two_logarithm_terms
#print axioms finite_logarithm_sample
#print axioms local_power_series_observation_definition
#print axioms canonical_local_power_series_log_name
#print axioms canonical_local_power_series_log_endpoints
#print axioms local_power_series_observation_error

end LeanProofs.IPRA.Analysis.ComplexLogarithmName
