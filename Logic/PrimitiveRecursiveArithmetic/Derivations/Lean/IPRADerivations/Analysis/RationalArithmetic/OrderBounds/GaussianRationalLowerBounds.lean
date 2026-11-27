import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameReciprocal

/-!
# Exact rational lower bounds for actual Gaussian rational values

`lower q A B` means |q|≥A/B through the existing squared rational
comparison. Independent original denominators remain in the cleared
form. Actual multiplication preserves the full two rational constants.
For A,B≥1 the original conjugate/norm reciprocal has bound B/A.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalLowerBounds

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianRationalHorner (represents positive_product canonical qmul)
open GaussianRationalReciprocal (reciprocal qone reciprocal_identity bound_congr bounded_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open GaussianRationalMetric (qnormSq squaredTolerance bounded)
open ComplexLogarithmRemainder (normSq)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def lower (q A B : PTm n) : Fm PTm n := RationalArgmin.rationalLE (squaredTolerance A B) (qnormSq q)
ipra_subst lower

theorem lower_congr {q q' A A' B B' : PTm n} (hq : Γ ⊢[PRAAx] q ≐ q')
    (hA : Γ ⊢[PRAAx] A ≐ A') (hB : Γ ⊢[PRAAx] B ≐ B') (h : Γ ⊢[PRAAx] lower q A B) :
    Γ ⊢[PRAAx] lower q' A' B' := by
  have p := Prf.eqSubst (Ax := PRAAx) (Γ := Γ) (lower (var 0) (var 1) (var 2) : Fm PTm 3)
    ![q,A,B] ![q',A',B'] (fun i => by fin_cases i; exact hq; exact hA; exact hB) (by simpa using h)
  simpa using p

theorem lower_from_representation (q a E A B : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hB : Γ ⊢[PRAAx] le one B) (hq : Γ ⊢[PRAAx] represents q a E)
    (h : Γ ⊢[PRAAx] le (A*A*(E*E)) (B*B*normSq a)) : Γ ⊢[PRAAx] lower q A B :=
  GaussianRationalMetric.comparison_of_cleared _ _ _ _ (B*B) (E*E)
    (positive_product _ _ hB hB) (positive_product _ _ hE hE)
    (GaussianRationalMetric.squared_tolerance_represents A B hB)
    (GaussianRationalMetric.qnormSq_represents q a E hE hq)
    (le_congr (by ipra_ring) (by ipra_ring) h)

theorem lower_to_cleared (q a E A B : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hB : Γ ⊢[PRAAx] le one B) (hq : Γ ⊢[PRAAx] represents q a E)
    (h : Γ ⊢[PRAAx] lower q A B) : Γ ⊢[PRAAx] le (A*A*(E*E)) (B*B*normSq a) :=
  le_congr (by ipra_ring) (by ipra_ring)
    (GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
      (GaussianRationalMetric.squared_tolerance_represents A B hB)
      (GaussianRationalMetric.qnormSq_represents q a E hE hq) h)

theorem product_lower (q r A B C D : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hD : Γ ⊢[PRAAx] le one D) (hq : Γ ⊢[PRAAx] lower q A B) (hr : Γ ⊢[PRAAx] lower r C D) :
    Γ ⊢[PRAAx] lower (GaussianRationalHorner.qmul q r) (A*C) (B*D) := by
  have a := lower_to_cleared q (rawGaussian q) (rawDen q) A B (raw_den_positive q) hB (raw_represents q) hq
  have b := lower_to_cleared r (rawGaussian r) (rawDen r) C D (raw_den_positive r) hD (raw_represents r) hr
  apply lower_from_representation _ _ _ _ _ (positive_product _ _ (raw_den_positive q) (raw_den_positive r))
    (positive_product _ _ hB hD)
    (GaussianRationalHorner.qmul_represents _ _ _ _ _ _ (raw_den_positive q) (raw_den_positive r) (raw_represents q) (raw_represents r))
  have e := natEq (ComplexLogarithmRemainder.normSq_mul (Γ := Γ) (rawGaussian q) (rawGaussian r))
  exact le_congr (by ipra_ring) (by apply deriveNat; ipra_simps; rw [e]; ring) (le_mul_mono a b)

/-- The fractional named-apartness interface, with no confusion with the natural-radius normLower. -/
theorem name_lower (q A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] lower q A B) : Γ ⊢[PRAAx] GaussianNameReciprocal.lower q B := by
  have first : Γ ⊢[PRAAx] RationalArgmin.rationalLE (squaredTolerance one B) (squaredTolerance A B) := by
    apply GaussianRationalMetric.comparison_of_cleared _ _ _ _ (B*B) (B*B)
      (positive_product _ _ hB hB) (positive_product _ _ hB hB)
      (GaussianRationalMetric.squared_tolerance_represents one B hB)
      (GaussianRationalMetric.squared_tolerance_represents A B hB)
    exact le_congr (.eqRefl _) (by ipra_ring) (le_mul_mono (le_refl (B*B)) (le_mul_mono hA hA))
  exact RationalArgmin.transitive first h

/-- A positive lower bound forces the norm numerator to be positive. -/
theorem norm_positive (q A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] lower q A B) : Γ ⊢[PRAAx] le one (GaussianRationalReciprocal.normNumerator q) :=
  GaussianNameReciprocal.lower_norm_positive q B hB (name_lower q A B hA hB h)

/-- An actual rational value with a positive lower bound cancels its reciprocal. -/
theorem reciprocal_identity_of_lower (q A B : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] lower q A B) : Γ ⊢[PRAAx] qmul q (reciprocal q) ≐ qone :=
  reciprocal_identity q (norm_positive q A B hA hB h)

/-- Full reciprocal constant B/A for the actual normalized conjugate/norm algorithm. -/
theorem inverse_bound (q A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] lower q A B) : Γ ⊢[PRAAx] bounded (GaussianRationalReciprocal.reciprocal q) B A := by
  have hn := norm_positive q A B hA hB h
  have clear := lower_to_cleared q (rawGaussian q) (rawDen q) A B (raw_den_positive q) hB (raw_represents q) h
  have main := le_mul_mono clear (le_refl (GaussianRationalReciprocal.normNumerator q))
  apply (GaussianRationalMetric.bounded_iff _ _ _ _ _ hn hA (GaussianRationalReciprocal.reciprocal_represents q hn)).iffMpr
  have norm := (ComplexLogarithmRemainder.normSq_scale (Γ := Γ) (rawDen q) (GaussianRationalReciprocal.conjugate (rawGaussian q))).eqTrans
    (congrMul (.eqRefl _) (GaussianRationalReciprocal.norm_conjugate _))
  exact le_congr (by
    have e := natEq norm
    apply deriveNat
    unfold GaussianRationalReciprocal.inverseNumerator GaussianRationalReciprocal.normNumerator at *
    ipra_simps
    rw [e]
    ring) (by unfold GaussianRationalReciprocal.normNumerator; ipra_ring) main

/-- Cancel a factor whose norm is at least `1/B`, multiplying the error by `B`. -/
theorem cancel_bounded_product (d q E K B : PTm n) (hd : Γ ⊢[PRAAx] canonical d)
    (hK : Γ ⊢[PRAAx] le one K) (hB : Γ ⊢[PRAAx] le one B) (hq : Γ ⊢[PRAAx] lower q one B)
    (h : Γ ⊢[PRAAx] bounded (qmul d q) E K) : Γ ⊢[PRAAx] bounded d (E*B) K := by
  have inv := inverse_bound q one B (le_refl one) hB hq
  have unit := reciprocal_identity_of_lower q one B (le_refl one) hB hq
  have cancel : Γ ⊢[PRAAx] qmul (qmul d q) (reciprocal q) ≐ d :=
    (qmul_associative _ _ _).eqTrans ((qmul_congr (.eqRefl d) unit).eqTrans (qmul_one_right d hd))
  exact bound_congr cancel (.eqRefl _) (by ipra_ring) (bounded_product _ _ _ _ _ _ hK (le_refl one) h inv)

theorem original_rational_gaussian_lower_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 3) ⟶ le one (var 5) ⟶ lower (var 0) (var 2) (var 3) ⟶ lower (var 1) (var 4) (var 5) ⟶
      lower (GaussianRationalHorner.qmul (var 0) (var 1)) (var 2*var 4) (var 3*var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (product_lower _ _ _ _ _ _ hyp2.wk hyp2 Prf.hyp1 Prf.hyp0)))))
theorem actual_rational_gaussian_inverse_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ le one (var 2) ⟶ lower (var 0) (var 1) (var 2) ⟶
      bounded (GaussianRationalReciprocal.reciprocal (var 0)) (var 2) (var 1)) :=
  closeUniv 3 (.impI (.impI (.impI (inverse_bound _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianRationalLowerBounds
