import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaEulerFullHeadInverse
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGaussEulerPowerRatio
import IPRADerivations.Analysis.Names.GaussianNamedBoundedProductObservation

/-!
# Positive Euler exponents in the Gauss multiplication identity

A positive coefficient times the actual logarithm names the same
exponent as the negative of the reciprocal Euler exponent. This
identification and the coefficient addition law preserve the literal
exponential programs.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGaussEulerPositiveExponents

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaEulerFullHeadInverse (negExpF negExpData exponent_input)
open GaussianGammaEulerShift (constant_sum_cross)
open GaussianGammaFiniteApproximantName
  (logF log_regular logExponentF logExponentData log_exponent_regular exponential_input)
open GaussianGaussEulerPowerRatio
  (fixedExponentF fixedExponentData fixed_exponent_regular fixedPowerF fixedPowerData)
open GaussianGammaWeierstrassApproximant (constant_data_cross)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws
  (negativeF negativeData negative_fast zeroF zero_fast zero_at add_associative add_commutative add_negative add_zero add_zero_left)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianRationalHorner (qadd qzero ofGaussian)
open GaussianRationalMetric (qnegative qnegative_canonical)
open GaussianRationalSyntheticDivision (qmul_congr qadd_congr qzero_add qmul_zero_left)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem fixed_power_regular (c N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] pointCN fixedPowerF (fixedPowerData c N) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (exponential_input _ _ (fixed_exponent_regular c N hN))

theorem fixed_exponent_coeff_congr (c d N : PTm n) (hN : Γ ⊢[PRAAx] le one N) (eq : Γ ⊢[PRAAx] c ≐ d) :
    Γ ⊢[PRAAx] crossEquivalent fixedExponentF fixedExponentF (fixedExponentData c N) (fixedExponentData d N) :=
  multiply_cross constantF constantF logF logF c d N N (constant_regular c) (constant_regular d)
    (log_regular N hN) (log_regular N hN) (constant_data_cross c d eq) (cross_refl _ _ (log_regular N hN))

theorem fixed_power_coeff_congr (c d N : PTm n) (hN : Γ ⊢[PRAAx] le one N) (eq : Γ ⊢[PRAAx] c ≐ d) :
    Γ ⊢[PRAAx] crossEquivalent fixedPowerF fixedPowerF (fixedPowerData c N) (fixedPowerData d N) :=
  GaussianExponentialRadiusIndependence.independent_radii_proper fixedExponentF fixedExponentF _ _ _ _
    (exponential_input _ _ (fixed_exponent_regular c N hN)) (exponential_input _ _ (fixed_exponent_regular d N hN))
    (fixed_exponent_coeff_congr c d N hN eq)

theorem fixed_exponent_sum (c d N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent (addF fixedExponentF fixedExponentF) fixedExponentF
      (addData (fixedExponentData c N) (fixedExponentData d N)) (fixedExponentData (qadd c d) N) := by
  have hc := constant_regular (Γ := Γ) c
  have hd := constant_regular (Γ := Γ) d
  have hl := log_regular (Γ := Γ) N hN
  have split := GaussianNameRingLaws.right_distributive constantF constantF logF c d N hc hd hl
  have sum := multiply_cross (addF constantF constantF) constantF logF logF (addData c d) (qadd c d) N N
    (add_fast _ _ _ _ hc hd) (constant_regular _) hl hl (constant_sum_cross c d) (cross_refl _ _ hl)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ split) sum

theorem fixed_power_sum (c d N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF fixedPowerF fixedPowerF) fixedPowerF
      (multiplyData fixedPowerF fixedPowerF (fixedPowerData c N) (fixedPowerData d N)) (fixedPowerData (qadd c d) N) :=
  GaussianGammaFoldedApproximantBalance.exponential_product_equivalent fixedExponentF fixedExponentF fixedExponentF
    _ _ _ _ _ _ (exponential_input _ _ (fixed_exponent_regular c N hN))
    (exponential_input _ _ (fixed_exponent_regular d N hN)) (exponential_input _ _ (fixed_exponent_regular (qadd c d) N hN))
    (fixed_exponent_sum c d N hN)

private theorem zero_exponent (N a : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent fixedExponentF zeroF (fixedExponentData qzero N) a := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (fixed_exponent_regular qzero N hN) (zero_fast a)
  refine .allI ?_
  let p : PTm (n+1) := var 0
  let x := Syn.shift N
  let y := Syn.shift a
  let k := GaussianNamedBoundedProductObservation.clock constantF logF p qzero x
  have e := GaussianNamedBoundedProductObservation.name_at (Γ := Γ.map Fm.shift) constantF logF p qzero x
  have eq := e.eqTrans ((qmul_congr (constant_at k qzero) (.eqRefl _)).eqTrans
    ((qmul_zero_left (ap2 logF k x)).eqTrans (zero_at p y).eqSymm))
  simpa [GaussianNameConjugation.pointwiseEqual,fixedExponentF,fixedExponentData,Syn.shift,p,x,y] using eq

private theorem zeros_cross (x y : PTm n) : Γ ⊢[PRAAx] crossEquivalent zeroF zeroF x y := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (zero_fast x) (zero_fast y)
  exact .allI ((zero_at (var 0) (Syn.shift x)).eqTrans (zero_at (var 0) (Syn.shift y)).eqSymm)

private theorem negate_sum (c : PTm n) : Γ ⊢[PRAAx] qadd (qnegative c) c ≐ qzero :=
  (GaussianReciprocalHorner.qadd_commutative _ _).eqTrans
    ((qadd_congr (.eqRefl _) (qzero_add _ (qnegative_canonical c)).eqSymm).eqTrans
      (GaussianNameRingLaws.additive_inverse_value c))

private theorem named_additive_inverse (f g : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hs : Γ ⊢[PRAAx] crossEquivalent (addF f g) zeroF (addData x y) (negativeData x)) :
    Γ ⊢[PRAAx] crossEquivalent (negativeF f) g (negativeData x) y := by
  let F := negativeF f
  let u := negativeData x
  let Q := addF F f
  let v := addData u x
  have hx := negative_fast f x hf
  have assoc := add_associative F f g u x y hx hf hg
  have right := add_cross F F (addF f g) zeroF u u (addData x y) u hx hx (add_fast _ _ _ _ hf hg)
    (zero_fast u) (cross_refl _ _ hx) hs
  have left := cross_trans _ _ _ _ _ _ assoc (cross_trans _ _ _ _ _ _ right (GaussianNameRingLaws.add_zero F u hx))
  have addinv := cross_trans _ _ _ _ _ _ (add_commutative F f u x hx hf) (add_negative f x hf)
  have cancel := add_cross Q zeroF g g v y y y (add_fast _ _ _ _ hx hf) (zero_fast y) hg hg
    (cross_trans _ _ _ _ _ _ addinv (zeros_cross x y)) (cross_refl _ _ hg)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ left)
    (cross_trans _ _ _ _ _ _ cancel (GaussianNameRingLaws.add_zero_left g y hg))

theorem positive_exponent_from_original (z B N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent (negativeF logExponentF) fixedExponentF
      (negativeData (logExponentData z B N)) (fixedExponentData (ofGaussian z B) N) := by
  let q := ofGaussian z B
  let x := logExponentData z B N
  let y := fixedExponentData q N
  let a := qnegative q
  let u := negativeData x
  have hL := log_regular (Γ := Γ) N hN
  have hf := log_exponent_regular (Γ := Γ) z B N hN
  have hg := fixed_exponent_regular q N hN
  have swap := GaussianNameRingLaws.multiply_commutative logF constantF N a hL (constant_regular a)
  have first := add_cross logExponentF fixedExponentF fixedExponentF fixedExponentF x (fixedExponentData a N) y y
    hf (fixed_exponent_regular a N hN) hg hg swap (cross_refl _ _ hg)
  have sum := fixed_exponent_sum a q N hN
  have zero := fixed_exponent_coeff_congr (qadd a q) qzero N hN (negate_sum q)
  exact named_additive_inverse logExponentF fixedExponentF x y hf hg
    (cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ sum (cross_trans _ _ _ _ _ _ zero (zero_exponent N u hN))))

theorem positive_from_original (z B N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent negExpF fixedPowerF (negExpData z B N) (fixedPowerData (ofGaussian z B) N) :=
  GaussianExponentialRadiusIndependence.independent_radii_proper (negativeF logExponentF) fixedExponentF _ _ _ _
    (GaussianExponentialInverse.negative_input _ _ _ (exponent_input z B N hN))
    (exponential_input _ _ (fixed_exponent_regular _ N hN)) (positive_exponent_from_original z B N hN)

theorem actual_positive_Euler_exponent_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ crossEquivalent negExpF fixedPowerF (negExpData (var 0) (var 1) (var 2))
      (fixedPowerData (ofGaussian (var 0) (var 1)) (var 2))) :=
  closeUniv 3 (.impI (positive_from_original _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGaussEulerPositiveExponents
