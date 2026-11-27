import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.GaussianRationalLowerBounds
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianPowers.GaussianRationalPowerDifference
import IPRADerivations.Analysis.RationalArithmetic.Scaling.GaussianRationalNaturalScale
import IPRADerivations.Analysis.RationalArithmetic.Complex.GaussianCoordinateRadius
import IPRADerivations.Analysis.RationalArithmetic.Embeddings.RationalGaussianEmbedding
import IPRADerivations.Analysis.RationalArithmetic.Representations.RationalRepresentedUpper

/-!
# Stable cancellation of rational squares

A lower bound on the sum of the two observations controls cancellation
of their squares with the same explicit radius when the sum has norm
at least one.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalSquareCancellation

open_ipra
open GaussianRationalHorner (qmul qadd qadd_represents represents_congr represents_rescale)
open GaussianRationalNaturalScale (naturalPoint natural_point_represents)
open GaussianRationalL1 (rawGaussian rawDen raw_den_positive raw_represents)
open GaussianRootAlgebra (equal_refl re_add re_scale re_one)
open ComplexLogarithmRemainder (add scale re normSq oneCode)
open GaussianRelativeNormTriangle (signed_le_absolute)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Foundations.GapDecision (zabs)
open RationalGaussianEmbedding (scalarZero scalar_zero_represents)
open GaussianRationalMetric (qsub qsub_canonical distanceBounded)
open GaussianRationalLowerBounds (lower cancel_bounded_product)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalPowerDifference (product_difference)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianRationalCoefficientScaling (qmul_add)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem difference_factorization (a b : PTm n) :
    Γ ⊢[PRAAx] qsub (qmul a a) (qmul b b) ≐ qmul (qsub a b) (qadd a b) :=
  (product_difference a b a b).eqTrans
    ((qadd_congr (.eqRefl _) (qmul_commutative b (qsub a b))).eqTrans
      (qmul_add (qsub a b) a b).eqSymm)

/-- Cancel the difference of two squares using a `1/B` lower bound on their sum. -/
theorem cancel_square_scaled (a b E K B : PTm n) (hK : Γ ⊢[PRAAx] le one K)
    (hB : Γ ⊢[PRAAx] le one B) (hL : Γ ⊢[PRAAx] lower (qadd a b) one B)
    (h : Γ ⊢[PRAAx] distanceBounded (qmul a a) (qmul b b) E K) :
    Γ ⊢[PRAAx] distanceBounded a b (E*B) K :=
  cancel_bounded_product (qsub a b) (qadd a b) E K B (qsub_canonical a b) hK hB hL
    (bound_congr (difference_factorization a b) (.eqRefl _) (.eqRefl _) h)

theorem cancel_square (a b E K : PTm n) (hK : Γ ⊢[PRAAx] le one K)
    (hL : Γ ⊢[PRAAx] lower (qadd a b) one one)
    (h : Γ ⊢[PRAAx] distanceBounded (qmul a a) (qmul b b) E K) :
    Γ ⊢[PRAAx] distanceBounded a b E K :=
  bound_congr (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (cancel_square_scaled a b E K one hK (le_refl one) hL h)

theorem natural_sum_lower (m q : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hq : Γ ⊢[PRAAx] RationalArgmin.rationalLE scalarZero (fstT q)) :
    Γ ⊢[PRAAx] lower (qadd (naturalPoint m) q) one one := by
  let E := rawDen q
  let a := rawGaussian q
  let b := scale E (scale m oneCode)
  let c := add b a
  let u := re a
  let v := re c
  let z := ZT.ofNat (zabs v)
  let L := RationalRepresentedUpper.left (ZT.ofNat zero) E one
  let R := RationalRepresentedUpper.right u one E zero one
  let hE := raw_den_positive (Γ := Γ) q
  have hq' := RationalValueBounds.upper_of_order scalarZero (fstT q) zero one hq
  have r : Γ ⊢[PRAAx] zle L R := RationalRepresentedUpper.to_signed _ _ _ _ one E zero one
    (scalar_zero_represents one) (raw_represents q).andE₁ hq'
  let δ₀ := monus (R.pos+L.neg) (L.pos+R.neg)
  let δ₁ := monus (z.pos+v.neg) (v.pos+z.neg)
  have rt : Γ ⊢[PRAAx] le E (zabs v) := by
    refine le_of_eq_add (d := E*monus m one+δ₀+δ₁) ?_
    have h₀ := zle_toZ r
    have h₁ := zle_toZ (Γ := Γ) (signed_le_absolute v)
    have h₂ := natEq (eq_add_of_le hm)
    apply deriveNat
    change ZT.toZ Γ L+𝔞 δ₀ = ZT.toZ Γ R at h₀
    change ZT.toZ Γ v+𝔞 δ₁ = ZT.toZ Γ z at h₁
    simp only [v,c,b,z,L,R,RationalRepresentedUpper.left,RationalRepresentedUpper.right,
      re_add,re_scale,re_one,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat,IPRA.Q.mk_add,IPRA.Q.mk_mul,map_add,map_mul] at h₀ h₁ h₂ ⊢
    ipra_simps
    linear_combination -h₁-h₀+𝔞 E*h₂
  have hc := qadd_represents _ _ b a E hE
    (represents_congr (.eqRefl _) (equal_refl _) (one_mul E)
      (represents_rescale _ _ one E (natural_point_represents m)))
    (raw_represents q)
  have hn : Γ ⊢[PRAAx] le (zabs v*zabs v) (normSq c) :=
    le_congr (.eqRefl _) (GaussianCoordinateRadius.native_squared c).eqSymm (le_add_right _ _)
  exact GaussianRationalLowerBounds.lower_from_representation _ _ _ _ _ hE (le_refl one) hc
    (le_congr (by ipra_ring) (by ipra_ring) (le_trans (le_mul_mono rt rt) hn))

theorem actual_rational_square_cancellation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((le one (var 0) ⋏ lower (qadd (var 3) (var 2)) one one) ⟶
      distanceBounded (qmul (var 3) (var 3)) (qmul (var 2) (var 2)) (var 1) (var 0) ⟶
        distanceBounded (var 3) (var 2) (var 1) (var 0)) :=
  closeUniv 4 (.impI (.impI (cancel_square _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRationalSquareCancellation
