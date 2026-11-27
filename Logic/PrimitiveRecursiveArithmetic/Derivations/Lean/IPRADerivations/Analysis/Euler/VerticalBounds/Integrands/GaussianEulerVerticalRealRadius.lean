import IPRADerivations.Analysis.Euler.Integration.Decay.Quadrature.GaussianEulerDecayRealSamples
import IPRADerivations.Analysis.RationalArithmetic.Representations.RationalRepresentedUpper

/-!
# A positive exact radius from a real observation's lower envelope

If a real observation is at least -1/U, its own real coordinate plus
2/U is a nonnegative rational radius bounding that observation. The
radius has explicit original native numerator and denominator data.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerVerticalRealRadius

open_ipra
open GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open ComplexLogarithmRemainder (re im normSq)
open RationalGaussianEmbedding (scalarZero embed)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalMetric (bounded)
open GaussianRationalHorner (positive_product)
open RationalValueBounds (upper)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def gap (q U : PTm n) : PTm n := monus (U*(re (rawGaussian q)).pos+rawDen q) (U*(re (rawGaussian q)).neg)
def numerator (q U : PTm n) : PTm n := gap q U+rawDen q
def denominator (q U : PTm n) : PTm n := rawDen q*U
def scalar (q U : PTm n) : PTm n := RationalArithmetic.add (fstT q) (fraction two U)
def radius (q U : PTm n) : PTm n := embed (scalar q U)

theorem lower_gap (q U : PTm n) (h : Γ ⊢[PRAAx] upper scalarZero (fstT q) one U) : Γ ⊢[PRAAx]
    le (U*(re (rawGaussian q)).neg) (U*(re (rawGaussian q)).pos+rawDen q) := by
  have value := zle_toZ (RationalRepresentedUpper.to_signed _ _ (ZT.ofNat zero) (re (rawGaussian q)) one (rawDen q) one U
    (RationalGaussianEmbedding.scalar_zero_represents one) (raw_represents q).andE₁ h)
  apply le_of_eq_add (d := PolynomialBisection.slack
    (RationalRepresentedUpper.left (ZT.ofNat zero) (rawDen q) U)
    (RationalRepresentedUpper.right (re (rawGaussian q)) one (rawDen q) one U))
  apply deriveNat
  dsimp only [PolynomialBisection.slack,RationalRepresentedUpper.left,RationalRepresentedUpper.right] at value ⊢
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat] at value
  simp only [ZT.toZ] at value
  ipra_simps
  linear_combination -value

theorem gap_identity (q U : PTm n) (h : Γ ⊢[PRAAx] upper scalarZero (fstT q) one U) : Γ ⊢[PRAAx]
    U*(re (rawGaussian q)).pos+rawDen q ≐ U*(re (rawGaussian q)).neg+gap q U :=
  eq_add_of_le (lower_gap q U h)

theorem denominator_positive (q U : PTm n) (hU : Γ ⊢[PRAAx] le one U) : Γ ⊢[PRAAx] le one (denominator q U) :=
  positive_product _ _ (raw_den_positive q) hU

theorem corrected_represents (q U : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (h : Γ ⊢[PRAAx] upper scalarZero (fstT q) one U) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (scalar q U) (ZT.ofNat (numerator q U)) (denominator q U) := by
  have actual := RationalRepresentations.represents_add _ _ _ _ _ _ (raw_represents q).andE₁ (fraction_represents two U hU)
  apply GaussianRationalHorner.scalar_congr (.eqRefl _) _ (.eqRefl _) actual
  apply ZT.derive
  have e := natEq (gap_identity (Γ := Γ) q U h)
  simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat,numerator]
  simp only [ZT.toZ]
  ipra_simps
  linear_combination e

theorem corrected_positive (q U : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (h : Γ ⊢[PRAAx] upper scalarZero (fstT q) one U) : Γ ⊢[PRAAx]
    GaussianPositiveRealArithmetic.positive (radius q U) :=
  GaussianPositiveRealArithmetic.positive_embed _ (GaussianRationalL1.nonnegative_of_representation _ _ _
    (denominator_positive q U hU) (corrected_represents q U hU h))

theorem corrected_bounds_original (q U : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (hr : Γ ⊢[PRAAx] GaussianRationalConjugation.point q ≐ q)
    (h : Γ ⊢[PRAAx] upper scalarZero (fstT q) one U) : Γ ⊢[PRAAx]
    bounded q (numerator q U) (denominator q U) := by
  apply (GaussianRationalMetric.bounded_iff q (rawGaussian q) (rawDen q) _ _
    (raw_den_positive q) (denominator_positive q U hU) (raw_represents q)).iffMpr
  apply le_of_eq_add (d := num 4*gap q U*rawDen q*rawDen q*rawDen q)
  apply deriveNat
  have e := natEq (gap_identity (Γ := Γ) q U h)
  have imzero := ZT.toZ_eq (GaussianEulerDecayRealSamples.fixed_raw_imaginary_zero q hr)
  dsimp only [numerator,denominator]
  ipra_simps
  rw [ComplexLogarithmRemainder.normSq_eval,imzero]
  dsimp only [ZT.toZ] at *
  linear_combination -(𝔞(rawDen q)*𝔞(rawDen q))*(𝔞(gap q U)-𝔞(rawDen q)+𝔞(U)*(𝔞((re (rawGaussian q)).pos)-𝔞((re (rawGaussian q)).neg)))*e

theorem actual_corrected_real_observation_radius_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((le one (var 1) ⋏ ((GaussianRationalConjugation.point (var 0) ≐ var 0) ⋏ upper scalarZero (fstT (var 0)) one (var 1))) ⟶
      (GaussianPositiveRealArithmetic.positive (radius (var 0) (var 1)) ⋏ bounded (var 0) (numerator (var 0) (var 1)) (denominator (var 0) (var 1)))) :=
  closeUniv 2 (.impI (.andI (corrected_positive _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₂)
    (corrected_bounds_original _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianEulerVerticalRealRadius
