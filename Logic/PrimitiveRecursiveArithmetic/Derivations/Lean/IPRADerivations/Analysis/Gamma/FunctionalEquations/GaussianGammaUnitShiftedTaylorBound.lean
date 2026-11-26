import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGammaUnitReciprocalShift
import IPRADerivations.Analysis.Gamma.Taylor.GaussianGammaQuadraticSampler

/-!
# The cubic error of the actual shifted reciprocal times the step

The original reciprocal samples at the small and shifted points are
compared at a common auxiliary query. A cubic budget on that query
preserves the actual Euler–Mascheroni observation in the center.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaUnitShiftedTaylorBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaUnitReciprocalShift (small large step small_source original_reciprocal_shift_observations)
open GaussianGammaFiniteQuadraticExpansion (quadratic)
open GaussianGammaUnitCoefficientMass (budget)
open ComplexLogarithmRemainder (oneCode)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def cubic (D : PTm n) : PTm n := D*D*D

theorem cubic_positive (D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx] le one (cubic D) :=
  positive_product _ _ (positive_product _ _ hD hD) hD

theorem denominator_le_cubic (D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx] le D (cubic D) := by
  have square : Γ ⊢[PRAAx] le D (D*D) :=
    le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right D hD)
  exact le_trans square (mul_le_mul_right D square)

theorem cubic_power (D : PTm n) : Γ ⊢[PRAAx] pw D (num 3) ≐ cubic D := by
  have sq : Γ ⊢[PRAAx] pw D two ≐ D*D := (pw_succ D one).eqTrans (congrMul (pw_one D) (.eqRefl _))
  exact (pw_succ D two).eqTrans (congrMul sq (.eqRefl _))

theorem original_small_cubic (t D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (ht : Γ ⊢[PRAAx] le (cubic D) (unit t)) : Γ ⊢[PRAAx]
    distanceBounded (small t D) (quadratic t (step D)) (budget one+two) (cubic D) := by
  let U := unit t
  let C := cubic D
  have hC := cubic_positive D hD
  have hU := unit_positive (Γ := Γ) t
  have hs : Γ ⊢[PRAAx] GaussianGammaQuadraticSampler.source oneCode one D one D :=
    .andI (small_source D hD) (.andI hD (.andI hD (GaussianGammaUnitEulerDifference.increment_bound D D hD (le_refl _))))
  have raw := GaussianGammaQuadraticSampler.original_observations t t oneCode one D one D hs
  have pow2 := GaussianPolynomialPerturbation.one_power (Γ := Γ) two
  have pow3 := GaussianPolynomialPerturbation.one_power (Γ := Γ) (num 3)
  have numer : Γ ⊢[PRAAx] GaussianGammaQuadraticSampler.numerator t t one one D ≐ budget one*U*U+D*U+C*U :=
    congrAdd (congrAdd (congrMul (congrMul (congrMul (.eqRefl _) pow3) (.eqRefl _)) (.eqRefl _))
      (congrMul (congrMul pow2 (.eqRefl _)) (.eqRefl _))) (congrMul (cubic_power D) (.eqRefl _))
      |>.eqTrans (by ipra_ring)
  have den : Γ ⊢[PRAAx] GaussianGammaQuadraticSampler.denominator t t D ≐ C*U*U :=
    congrMul (congrMul (cubic_power D) (.eqRefl _)) (.eqRefl _)
  have bounded : Γ ⊢[PRAAx] distanceBounded (small t D) (quadratic t (step D)) (budget one*U*U+D*U+C*U) (C*U*U) :=
    distance_congr (.eqRefl _) (.eqRefl _) numer den raw
  have first : Γ ⊢[PRAAx] le D U := le_trans (denominator_le_cubic D hD) ht
  have second : Γ ⊢[PRAAx] le C U := ht
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hC hU) hU) hC
    (by ipra_le 𝔞 C*𝔞 U*sl first+𝔞 C*𝔞 U*sl second) bounded

theorem original_times_neighbor_cubic (t D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (ht : Γ ⊢[PRAAx] le (cubic D) (unit t)) : Γ ⊢[PRAAx]
    distanceBounded (qmul (step D) (large t D)) (quadratic t (step D)) (budget one+num 12) (cubic D) := by
  let C := cubic D
  let U := unit t
  have hC := cubic_positive D hD
  have hU := unit_positive (Γ := Γ) t
  have grow : Γ ⊢[PRAAx] le C U := ht
  have first : Γ ⊢[PRAAx] distanceBounded (qmul (step D) (large t D)) (small t D) (num 10) C :=
    distance_radius_mono _ _ _ _ _ _ hU hC
      (by ipra_le 10*sl grow) (distance_symmetric _ _ _ _ hU (original_reciprocal_shift_observations t D hD))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hC first (original_small_cubic t D hD ht))

end LeanProofs.IPRA.Analysis.GaussianGammaUnitShiftedTaylorBound
