import IPRADerivations.Analysis.Gamma.EulerProducts.Factorials.GaussianGammaRisingFactorial
import IPRADerivations.Analysis.Gamma.Names.Input.GaussianGammaInputProperness

/-!
# Actual native falling-factorial numerator and factorial normalization

The finite numerator reads z-N+1,...,z in ascending order, using the
original rising-product program. Each in-range entry is the actual
factor z-j at the reversed numerical index. Its original native endpoint
is z+1. Division by N! is a positive rational constant, even at N=0.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaFallingFactorial

open_ipra
open ComplexLogarithmRemainder (oneCode scale)
open GaussianRootAlgebra (equal equal_of_values)
open GaussianGammaEulerHeadShift (shifted linear)
open GaussianGammaShiftTrajectory (point point_native)
open GaussianGammaRepeatedShift (risingProduct)
open GaussianRationalHorner (ofGaussian qmul canonical)
open GaussianRationalSyntheticDivision (qone qmul_congr)
open GaussianRationalNaturalScale (naturalPoint)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def start (z B N : PTm n) : PTm n := GaussianRootAlgebra.sub (shifted z B) (scale (B*N) oneCode)
def baseRadius (R N : PTm n) : PTm n := R+N+one
def endpointRadius (R N : PTm n) : PTm n := baseRadius R N+N
def fallingProduct (z B N : PTm n) : PTm n := risingProduct (start z B N) B N
def fallingFactor (z B j : PTm n) : PTm n := ofGaussian (GaussianRootAlgebra.sub z (scale (B*j) oneCode)) B
def factorialInverse (N : PTm n) : PTm n := GaussianGammaEulerShiftLimit.reciprocalPoint (Products.fact N)
def binomial (z B N : PTm n) : PTm n := qmul (factorialInverse N) (fallingProduct z B N)

ipra_subst start
ipra_subst baseRadius
ipra_subst endpointRadius
ipra_subst fallingProduct
ipra_subst fallingFactor
ipra_subst factorialInverse [GaussianGammaEulerShiftLimit.reciprocalPoint, Products.fact]
ipra_subst binomial

theorem endpoint_native (z B N : PTm n) : Γ ⊢[PRAAx] equal (point (start z B N) B N) (shifted z B) := by
  apply GaussianRootAlgebra.equal_trans (point_native (start z B N) B N)
  apply equal_of_values <;>
    simp only [GaussianGammaEulerHeadLower.translated,start,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,
      GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
      GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one]
  all_goals ipra_simps; ring

theorem start_source (z R B N : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B) : Γ ⊢[PRAAx]
    GaussianGammaCanonicalExponent.source (start z B N) (baseRadius R N) B := by
  have moved := GaussianGammaEulerShiftLimit.shifted_source z R B h
  have oneBound : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (oneCode : PTm n) one :=
    le_congr ComplexLogarithmRemainder.normSq_one.eqSymm (by ipra_ring) (le_refl one)
  have subtractBound := ComplexLogarithmRemainder.bounded_neg (ComplexLogarithmRemainder.bounded_scale (B*N) oneBound)
  have original := ComplexLogarithmRemainder.bounded_add moved.andE₂.andE₂ subtractBound
  exact .andI (le_trans h.andE₁ (le_of_eq_add (d := N+one) (by unfold baseRadius; ipra_ring)))
    (.andI h.andE₂.andE₁ (le_congr (.eqRefl _) (by unfold baseRadius; ipra_ring) original))

theorem endpoint_source (z R B N : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B) : Γ ⊢[PRAAx]
    GaussianGammaCanonicalExponent.source (shifted z B) (endpointRadius R N) B :=
  GaussianGammaFiniteValueProperness.source_equal _ _ _ _
    (GaussianGammaShiftTrajectory.point_source _ _ _ N (start_source z R B N h)) (endpoint_native z B N)

/-- Literal in-range entry: z-N+1+i equals z-(N-1-i). -/
theorem original_factor_at (z B N i : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    linear (start z B N) B i ≐ fallingFactor z B (monus N (succ i)) := by
  have split := natEq (AnalyticNumberTheory.Totatives.split_lt hi)
  apply GaussianGammaFiniteValueProperness.fraction_equal _ _ B hB
  apply equal_of_values
  · simp only [GaussianGammaEulerHeadLower.translated,start,shifted,GaussianRootAlgebra.re_add,GaussianRootAlgebra.re_sub,
      GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one]
    ipra_simps
    linear_combination -(Groth.ι (IPRA.Q.mk Γ B))*split
  · simp only [GaussianGammaEulerHeadLower.translated,start,shifted,GaussianRootAlgebra.im_add,GaussianRootAlgebra.im_sub,
      GaussianRootAlgebra.im_scale,GaussianRootAlgebra.im_one]
    ring

theorem original_entry_at (z B N i : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    inst2 GaussianGammaRepeatedShift.linearBody i (GaussianGammaShiftTrajectory.data (start z B N) B) ≐
      fallingFactor z B (monus N (succ i)) :=
  (GaussianGammaRepeatedShift.linear_at _ _ _).eqTrans (original_factor_at z B N i hB hi)

theorem falling_canonical (z B N : PTm n) : Γ ⊢[PRAAx] canonical (fallingProduct z B N) :=
  GaussianGammaRepeatedShift.prefix_canonical _ _ _
theorem factorial_positive (N : PTm n) : Γ ⊢[PRAAx] le one (Products.fact N) :=
  le_congr (.eqRefl _) (AnalyticNumberTheory.Primes.fact_pos N).eqSymm
    (zero_lt_succ (LeanProofs.IPRA.PTm.pred (Products.fact N)))
theorem factorial_inverse_unit (N : PTm n) : Γ ⊢[PRAAx]
    qmul (naturalPoint (Products.fact N)) (factorialInverse N) ≐ qone := by
  have scaled : Γ ⊢[PRAAx] GaussianRationalNaturalScale.natScale (Products.fact N) (factorialInverse N) ≐ qone :=
    GaussianRationalHorner.canonical_unique _ _ _ _ (GaussianRationalNaturalScale.natScale_canonical _ _)
      GaussianRationalSyntheticDivision.qone_canonical (factorial_positive N)
      (GaussianRationalNaturalScale.natScale_represents _ _ _ _ (factorial_positive N)
        (GaussianRationalHorner.ofGaussian_represents _ _ (factorial_positive N)))
      (GaussianRationalReciprocal.qone_represents_scaled (Products.fact N))
  exact (GaussianRationalNaturalScale.natScale_as_product _ _).eqSymm.eqTrans scaled

theorem binomial_canonical (z B N : PTm n) : Γ ⊢[PRAAx] canonical (binomial z B N) :=
  GaussianRationalHorner.qmul_canonical _ _
theorem factorial_normalization (z B N : PTm n) : Γ ⊢[PRAAx]
    qmul (naturalPoint (Products.fact N)) (binomial z B N) ≐ fallingProduct z B N :=
  (GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans
    ((qmul_congr (factorial_inverse_unit N) (.eqRefl _)).eqTrans
      ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
        (GaussianReciprocalHorner.qmul_one_right _ (falling_canonical z B N))))

theorem actual_falling_factorial_native_endpoint_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (equal (point (start (var 0) (var 1) (var 2)) (var 1) (var 2)) (shifted (var 0) (var 1))) :=
  closeUniv 3 (endpoint_native _ _ _)
theorem actual_falling_factorial_derived_disk_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianGammaCanonicalExponent.source (var 0) (var 1) (var 2) ⟶
      GaussianGammaCanonicalExponent.source (start (var 0) (var 2) (var 3)) (baseRadius (var 1) (var 3)) (var 2)) :=
  closeUniv 4 (.impI (start_source _ _ _ _ Prf.hyp0))
theorem actual_falling_factorial_in_range_factor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((le one (var 1) ⋏ lt (var 3) (var 2)) ⟶
      linear (start (var 0) (var 1) (var 2)) (var 1) (var 3) ≐
        fallingFactor (var 0) (var 1) (monus (var 2) (succ (var 3)))) :=
  closeUniv 4 (.impI (original_factor_at _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem actual_binomial_factorial_normalization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (qmul (naturalPoint (Products.fact (var 2))) (binomial (var 0) (var 1) (var 2)) ≐
      fallingProduct (var 0) (var 1) (var 2)) := closeUniv 3 (factorial_normalization _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaFallingFactorial
