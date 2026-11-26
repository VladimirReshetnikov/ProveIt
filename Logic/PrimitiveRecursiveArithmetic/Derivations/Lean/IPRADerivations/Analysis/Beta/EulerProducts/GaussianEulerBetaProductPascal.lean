import IPRADerivations.Analysis.Beta.EulerProducts.GaussianEulerBetaProductValue
import IPRADerivations.Analysis.Gamma.EulerProducts.Exponents.GaussianGammaExponentStep
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianRationalRoundedPower

/-!
# Pascal recurrence of the original reciprocal Euler head

Actual reciprocal unit products and the exact original head successor
and shift identify the two neighboring values as two literal factors
times the SAME next reciprocal head. Their original factor difference
is one. Thus the product-side Beta value satisfies precisely the Pascal
recurrence of the separately proved stored polynomial primitive.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerBetaProductPascal

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qmul ofGaussian canonical)
open GaussianRationalMetric (qsub)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr)
open GaussianRationalReciprocal (qone)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalNaturalScale (natScale naturalPoint)
open GaussianGammaEulerHead (head factor)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaHarmonicIncrement (reciprocalPoint)
open GaussianEulerBetaProductValue (value value_canonical value_inverse)
open GaussianEulerBetaPoleGuard (source)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem one_left (x : PTm n) (hx : Γ ⊢[PRAAx] canonical x) : Γ ⊢[PRAAx] qmul qone x ≐ x :=
  (qmul_commutative _ _).eqTrans (qmul_one_right x hx)

theorem inverse_unique (a u v : PTm n) (hu : Γ ⊢[PRAAx] canonical u) (hv : Γ ⊢[PRAAx] canonical v)
    (hU : Γ ⊢[PRAAx] qmul a u ≐ qone) (hV : Γ ⊢[PRAAx] qmul a v ≐ qone) : Γ ⊢[PRAAx] u ≐ v :=
  (qmul_one_right u hu).eqSymm.eqTrans ((qmul_congr (.eqRefl _) hV.eqSymm).eqTrans
    ((qmul_associative _ _ _).eqSymm.eqTrans
      ((qmul_congr ((qmul_commutative _ _).eqTrans hU) (.eqRefl _)).eqTrans (one_left v hv))))

theorem inverse_factor (a b c u v : PTm n) (hv : Γ ⊢[PRAAx] canonical v)
    (hc : Γ ⊢[PRAAx] c ≐ qmul b a) (hU : Γ ⊢[PRAAx] qmul c u ≐ qone) (hV : Γ ⊢[PRAAx] qmul b v ≐ qone) : Γ ⊢[PRAAx] v ≐ qmul a u :=
  inverse_unique b v _ hv (GaussianRationalHorner.qmul_canonical _ _) hV
    ((qmul_associative _ _ _).eqSymm.eqTrans ((qmul_congr hc.eqSymm (.eqRefl _)).eqTrans hU))

theorem natural_reciprocal_unit (N : PTm n) : Γ ⊢[PRAAx] qmul (naturalPoint (succ N)) (reciprocalPoint N) ≐ qone := by
  have n := zero_lt_succ (Γ := Γ) N
  have scaled : Γ ⊢[PRAAx] natScale (succ N) (reciprocalPoint N) ≐ qone :=
    GaussianRationalHorner.canonical_unique _ _ (ComplexLogarithmRemainder.scale (succ N) ComplexLogarithmRemainder.oneCode) (succ N)
      (GaussianRationalNaturalScale.natScale_canonical _ _) GaussianRationalSyntheticDivision.qone_canonical n
      (GaussianRationalNaturalScale.natScale_represents _ _ _ _ n (GaussianRationalHorner.ofGaussian_represents _ _ n))
      (GaussianRationalReciprocal.qone_represents_scaled (succ N))
  exact (GaussianRationalNaturalScale.natScale_as_product _ _).eqSymm.eqTrans scaled

/-- The ORIGINAL shifted head and the ORIGINAL z/[B(N+1)] factor. -/
theorem shifted_head_factor (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    head z B (succ N) ≐ qmul (head (shifted z B) B N) (ofGaussian z (B*succ N)) := by
  let H := head z B (succ N)
  have unit : Γ ⊢[PRAAx] qmul (reciprocalPoint N) (naturalPoint (succ N)) ≐ qone :=
    (qmul_commutative _ _).eqTrans (natural_reciprocal_unit N)
  exact (one_left H (GaussianEulerBetaProductValue.head_canonical z B (succ N))).eqSymm.eqTrans
    ((qmul_congr unit.eqSymm (.eqRefl _)).eqTrans
      ((qmul_associative _ _ _).eqTrans
        ((qmul_congr (.eqRefl _) (GaussianEulerBetaProductValue.head_IBP_balance z B N hB).eqSymm).eqTrans
          ((qmul_associative _ _ _).eqSymm.eqTrans
            ((qmul_congr (GaussianGammaExponentStep.reciprocal_times_point z B N hB) (.eqRefl _)).eqTrans (qmul_commutative _ _))))))

theorem old_value_factor (z B A N : PTm n) (h : Γ ⊢[PRAAx] source z B A) : Γ ⊢[PRAAx]
    value z B N ≐ qmul (factor N z B) (value z B (succ N)) :=
  inverse_factor _ _ _ _ _ (value_canonical z B N) (GaussianGammaEulerHead.head_succ z B N)
    (value_inverse z B A (succ N) h) (value_inverse z B A N h)
theorem shifted_value_factor (z B A N : PTm n) (h : Γ ⊢[PRAAx] source z B A) : Γ ⊢[PRAAx]
    value (shifted z B) B N ≐ qmul (ofGaussian z (B*succ N)) (value z B (succ N)) :=
  inverse_factor _ _ _ _ _ (value_canonical (shifted z B) B N) (shifted_head_factor z B N h.andE₁)
    (value_inverse z B A (succ N) h) (value_inverse (shifted z B) B A N (GaussianEulerBetaProductValue.shifted_source z B A h))

theorem factor_difference (z B N : PTm n) : Γ ⊢[PRAAx] qsub (factor N z B) (ofGaussian z (B*succ N)) ≐ qone :=
  (qsub_congr (GaussianReciprocalHorner.qadd_commutative _ _) (.eqRefl _)).eqTrans
    (GaussianRationalSyntheticDivision.qadd_sub_cancel _ qone GaussianRationalSyntheticDivision.qone_canonical)

theorem product_value_Pascal (z B A N : PTm n) (h : Γ ⊢[PRAAx] source z B A) : Γ ⊢[PRAAx]
    value z B (succ N) ≐ qsub (value z B N) (value (shifted z B) B N) := by
  have rhs := (qsub_congr (old_value_factor z B A N h) (shifted_value_factor z B A N h)).eqTrans
    ((qsub_congr (qmul_commutative _ _) (qmul_commutative _ _)).eqTrans
      ((GaussianRationalRoundedPower.multiplication_difference _ _ _).eqTrans
        ((qmul_congr (.eqRefl _) (factor_difference z B N)).eqTrans (qmul_one_right _ (value_canonical z B (succ N))))))
  exact rhs.eqSymm

theorem value_zero (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    value z B zero ≐ GaussianRationalReciprocal.reciprocal (ofGaussian z B) :=
  GaussianNameReciprocal.reciprocal_congr (GaussianGammaEulerHead.head_zero z B hB)

def output (z B N : PTm n) : PTm n := pairT (value z B (succ N))
  (pairT (qsub (value z B N) (value (shifted z B) B N)) (value z B zero))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (z B N : PTm n) : PTm n := ap3 outputF z B N
theorem program_at (z B N : PTm n) : Γ ⊢[PRAAx] run z B N ≐ output z B N := by
  simpa [run,outputF,output,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![z,B,N]

theorem actual_original_Beta_product_value_Pascal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) ⟶ value (var 0) (var 1) (succ (var 3)) ≐
      qsub (value (var 0) (var 1) (var 3)) (value (shifted (var 0) (var 1)) (var 1) (var 3))) :=
  closeUniv 4 (.impI (product_value_Pascal _ _ _ _ Prf.hyp0))
theorem actual_original_Beta_product_zero_value_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ value (var 0) (var 1) zero ≐ GaussianRationalReciprocal.reciprocal (ofGaussian (var 0) (var 1))) :=
  closeUniv 2 (.impI (value_zero _ _ Prf.hyp0))
theorem actual_original_positive_integer_reciprocal_unit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (qmul (naturalPoint (succ (var 0))) (reciprocalPoint (var 0)) ≐ qone) :=
  closeUniv 1 (natural_reciprocal_unit _)
theorem actual_Beta_product_Pascal_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) :=
  closeUniv 3 (program_at _ _ _)

end LeanProofs.IPRA.Analysis.GaussianEulerBetaProductPascal
