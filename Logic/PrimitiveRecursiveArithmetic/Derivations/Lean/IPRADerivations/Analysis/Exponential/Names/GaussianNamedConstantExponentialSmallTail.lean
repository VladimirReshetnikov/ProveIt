import IPRADerivations.Analysis.Exponential.Estimates.GaussianRationalExponentialSmallTail
import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianSignedNameExponentialOrder

/-!
# The named exponential's fixed Taylor error on the half disk

Evaluate the original exponential of a constant rational at a later
clock whose actual Taylor degree is at least the requested degree.
The finite factored tail and the original name's regularity give
the truncation error and an explicit observation allowance.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedConstantExponentialSmallTail

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianRadiusExponentialName (sample sample_at sample_regularity index)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalExponentialTail (scalarPrefix prefix_difference)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded bounded)
open GaussianRationalPolynomialExponential (scalarSum scalarBody)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (monus)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def errorNumerator (m p A B : PTm n) : PTm n := two*pw A (succ m)*unit p+two*pw B (succ m)
def errorDenominator (m p B : PTm n) : PTm n := pw B (succ m)*unit p

theorem constant_error (q m p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hq : Γ ⊢[PRAAx] bounded q A B) (hh : Γ ⊢[PRAAx] bounded q one two) :
    Γ ⊢[PRAAx] distanceBounded (sample constantF one p q) (scalarSum q m)
      (errorNumerator m p A B) (errorDenominator m p B) := by
  let s := p+m
  let K := index one s
  let k := monus K m
  let N := succ m
  let U := unit p
  let V := unit s
  let D := pw B N
  have hK : Γ ⊢[PRAAx] le m K :=
    le_congr (.eqRefl _) (GaussianRadiusExponentialName.index_add one p m).eqSymm
      (le_add_left m (index one p))
  have hDeg : Γ ⊢[PRAAx] succ K ≐ N+k :=
    (congrSucc (eq_add_of_le hK)).eqTrans (by dsimp [N,k]; ipra_ring)
  have query : Γ ⊢[PRAAx] sample constantF one s q ≐ scalarPrefix q (N+k) :=
    (sample_at constantF one s q).eqTrans
      (GaussianRationalFiniteSum.sum_index_congr scalarBody hDeg
        (constant_at (GaussianRadiusExponentialName.inputPrecision one s) q))
  have ds : Γ ⊢[PRAAx] le one D := GaussianFactorBudget.power_positive B N hB
  have finite : Γ ⊢[PRAAx] distanceBounded (sample constantF one s q) (scalarSum q m) (two*pw A N) D :=
    GaussianRationalReciprocal.bound_congr
      ((GaussianRationalSyntheticDivision.qsub_congr query (.eqRefl _)).eqTrans (prefix_difference q N k)).eqSymm
      (.eqRefl _) (.eqRefl _) (GaussianRationalExponentialSmallTail.small_tail q N A B k hB hq hh)
  have inp := GaussianSignedNameExponentialOrder.constant_input q one
    (GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ RationalAlgebra.two_positive
      (le_refl one) (le_congr (one_mul one).eqSymm (one_mul two).eqSymm RationalAlgebra.two_positive) hh)
  have pPos := unit_positive (Γ := Γ) p
  have sPos := unit_positive (Γ := Γ) s
  have increase : Γ ⊢[PRAAx] le U V := GaussianBalancedRadiusArithmetic.unit_monotone p s (le_add_right p m)
  have near : Γ ⊢[PRAAx] distanceBounded (sample constantF one p q) (sample constantF one s q) two U :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ pPos sPos) pPos
      (by ipra_le 𝔞 U*sl increase) (sample_regularity constantF one q p s inp)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp [errorNumerator,U,D,N]; ipra_ring)
    (mul_comm U D) (GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ pPos ds near finite)

theorem actual_named_constant_exponential_small_tail_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 4) ⟶ bounded (var 0) (var 3) (var 4) ⟶ bounded (var 0) one two ⟶
      distanceBounded (sample constantF one (var 2) (var 0)) (scalarSum (var 0) (var 1))
        (errorNumerator (var 1) (var 2) (var 3) (var 4)) (errorDenominator (var 1) (var 2) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (constant_error _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianNamedConstantExponentialSmallTail
