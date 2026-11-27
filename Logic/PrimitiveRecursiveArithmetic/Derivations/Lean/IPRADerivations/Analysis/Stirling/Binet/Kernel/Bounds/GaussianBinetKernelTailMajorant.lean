import IPRADerivations.Analysis.RationalArithmetic.Distances.GaussianRationalL1
import IPRADerivations.Analysis.RationalArithmetic.Powers.RationalPowerBounds.RationalReciprocalPowerTail
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.RationalIdentities.RationalSumLinearity

/-!
# Reciprocal-square majorant for the Binet kernel tail

The finite sum of `1/(8j²)` over `N < j ≤ N+r` is bounded by `1/(8N)`.
The rational terms and bound use the original scalar sum evaluator.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBinetKernelTailMajorant

open_ipra
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalHorner (positive_product)
open RationalAlgebra (multiply_congr)
open RationalArithmetic (multiply_monotone)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalNonnegativePowers (fraction_congr fraction_multiply)
open RationalReciprocalPowerTail (potential potential_two)
open RationalSumLinearity (scaledBody scaled_term sum_homogeneous)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "eight" => num 8

def body : PTm 2 := scaledBody RationalReciprocalPowerTail.body
def data (N : PTm n) : PTm n := pairT (fraction one eight) (RationalReciprocalPowerTail.data two N)
def sum (N r : PTm n) : PTm n := RationalFiniteSum.sum body r (data N)

ipra_subst data [one, two]

theorem eight_positive : Γ ⊢[PRAAx] le one (eight : PTm n) := by ipra_le 7

theorem term_at (N i : PTm n) : Γ ⊢[PRAAx] inst2 body i (data N) ≐
    fraction one (eight * (succ (N+i) * succ (N+i))) := by
  let k := succ (N+i)
  have hk : Γ ⊢[PRAAx] le one k := zero_lt_succ _
  have pwSquare : Γ ⊢[PRAAx] pw k two ≐ k*k :=
    (pw_succ k one).eqTrans (congrMul (pw_one k) (.eqRefl _))
  have row := (RationalReciprocalPowerTail.term_at (Γ := Γ) two N i).eqTrans (fraction_congr (.eqRefl _) pwSquare)
  have scale := scaled_term (Γ := Γ) RationalReciprocalPowerTail.body i (fraction one eight)
    (RationalReciprocalPowerTail.data two N)
  exact scale.eqTrans ((multiply_congr (.eqRefl _) row).eqTrans
    ((fraction_multiply one eight one (k*k) eight_positive (positive_product _ _ hk hk)).eqTrans
      (fraction_congr (one_mul _) (.eqRefl _))))

theorem bound (N r : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] rationalLE (sum N r) (fraction one (eight*N)) := by
  let c : PTm n := fraction one eight
  let F := RationalReciprocalPowerTail.body
  let x := RationalReciprocalPowerTail.data two N
  have hc := GaussianRationalL1.nonnegative_of_representation c one eight (eight_positive (Γ := Γ))
    (fraction_represents _ _ eight_positive)
  have raw := RationalReciprocalPowerTail.sharp_tail (Γ := Γ) two N r (le_refl two) hN
  have expanded := sum_homogeneous (Γ := Γ) F r c x
  have upper := (multiply_congr (.eqRefl c) (potential_two (Γ := Γ) N)).eqTrans
    ((fraction_multiply one eight one N eight_positive hN).eqTrans (fraction_congr (one_mul _) (.eqRefl _)))
  exact rationalLE_congr expanded.eqSymm upper (multiply_monotone c _ _ hc raw)

end LeanProofs.IPRA.Analysis.GaussianBinetKernelTailMajorant
