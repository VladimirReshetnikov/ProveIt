import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.RationalSumAdditivity
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.RationalSumConstants
import IPRADerivations.Analysis.RationalArithmetic.Distances.GaussianRationalL1

/-!
# The scalar quadratic interval bound for Euler logarithm residuals

The actual scalar sum uses the original reciprocal-power tail with
exponent two, and adds the constant observation allowance in each row.
Its bound is the exact rational A/N + C*r/U for every numerical
interval length r and positive N and U.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerResidualIntervalMajorant

open_ipra
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalHorner (positive_product)
open RationalAlgebra (add_congr multiply_congr)
open RationalArithmetic (add multiply)
open RationalArgmin (rationalLE rationalLE_congr reflexive)
open RationalNonnegativePowers (fraction_congr fraction_multiply)
open RationalReciprocalPowerTail (reciprocalPower potential)
open RationalSumAdditivity (addedBody added_term sum_additive)
open RationalSumConstants (constantBody sum_constant term_constant)
open RationalSumLinearity (scaledBody scaled_term sum_homogeneous)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private abbrev quadraticBody : PTm 2 := scaledBody RationalReciprocalPowerTail.body
private abbrev quadraticData (A N : PTm n) : PTm n := pairT (fraction A one) (RationalReciprocalPowerTail.data two N)

def budgetBody : PTm 2 := addedBody quadraticBody constantBody
def budgetData (A C U N : PTm n) : PTm n := pairT (quadraticData A N) (fraction C U)
def budgetSum (A C U N r : PTm n) : PTm n := RationalFiniteSum.sum budgetBody r (budgetData A C U N)
def numerator (A C U N r : PTm n) : PTm n := A * U + C * r * N
def denominator (U N : PTm n) : PTm n := N * U

ipra_subst budgetData [one, two]

private theorem fraction_add (a b c d : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d) :
    Γ ⊢[PRAAx] add (fraction a b) (fraction c d) ≐ fraction (a * d + c * b) (b * d) := by
  have hbd := positive_product _ _ hb hd
  have rep := RationalRepresentations.represents_add _ _ _ _ _ _
    (fraction_represents a b hb) (fraction_represents c d hd)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.add_guard _ _)
    (RationalNormalForm.normalize_well_formed _ _ hbd) rep (fraction_represents _ _ hbd) hbd hbd
  apply ZT.derive
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_ofNat, Q.mk_add, Q.mk_mul, map_add, map_mul]

private alias square_denominator := Common.pw_two

private theorem quadratic_term (A N i : PTm n) :
    Γ ⊢[PRAAx] inst2 quadraticBody i (quadraticData A N) ≐ fraction A (succ (N + i) * succ (N + i)) := by
  let k := succ (N + i)
  have hk : Γ ⊢[PRAAx] le one k := zero_lt_succ _
  have hD := positive_product _ _ hk hk
  have at_i := (RationalReciprocalPowerTail.term_at (Γ := Γ) two N i).eqTrans
    (fraction_congr (.eqRefl _) (square_denominator k))
  exact (scaled_term _ i (fraction A one) (RationalReciprocalPowerTail.data two N)).eqTrans
    ((multiply_congr (.eqRefl _) at_i).eqTrans
      ((fraction_multiply A one one (k * k) (le_refl one) hD).eqTrans
        (fraction_congr (by ipra_ring) (one_mul _))))

/-- The exact scalar allowance of row `N+i+1`. -/
theorem budget_term (A C U N i : PTm n) (hU : Γ ⊢[PRAAx] le one U) :
    Γ ⊢[PRAAx] inst2 budgetBody i (budgetData A C U N) ≐
      fraction (A * U + C * (succ (N + i) * succ (N + i))) ((succ (N + i) * succ (N + i)) * U) := by
  let k := succ (N + i)
  have hk : Γ ⊢[PRAAx] le one k := zero_lt_succ _
  have hD := positive_product _ _ hk hk
  exact (added_term quadraticBody constantBody i (quadraticData A N) (fraction C U)).eqTrans
    ((add_congr (quadratic_term A N i) (by rw [term_constant]; exact .eqRefl _)).eqTrans
      (fraction_add A (k * k) C U hD hU))

private theorem potential_two (N : PTm n) : Γ ⊢[PRAAx] potential two N ≐ fraction one N :=
  fraction_congr (.eqRefl _) ((congrMul (pred_succ one) (congrAp2 powF (pred_succ one) (.eqRefl N))).eqTrans
    ((one_mul _).eqTrans (pw_one N)))

theorem exact_scalar_sum (A C U N r : PTm n) (hU : Γ ⊢[PRAAx] le one U) :
    Γ ⊢[PRAAx] budgetSum A C U N r ≐
      add (multiply (fraction A one) (RationalReciprocalPowerTail.tail two N r)) (fraction (C * r) U) := by
  have constant := (sum_constant r (fraction C U) (RationalNormalForm.normalize_well_formed _ _ hU)).eqTrans
    ((fraction_multiply C U r one hU (le_refl one)).eqTrans (fraction_congr (.eqRefl _) (by ipra_ring)))
  exact (sum_additive quadraticBody constantBody r (quadraticData A N) (fraction C U)).eqTrans
    (add_congr (sum_homogeneous _ _ _ _) constant)

/-- The actual scalar budget sums to at most `A/N + C*r/U`. -/
theorem scalar_bound (A C U N r : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hU : Γ ⊢[PRAAx] le one U) :
    Γ ⊢[PRAAx] rationalLE (budgetSum A C U N r) (fraction (numerator A C U N r) (denominator U N)) := by
  let a := fraction A one
  let b := fraction (C * r) U
  have nonnegative := GaussianRationalL1.nonnegative_of_representation (Γ := Γ) a A one
    (le_refl one) (fraction_represents A one (le_refl one))
  have t := RationalReciprocalPowerTail.sharp_tail (Γ := Γ) two N r (le_refl two) hN
  have scaled := RationalArithmetic.multiply_monotone a _ _ nonnegative t
  have upper : Γ ⊢[PRAAx] multiply a (potential two N) ≐ fraction A N :=
    (multiply_congr (.eqRefl _) (potential_two N)).eqTrans
      ((fraction_multiply A one one N (le_refl one) hN).eqTrans
        (fraction_congr (by ipra_ring) (one_mul _)))
  have added := GaussianRationalSyntheticBounds.add_monotone _ _ _ _ scaled (reflexive b)
  exact rationalLE_congr (exact_scalar_sum A C U N r hU).eqSymm
    ((add_congr upper (.eqRefl _)).eqTrans (fraction_add A N (C * r) U hN hU)) added

theorem actual_Euler_residual_scalar_interval_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 3) ⟶ le one (var 2) ⟶
      rationalLE (budgetSum (var 0) (var 1) (var 2) (var 3) (var 4))
        (fraction (numerator (var 0) (var 1) (var 2) (var 3) (var 4)) (denominator (var 2) (var 3)))) :=
  closeUniv 5 (.impI (.impI (scalar_bound _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerResidualIntervalMajorant
