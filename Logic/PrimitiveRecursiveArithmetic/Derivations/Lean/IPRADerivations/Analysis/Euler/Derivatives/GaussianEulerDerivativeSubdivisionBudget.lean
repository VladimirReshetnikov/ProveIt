import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.GaussianRationalLowerBounds
import IPRADerivations.Analysis.Names.Order.GaussianFastValueCut
import IPRADerivations.Analysis.Euler.Logarithms.ParameterRates.GaussianEulerLogarithmicParameterIncrement

/-!
# Numerical separation and subdivision budgets for Euler differentiation

Native nonzeroness supplies the existing rational reciprocal certificate
|h/D|>=1/D. A genuine PR4 counter pays both the unit-log guard and an
accumulated quadratic error. The safe extra denominator factor D turns
the latter into an absolute error 1/(D*2^(p+6)); the actual reciprocal
then gives relative error 2^-(p+6). Independent later counts and read
precisions retain these budgets. No derivative or remainder is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerDerivativeSubdivisionBudget

open_ipra
open GaussianRationalHorner (ofGaussian qmul positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (reciprocal bound_congr bounded_product)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianNameReciprocal (lower)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def separated (h D : PTm n) : Fm PTm n := le one D ⋏ le one (ComplexLogarithmRemainder.normSq h)
def count (p J K D : PTm n) : PTm n := one+J+K*D*unit (p+num 6)
def countF : PR 4 := PTm.toPR (count (var 0) (var 1) (var 2) (var 3))
def run (p J K D : PTm n) : PTm n := PTm.app countF ![p,J,K,D]
def tailQuery (p D : PTm n) : PTm n := GaussianFastValueCut.exponent D (p+num 6)
def readQuery (p N C D : PTm n) : PTm n := GaussianFastValueCut.exponent (C*N*D) (p+num 6)
def compactCount (p j R E T D : PTm n) : PTm n := count p (GaussianEulerLogarithmicMultiplier.logRadius E T)
  (T*GaussianEulerLogarithmicParameterIncrement.curvature j R E T) D

ipra_subst separated
ipra_subst count
ipra_subst run
ipra_subst tailQuery
ipra_subst readQuery
ipra_subst compactCount

theorem program_at (p J K D : PTm n) : Γ ⊢[PRAAx] run p J K D ≐ count p J K D := by
  simpa [run,countF] using toPR_eq (Γ := Γ) (count (var 0) (var 1) (var 2) (var 3) : PTm 4) ![p,J,K,D]

theorem parameter_lower (h D : PTm n) (hs : Γ ⊢[PRAAx] separated h D) : Γ ⊢[PRAAx] lower (ofGaussian h D) D :=
  GaussianRationalLowerBounds.lower_from_representation _ _ D one D hs.andE₁ hs.andE₁
    (GaussianRationalHorner.ofGaussian_represents h D hs.andE₁)
    (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (D*D) hs.andE₂))

theorem parameter_inverse_bound (h D : PTm n) (hs : Γ ⊢[PRAAx] separated h D) : Γ ⊢[PRAAx]
    bounded (reciprocal (ofGaussian h D)) D one := GaussianNameReciprocal.inverse_bound _ D hs.andE₁ (parameter_lower h D hs)

theorem count_positive (p J K D : PTm n) : Γ ⊢[PRAAx] le one (count p J K D) :=
  le_trans (le_add_right one J) (le_add_right _ _)
theorem log_budget (p J K D : PTm n) : Γ ⊢[PRAAx] le J (count p J K D) :=
  le_trans (le_add_left J one) (le_add_right _ _)
theorem quadratic_budget (p J K D : PTm n) : Γ ⊢[PRAAx] le (K*D*unit (p+num 6)) (count p J K D) := le_add_left _ _

theorem later_positive (p J K D N : PTm n) (hN : Γ ⊢[PRAAx] le (count p J K D) N) : Γ ⊢[PRAAx] le one N :=
  le_trans (count_positive p J K D) hN

theorem unit_log_guard (p J K D N X Y : PTm n) (hN : Γ ⊢[PRAAx] le (count p J K D) N)
    (hXY : Γ ⊢[PRAAx] le X Y) : Γ ⊢[PRAAx] le (J*X) (Y*N) :=
  le_congr (.eqRefl _) (mul_comm _ _) (AnalyticNumberTheory.PhiLower.le_mul_mono (le_trans (log_budget p J K D) hN) hXY)

/-- Exact cleared comparison K*X²/(Y²*N)<=1/(D*2^(p+6)). -/
theorem accumulated_quadratic_budget (p J K D N X Y : PTm n)
    (hN : Γ ⊢[PRAAx] le (count p J K D) N) (hXY : Γ ⊢[PRAAx] le X Y) : Γ ⊢[PRAAx]
    le ((K*X*X)*(D*unit (p+num 6))) ((Y*Y)*N) := by
  have budget := le_trans (quadratic_budget p J K D) hN
  ipra_le (𝔞 X)^2*sl budget+𝔞 N*sl (sq_le_sq hXY)

theorem accumulated_quadratic_bound (q p J K D N X Y : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hY : Γ ⊢[PRAAx] le one Y)
    (hN : Γ ⊢[PRAAx] le (count p J K D) N) (hXY : Γ ⊢[PRAAx] le X Y)
    (hq : Γ ⊢[PRAAx] bounded q (K*X*X) ((Y*Y)*N)) : Γ ⊢[PRAAx]
    bounded q one (D*unit (p+num 6)) :=
  bounded_radius_mono _ _ _ _ _
    (positive_product _ _ (positive_product _ _ hY hY) (later_positive p J K D N hN))
    (positive_product _ _ hD (unit_positive _))
    (le_congr (.eqRefl _) (one_mul _).eqSymm (accumulated_quadratic_budget p J K D N X Y hN hXY)) hq

theorem normalize_error (q h p D : PTm n) (hs : Γ ⊢[PRAAx] separated h D)
    (hq : Γ ⊢[PRAAx] bounded q one (D*unit (p+num 6))) : Γ ⊢[PRAAx]
    bounded (qmul q (reciprocal (ofGaussian h D))) one (unit (p+num 6)) := by
  have actual := bounded_product _ _ one (D*unit (p+num 6)) D one
    (positive_product _ _ hs.andE₁ (unit_positive _)) (le_refl one)
    hq (parameter_inverse_bound h D hs)
  exact bounded_radius_mono _ _ _ _ _
    (positive_product _ _ (positive_product _ _ hs.andE₁ (unit_positive _)) (le_refl one)) (unit_positive _)
    (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by ipra_ring)) actual

theorem relative_quadratic_bound (q h p J K D N X Y : PTm n)
    (hs : Γ ⊢[PRAAx] separated h D) (hY : Γ ⊢[PRAAx] le one Y)
    (hN : Γ ⊢[PRAAx] le (count p J K D) N) (hXY : Γ ⊢[PRAAx] le X Y)
    (hq : Γ ⊢[PRAAx] bounded q (K*X*X) ((Y*Y)*N)) : Γ ⊢[PRAAx]
    bounded (qmul q (reciprocal (ofGaussian h D))) one (unit (p+num 6)) :=
  normalize_error q h p D hs (accumulated_quadratic_bound q p J K D N X Y hs.andE₁ hY hN hXY hq)

theorem tail_query_budget (p D s : PTm n) (hs : Γ ⊢[PRAAx] le (tailQuery p D) s) : Γ ⊢[PRAAx]
    le (D*unit (p+num 6)) (unit s) :=
  le_trans (GaussianFastValueCut.query_budget D (p+num 6)) (GaussianExponentialReference.unit_monotone hs)

theorem observation_query_budget (p N C D s : PTm n) (hs : Γ ⊢[PRAAx] le (readQuery p N C D) s) : Γ ⊢[PRAAx]
    le ((C*N)*(D*unit (p+num 6))) (unit s) :=
  le_congr (by ipra_ring) (.eqRefl _)
    (le_trans (GaussianFastValueCut.query_budget (C*N*D) (p+num 6)) (GaussianExponentialReference.unit_monotone hs))

theorem relative_tail_error (q h p D s : PTm n) (hs : Γ ⊢[PRAAx] separated h D)
    (hRead : Γ ⊢[PRAAx] le (tailQuery p D) s) (hq : Γ ⊢[PRAAx] bounded q one (unit s)) : Γ ⊢[PRAAx]
    bounded (qmul q (reciprocal (ofGaussian h D))) one (unit (p+num 6)) :=
  normalize_error q h p D hs (bounded_radius_mono _ _ _ _ _ (unit_positive s)
    (positive_product _ _ hs.andE₁ (unit_positive _))
    (le_congr (by ipra_ring) (by ipra_ring) (tail_query_budget p D s hRead)) hq)

theorem relative_observation_error (q h p N C D s : PTm n) (hs : Γ ⊢[PRAAx] separated h D)
    (hRead : Γ ⊢[PRAAx] le (readQuery p N C D) s) (hq : Γ ⊢[PRAAx] bounded q (C*N) (unit s)) : Γ ⊢[PRAAx]
    bounded (qmul q (reciprocal (ofGaussian h D))) one (unit (p+num 6)) :=
  normalize_error q h p D hs (bounded_radius_mono _ _ _ _ _ (unit_positive s)
    (positive_product _ _ hs.andE₁ (unit_positive _))
    (le_congr (.eqRefl _) (one_mul _).eqSymm (observation_query_budget p N C D s hRead)) hq)

theorem compact_unit_log_guard (p j R E T D N X Y : PTm n)
    (hN : Γ ⊢[PRAAx] le (compactCount p j R E T D) N) (hXY : Γ ⊢[PRAAx] le X Y) : Γ ⊢[PRAAx]
    le (GaussianEulerLogarithmicMultiplier.logRadius E T*X) (Y*N) :=
  unit_log_guard p _ _ D N X Y hN hXY

/-- The literal interval weight C/E is retained before spending its actual
guard C<=E*T. No compact curvature is declared independent of cutoffs. -/
theorem compact_quadratic_budget (p j R C E T D N X Y : PTm n)
    (hN : Γ ⊢[PRAAx] le (compactCount p j R E T D) N) (hXY : Γ ⊢[PRAAx] le X Y)
    (hC : Γ ⊢[PRAAx] le C (E*T)) : Γ ⊢[PRAAx]
    le ((C*GaussianEulerLogarithmicParameterIncrement.curvature j R E T*X*X)*(D*unit (p+num 6)))
      (E*((Y*Y)*N)) := by
  have main := accumulated_quadratic_budget p _ (T*GaussianEulerLogarithmicParameterIncrement.curvature j R E T) D N X Y hN hXY
  have width := mul_le_mul_right (GaussianEulerLogarithmicParameterIncrement.curvature j R E T*X*X*D*unit (p+num 6)) hC
  have first : Γ ⊢[PRAAx]
      le ((C*GaussianEulerLogarithmicParameterIncrement.curvature j R E T*X*X)*(D*unit (p+num 6)))
        (E*((T*GaussianEulerLogarithmicParameterIncrement.curvature j R E T*X*X)*(D*unit (p+num 6)))) :=
    le_congr (by ipra_ring) (by ipra_ring) width
  exact le_trans first (le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right E main))

theorem actual_encoded_nonzero_parameter_lower_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (separated (var 0) (var 1) ⟶ lower (ofGaussian (var 0) (var 1)) (var 1)) :=
  closeUniv 2 (.impI (parameter_lower _ _ Prf.hyp0))

theorem actual_PR_derivative_subdivision_counter_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ count (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (program_at _ _ _ _)

theorem actual_later_subdivision_arithmetic_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((le (count (var 0) (var 1) (var 2) (var 3)) (var 4) ⋏ le (var 5) (var 6)) ⟶
      (le (var 1*var 5) (var 6*var 4) ⋏
       le ((var 2*var 5*var 5)*(var 3*unit (var 0+num 6))) ((var 6*var 6)*var 4))) :=
  closeUniv 7 (.impI (.andI (unit_log_guard _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)
    (accumulated_quadratic_budget _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

theorem actual_normalized_quadratic_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    ((separated (var 1) (var 5) ⋏ (le one (var 8) ⋏
      (le (count (var 2) (var 3) (var 4) (var 5)) (var 6) ⋏ (le (var 7) (var 8) ⋏
        bounded (var 0) (var 4*var 7*var 7) ((var 8*var 8)*var 6))))) ⟶
      bounded (qmul (var 0) (reciprocal (ofGaussian (var 1) (var 5)))) one (unit (var 2+num 6))) :=
  closeUniv 9 (.impI (relative_quadratic_bound _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerDerivativeSubdivisionBudget
