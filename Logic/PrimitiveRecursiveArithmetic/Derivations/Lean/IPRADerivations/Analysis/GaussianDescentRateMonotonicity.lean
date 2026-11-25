import IPRADerivations.Analysis.GaussianDescentClock
import IPRADerivations.Analysis.GaussianFactorBudget
import IPRADerivations.Analysis.RationalNonnegativePowers
import IPRADerivations.Core.CertificateTactics

/-!
# The actual rational descent rate is monotone in the numerical degree

Both factors of D_d=2^d*4^(2*d*d) are proved monotone from the actual
natural power programs. Positive a<=b gives (a-1)/a<=(b-1)/b by an exact
natural cross identity, and squaring yields the order of the literal
normalized clock fractions. Multiplication by an arbitrary original
Gaussian point's squared norm is legitimate because its nonnegativity is
derived from its actual positive-denominator representation. No residual,
canonical input, successful comparison, or rate-order law is assumed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianDescentRateMonotonicity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianDescentClockArithmetic (four descentD rateDenominator rate_positive)
open LeanProofs.IPRA.Analysis.GaussianDescentClock (contractionSquare)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction fraction_order)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qnormSq)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

theorem degree_exponent_monotone (d N : PTm n) (h : Γ ⊢[PRAAx] le d N) : Γ ⊢[PRAAx]
    le (two*d*d) (two*N*N) := le_mul_mono (le_mul_mono (le_refl two) h) h

theorem descentD_monotone (d N : PTm n) (h : Γ ⊢[PRAAx] le d N) : Γ ⊢[PRAAx] le (descentD d) (descentD N) :=
  le_mul_mono (GaussianFactorBudget.power_monotone_length two d N (le_succ_self one) h)
    (GaussianFactorBudget.power_monotone_length four (two*d*d) (two*N*N)
      GaussianDescentClockArithmetic.four_positive (degree_exponent_monotone d N h))

theorem rate_denominator_monotone (d N : PTm n) (h : Γ ⊢[PRAAx] le d N) : Γ ⊢[PRAAx]
    le (rateDenominator d) (rateDenominator N) :=
  le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right four (descentD_monotone d N h))

/-- The exact cross-product gap is b-a. No predecessor cancellation or
strict input order is used, including the boundary a=1. -/
theorem pred_ratio_identity (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hab : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx]
    pred b*a ≐ pred a*b+monus b a := by
  ipra_lc 𝔞(b)*natEq (RationalIntegerNormalization.positive_form ha)-
    𝔞(a)*natEq (RationalIntegerNormalization.positive_form (le_trans ha hab))+natEq (eq_add_of_le hab)

theorem pred_ratio_cross (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hab : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx]
    le (pred a*b) (pred b*a) := le_of_eq_add (pred_ratio_identity a b ha hab)

theorem pred_ratio_monotone (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hab : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx]
    rationalLE (fraction (pred a) a) (fraction (pred b) b) :=
  fraction_order _ _ _ _ ha (le_trans ha hab)
    (le_congr (mul_comm _ _) (.eqRefl _) (pred_ratio_cross a b ha hab))

theorem pred_square_ratio_monotone (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hab : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx]
    rationalLE (fraction (pred a*pred a) (a*a)) (fraction (pred b*pred b) (b*b)) :=
  fraction_order _ _ _ _ (positive_product a a ha ha)
    (positive_product b b (le_trans ha hab) (le_trans ha hab))
    (le_congr (by ipra_ring) (by ipra_ring) (sq_le_sq (pred_ratio_cross a b ha hab)))

/-- This is the actual normalized clock quantity, including degree zero. -/
theorem contraction_square_monotone (d N : PTm n) (h : Γ ⊢[PRAAx] le d N) : Γ ⊢[PRAAx]
    rationalLE (contractionSquare d) (contractionSquare N) :=
  pred_square_ratio_monotone (rateDenominator d) (rateDenominator N) (rate_positive d) (rate_denominator_monotone d N h)

theorem norm_numerator_nonnegative (v : PTm n) : Γ ⊢[PRAAx]
    le (RationalSupMetric.numeratorOf (qnormSq v)).neg (RationalSupMetric.numeratorOf (qnormSq v)).pos :=
  GaussianRationalL1.nonnegative_of_representation _ _ _
    (positive_product _ _ (raw_den_positive v) (raw_den_positive v))
    (GaussianRationalMetric.qnormSq_represents v (rawGaussian v) (rawDen v) (raw_den_positive v) (raw_represents v))

theorem norm_product_monotone (d N v : PTm n) (h : Γ ⊢[PRAAx] le d N) : Γ ⊢[PRAAx]
    rationalLE (RationalArithmetic.multiply (contractionSquare d) (qnormSq v))
      (RationalArithmetic.multiply (contractionSquare N) (qnormSq v)) :=
  RationalArgmin.rationalLE_congr (RationalAlgebra.multiply_commutative _ _) (RationalAlgebra.multiply_commutative _ _)
    (RationalArithmetic.multiply_monotone (qnormSq v) (contractionSquare d) (contractionSquare N)
      (norm_numerator_nonnegative v) (contraction_square_monotone d N h))

/-- A genuine lower-degree residual comparison weakens to the original
degree without any positive-residual or canonical-point hypothesis. -/
theorem weaken_contract (d N u v : PTm n) (hdN : Γ ⊢[PRAAx] le d N)
    (h : Γ ⊢[PRAAx] rationalLE (qnormSq u) (RationalArithmetic.multiply (contractionSquare d) (qnormSq v))) : Γ ⊢[PRAAx]
    rationalLE (qnormSq u) (RationalArithmetic.multiply (contractionSquare N) (qnormSq v)) :=
  RationalArgmin.transitive h (norm_product_monotone d N v hdN)

def output (d N : PTm n) : PTm n := pairT (descentD d) (pairT (descentD N) (pairT (contractionSquare d) (contractionSquare N)))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (d N : PTm n) : PTm n := ap2 outputF d N
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (d N : PTm n) :
    Syn.subst σ (output d N) = output (Syn.subst σ d) (Syn.subst σ N) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (d N : PTm n) :
    Syn.subst σ (run d N) = run (Syn.subst σ d) (Syn.subst σ N) := by simp [run]
theorem program_at (d N : PTm n) : Γ ⊢[PRAAx] run d N ≐ output d N := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![d,N]
theorem returned_lower_degree_bound (d N : PTm n) : Γ ⊢[PRAAx] fstT (run d N) ≐ descentD d :=
  (congrFst (program_at d N)).eqTrans (fst_pair _ _)
theorem returned_upper_degree_bound (d N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run d N)) ≐ descentD N :=
  (congrFst ((congrSnd (program_at d N)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_lower_rate (d N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run d N))) ≐ contractionSquare d :=
  (congrFst ((congrSnd ((congrSnd (program_at d N)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_upper_rate (d N : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run d N))) ≐ contractionSquare N :=
  (congrSnd ((congrSnd ((congrSnd (program_at d N)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_rate_order (d N : PTm n) (h : Γ ⊢[PRAAx] le d N) : Γ ⊢[PRAAx]
    rationalLE (fstT (sndT (sndT (run d N)))) (sndT (sndT (sndT (run d N)))) :=
  RationalArgmin.rationalLE_congr (returned_lower_rate d N).eqSymm (returned_upper_rate d N).eqSymm (contraction_square_monotone d N h)

theorem actual_descent_clock_monotone_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (var 0) (var 1) ⟶ (le (descentD (var 0)) (descentD (var 1)) ⋏
      (le (rateDenominator (var 0)) (rateDenominator (var 1)) ⋏ rationalLE (contractionSquare (var 0)) (contractionSquare (var 1))))) :=
  closeUniv 2 (.impI (.andI (descentD_monotone _ _ Prf.hyp0)
    (.andI (rate_denominator_monotone _ _ Prf.hyp0) (contraction_square_monotone _ _ Prf.hyp0))))
theorem positive_predecessor_ratio_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⟶ le (var 0) (var 1) ⟶ rationalLE (fraction (pred (var 0)) (var 0)) (fraction (pred (var 1)) (var 1))) :=
  closeUniv 2 (.impI (.impI (pred_ratio_monotone _ _ Prf.hyp1 Prf.hyp0)))
theorem residual_contract_weakening_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 0) (var 1) ⟶ rationalLE (qnormSq (var 2)) (RationalArithmetic.multiply (contractionSquare (var 0)) (qnormSq (var 3))) ⟶
      rationalLE (qnormSq (var 2)) (RationalArithmetic.multiply (contractionSquare (var 1)) (qnormSq (var 3)))) :=
  closeUniv 4 (.impI (.impI (weaken_contract _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem descent_rate_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ output (var 0) (var 1)) := closeUniv 2 (program_at _ _)
theorem returned_descent_rate_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (var 0) (var 1) ⟶ rationalLE (fstT (sndT (sndT (run (var 0) (var 1))))) (sndT (sndT (sndT (run (var 0) (var 1)))))) :=
  closeUniv 2 (.impI (returned_rate_order _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianDescentRateMonotonicity
