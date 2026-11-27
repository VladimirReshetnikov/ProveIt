import IPRADerivations.Analysis.FiniteOperations.FiniteProducts.GaussianProductStability
import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.RationalClosure

/-!
# Exact finite arithmetic of the rational-descent clock

Source04's approximate-root clock uses M=4·2^d·4^(2d²), contraction
(M−1)/M, K=ceil((a/b)/(e/f)) and J=M K. Bernoulli's finite inequality,
block decay, the actual integer ceiling, and the final rational budget are
proved with all exponents and inputs internal. No descent contract is used
in this arithmetic module.
-/

set_option linter.unusedSimpArgs false
set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianDescentClockArithmetic

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Analysis.RationalIntegerNormalization (positive_form)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def four : PTm n := two*two
def descentD (d : PTm n) : PTm n := pw two d*pw four (two*d*d)
def rateDenominator (d : PTm n) : PTm n := four*descentD d
def ceiling (s t : PTm n) : PTm n := quo (s+pred t) t
def blocks (a b e f : PTm n) : PTm n := ceiling (a*f) (b*e)
def clock (d a b e f : PTm n) : PTm n := rateDenominator d*blocks a b e f

ipra_subst four
ipra_subst descentD
ipra_subst rateDenominator
ipra_subst ceiling
ipra_subst blocks
ipra_subst clock

alias positive_product := Common.one_le_mul

theorem four_positive : Γ ⊢[PRAAx] le one (four : PTm n) :=
  positive_product two two (le_succ_self one) (le_succ_self one)

theorem rate_positive (d : PTm n) : Γ ⊢[PRAAx] le one (rateDenominator d) :=
  positive_product _ _ four_positive (positive_product _ _
    (GaussianPolynomialPerturbation.power_positive two d (le_succ_self one))
    (GaussianPolynomialPerturbation.power_positive four (two*d*d) four_positive))

/-- The first two finite binomial terms for an increment of one. -/
theorem bernoulli (a k : PTm n) : Γ ⊢[PRAAx]
    le (pw a k*(a+succ k)) (pw (succ a) (succ k)) := by
  refine le_congr ?_ (.eqRefl _) (pw_bernoulli_unit a k)
  have h := natEq (pw_succ (Γ := Γ) a k)
  apply deriveNat
  ipra_simps
  rw [h]
  ring

/-- q^M≤1/2 for q=(M−1)/M, including M=1. -/
theorem block_decay (M : PTm n) (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx]
    le (two*pw (pred M) M) (pw M M) := by
  have hm := positive_form hM
  exact le_congr (congrMul (.eqRefl _) (congrAp2 powF hm.eqSymm (.eqRefl _)))
    (congrAp2 powF hm.eqSymm hm.eqSymm) (pw_bernoulli_half (pred M))

theorem power_composition (a M K : PTm n) : Γ ⊢[PRAAx] pw (pw a M) K ≐ pw a (M*K) :=
  pw_pow a M K

theorem dyadic_decay (M K : PTm n) (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx]
    le (pw two K*pw (pred M) (M*K)) (pw M (M*K)) := by
  have h := pw_le_pw K (block_decay M hM)
  exact le_congr ((GaussianProductStability.power_product two (pw (pred M) M) K).eqTrans
    (congrMul (.eqRefl _) (power_composition _ _ _))) (power_composition _ _ _) h

/-- The actual quotient program rounds upward and is the least such integer. -/
theorem ceiling_lower (s t : PTm n) (ht : Γ ⊢[PRAAx] le one t) : Γ ⊢[PRAAx] le s (t*ceiling s t) := by
  have d := div_mod_at (x := s+pred t) (positive_form ht)
  have r : Γ ⊢[PRAAx] le (rem (s+pred t) t) (pred t) :=
    (succ_monus_succ _ _).eqSymm.eqTrans (lt_congr (.eqRefl _) (positive_form ht) (Prf.andE₂ d))
  refine le_of_eq_add (d := monus (pred t) (rem (s+pred t) t)) ?_
  unfold ceiling
  ipra_lc -natEq (Prf.andE₁ d)+natEq (eq_add_of_le r)

theorem ceiling_upper (s t : PTm n) (ht : Γ ⊢[PRAAx] le one t) :
    Γ ⊢[PRAAx] le (t*ceiling s t) (s+pred t) :=
  Division.mul_quo_le (positive_form ht)

theorem ceiling_least (s t k : PTm n) (ht : Γ ⊢[PRAAx] le one t) (h : Γ ⊢[PRAAx] le s (t*k)) :
    Γ ⊢[PRAAx] le (ceiling s t) k := by
  apply Order.le_of_lt_succ (Division.quo_lt_of_lt_mul (positive_form ht) ?_)
  change Γ ⊢[PRAAx] le (succ (s+pred t)) (t*succ k)
  have left := (congrAdd (.eqRefl s) (positive_form ht)).eqTrans (add_succ _ _)
  exact le_congr left (mul_succ t k).eqSymm (add_le_add_right t h)

theorem geometric_budget (a b e f : PTm n) (hb : Γ ⊢[PRAAx] le one b) (he : Γ ⊢[PRAAx] le one e) : Γ ⊢[PRAAx]
    le (a*f) (b*e*pw two (blocks a b e f)) :=
  le_trans (ceiling_lower (a*f) (b*e) (positive_product b e hb he))
    (le_congr (mul_comm _ _) (mul_comm _ _)
      (mul_le_mul_right (b*e) (le_trans (le_succ_self _) (RationalClosure.succ_le_two_pow _))))

/-- The clock's exact rational budget: ((M−1)/M)^J·(a/b)≤e/f. -/
theorem clock_budget (d a b e f : PTm n) (hb : Γ ⊢[PRAAx] le one b) (he : Γ ⊢[PRAAx] le one e) : Γ ⊢[PRAAx]
    le (pw (pred (rateDenominator d)) (clock d a b e f)*a*f)
      (pw (rateDenominator d) (clock d a b e f)*b*e) := by
  unfold clock
  have g := mul_le_mul_right (pw (pred (rateDenominator d)) (clock d a b e f)) (geometric_budget a b e f hb he)
  have r := mul_le_mul_right (b*e) (dyadic_decay (Γ := Γ) (rateDenominator d) (blocks a b e f) (rate_positive d))
  change Γ ⊢[PRAAx] le ((a*f)*pw (pred (rateDenominator d)) (rateDenominator d*blocks a b e f))
    ((b*e*pw two (blocks a b e f))*pw (pred (rateDenominator d)) (rateDenominator d*blocks a b e f)) at g
  exact le_trans (le_congr (by ipra_ring) (by ipra_ring) g)
    (le_congr (.eqRefl _) (by ipra_ring) r)

def clockF : PR 5 := PTm.toPR (clock (var 0) (var 1) (var 2) (var 3) (var 4))
theorem clock_program (d a b e f : PTm n) : Γ ⊢[PRAAx]
    ConciseIPRA.PTm.app clockF ![d,a,b,e,f] ≐ clock d a b e f := by
  simpa [clockF] using toPR_eq (Γ := Γ) (clock (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![d,a,b,e,f]

theorem finite_bernoulli_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (pw (var 0) (var 1)*(var 0+succ (var 1))) (pw (succ (var 0)) (succ (var 1)))) :=
  closeUniv 2 (bernoulli _ _)
theorem ceiling_correct_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶
      (le (var 0) (var 1*ceiling (var 0) (var 1)) ⋏
        (le (var 1*ceiling (var 0) (var 1)) (var 0+pred (var 1)) ⋏
          (le (var 0) (var 1*var 2) ⟶ le (ceiling (var 0) (var 1)) (var 2))))) :=
  closeUniv 3 (.impI (.andI (ceiling_lower _ _ Prf.hyp0)
    (.andI (ceiling_upper _ _ Prf.hyp0) (.impI (ceiling_least _ _ _ Prf.hyp1 Prf.hyp0)))))
theorem block_decay_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (var 0) ⟶ le (two*pw (pred (var 0)) (var 0)) (pw (var 0) (var 0))) :=
  closeUniv 1 (.impI (block_decay _ Prf.hyp0))
theorem dyadic_decay_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⟶ le (pw two (var 1)*pw (pred (var 0)) (var 0*var 1)) (pw (var 0) (var 0*var 1))) :=
  closeUniv 2 (.impI (dyadic_decay _ _ Prf.hyp0))
theorem clock_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 2) ⟶ le one (var 3) ⟶
      le (pw (pred (rateDenominator (var 0))) (clock (var 0) (var 1) (var 2) (var 3) (var 4))*var 1*var 4)
        (pw (rateDenominator (var 0)) (clock (var 0) (var 1) (var 2) (var 3) (var 4))*var 2*var 3)) :=
  closeUniv 5 (.impI (.impI (clock_budget _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem clock_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (ConciseIPRA.PTm.app clockF ![var 0,var 1,var 2,var 3,var 4] ≐ clock (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (clock_program _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianDescentClockArithmetic
