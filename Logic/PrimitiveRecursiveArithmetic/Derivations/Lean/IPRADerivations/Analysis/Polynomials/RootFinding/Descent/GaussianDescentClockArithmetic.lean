import IPRADerivations.Analysis.FiniteOperations.GaussianProductStability
import IPRADerivations.Analysis.RationalArithmetic.RationalClosure

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

/-- The first two finite binomial terms, proved directly by QF induction. -/
theorem bernoulli (a k : PTm n) : Γ ⊢[PRAAx]
    le (pw a k*(a+succ k)) (pw (succ a) (succ k)) := by
  have all : Γ ⊢[PRAAx] .all (le (pw (Syn.shift a) (var 0)*(Syn.shift a+succ (var 0)))
      (pw (succ (Syn.shift a)) (succ (var 0)))) := by
    ipra_qfind (le_QF _ _) [subst_le, subst_ap2]
    · exact le_congr ((congrMul (pw_zero a) (.eqRefl _)).eqTrans (one_mul _)).eqSymm
        (pw_one (succ a)).eqSymm (le_of_eq_add (d := zero) (by ipra_ring))
    · let Δ := le (pw (Syn.shift a) (var 0)*(Syn.shift a+succ (var 0)))
        (pw (succ (Syn.shift a)) (succ (var 0))) :: Γ.map Fm.shift
      have step : Δ ⊢[PRAAx] le
          (pw (Syn.shift a) (succ (var 0))*(Syn.shift a+succ (succ (var 0))))
          ((pw (Syn.shift a) (var 0)*(Syn.shift a+succ (var 0)))*succ (Syn.shift a)) := by
        refine le_of_eq_add (d := pw (Syn.shift a) (var 0)*succ (var 0)) ?_
        have p := natEq (pw_succ (Γ := (le (pw (Syn.shift a) (var 0)*(Syn.shift a+succ (var 0)))
          (pw (succ (Syn.shift a)) (succ (var 0)))) :: Γ.map Fm.shift) (Syn.shift a) (var 0))
        apply deriveNat; ipra_simps; rw [p]; ring
      exact le_trans step (le_congr (.eqRefl _) (pw_succ _ _).eqSymm (mul_le_mul_right _ Prf.hyp0))
  simpa only [subst_le,PTm.subst_mul,PTm.subst_add,subst_ap2,ConciseIPRA.PTm.subst_succ,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE k all

/-- q^M≤1/2 for q=(M−1)/M, including M=1. -/
theorem block_decay (M : PTm n) (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx]
    le (two*pw (pred M) M) (pw M M) := by
  have m := positive_form hM
  have first : Γ ⊢[PRAAx] le (two*pw (pred M) M)
      (pw (pred M) (pred M)*(pred M+succ (pred M))) := by
    refine le_of_eq_add (d := pw (pred M) (pred M)) ?_
    have p := natEq ((congrAp2 powF m (.eqRefl (pred M))).eqTrans (pw_succ _ _))
    apply deriveNat; ipra_simps; rw [p]; ring
  have second := bernoulli (Γ := Γ) (pred M) (pred M)
  exact le_trans first (le_congr (.eqRefl _)
    (congrAp2 powF m.eqSymm m.eqSymm) second)

theorem power_composition (a M K : PTm n) : Γ ⊢[PRAAx] pw (pw a M) K ≐ pw a (M*K) := by
  have all : Γ ⊢[PRAAx] .all (pw (pw (Syn.shift a) (Syn.shift M)) (var 0) ≐
      pw (Syn.shift a) (Syn.shift M*var 0)) := by
    ipra_qfind [subst_ap2]
    · exact (pw_zero _).eqTrans ((congrAp2 powF (mul_zero M) (.eqRefl _)).eqTrans (pw_zero _)).eqSymm
    · exact (pw_succ _ _).eqTrans ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans
        ((pw_add _ _ _).eqSymm.eqTrans (congrAp2 powF (by ipra_ring) (.eqRefl _))))
  simpa only [Fm.subst_eq,PTm.subst_mul,subst_ap2,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE K all

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
  le_of_eq_add (Prf.andE₁ (div_mod_at (x := s+pred t) (positive_form ht)))

theorem ceiling_least (s t k : PTm n) (ht : Γ ⊢[PRAAx] le one t) (h : Γ ⊢[PRAAx] le s (t*k)) :
    Γ ⊢[PRAAx] le (ceiling s t) k := by
  refine .orE (lt_or_le k (ceiling s t)) ?_ Prf.hyp0
  refine succ_ne_zero' _ (a := monus (t*k) s+t*monus (ceiling s t) (succ k)+monus (s+pred t) (t*ceiling s t)) ?_
  ipra_lc -natEq (eq_add_of_le ((ceiling_upper (Γ := Γ) s t ht).wk (ψ := lt k (ceiling s t))))-
    Groth.ι (Q.mk (lt k (ceiling s t) :: Γ) t)*natEq (eq_add_of_le (Prf.hyp0 (Ax := PRAAx) (Γ := Γ) (φ := lt k (ceiling s t))))-
    natEq (eq_add_of_le (h.wk (ψ := lt k (ceiling s t))))-natEq (positive_form (ht.wk (ψ := lt k (ceiling s t))))

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
