import IPRADerivations.AnalyticNumberTheory.BrunElementary
import IPRADerivations.AnalyticNumberTheory.LocalFactor
import IPRADerivations.AnalyticNumberTheory.RSA
import IPRADerivations.AnalyticNumberTheory.SumReindex
import IPRADerivations.Analysis.Polynomials.RootFinding.Deflation.FactorTransport.GaussianFactorBudget

/-!
# Constructive upper order threshold for Barnes growth

The radius exponent in the dyadic Barnes bound is a quadratic times
a linear function of the dyadic index. A primitive-recursive threshold
makes the linear factor at most the prescribed positive rational extra
power of the radius. All the comparisons use integer powers.
-/

set_option autoImplicit false
set_option maxHeartbeats 550000

namespace LeanProofs.IPRA.Analysis.BarnesUpperOrderThreshold

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.BrunElementary (sq_le_pow)
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)
open LeanProofs.IPRA.Common (pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (pw_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.SumReindex (le_quo_of_mul_le)
open GaussianFactorBudget (power_monotone_length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def threshold (C b : PTm n) : PTm n := (two*b)*((two*b)*C)

private theorem floor_bounds (j d : PTm n) (hd : Γ ⊢[PRAAx] le one d) :
    Γ ⊢[PRAAx] le (d*quo j d) j ⋏ le (succ j) (d*succ (quo j d)) := by
  let t := quo j d
  have division := div_mod_at (Γ := Γ) (x := j) (pos_of_one_le hd)
  have rest : Γ ⊢[PRAAx] le (succ (rem j d)) d := division.andE₂
  refine .andI (le_congr (.eqRefl _) division.andE₁.eqSymm (le_add_right _ _)) ?_
  have upper := LeanProofs.IPRA.Common.add_le_add (le_refl (d*t)) rest
  exact le_congr ((congrSucc division.andE₁).eqTrans (by ipra_ring)).eqSymm (by ipra_ring) upper

theorem quotient_bound (C b j : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hj : Γ ⊢[PRAAx] le (threshold C b) j) :
    Γ ⊢[PRAAx] le (C*succ j) (pw two (quo j b)) := by
  let d := two*b
  let t := quo j d
  have twoPos := le_succ_self (Γ := Γ) one
  have hd : Γ ⊢[PRAAx] le one d :=
    le_trans hb (le_of_eq_add (d := b) (by dsimp only [d]; ipra_ring))
  have floor := floor_bounds j d hd
  have ht : Γ ⊢[PRAAx] le (d*C) t := le_quo_of_mul_le (pos_of_one_le hd) hj
  have hindex : Γ ⊢[PRAAx] le (two*t) (quo j b) :=
    le_quo_of_mul_le (pos_of_one_le hb) (le_congr (by dsimp only [d]; ipra_ring) (.eqRefl _) floor.andE₁)
  have linear := LeanProofs.IPRA.Common.mul_le_mul (le_refl C) floor.andE₂
  have square : Γ ⊢[PRAAx] le (C*(d*succ t)) (succ t*succ t) :=
    le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right (succ t) (le_trans ht (le_succ_self t)))
  exact le_trans linear (le_trans square (le_trans (sq_le_pow t) (power_monotone_length two _ _ twoPos hindex)))

theorem powered_bound (C b j : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hj : Γ ⊢[PRAAx] le (threshold C b) j) :
    Γ ⊢[PRAAx] le (pw (C*succ j) b) (pw two j) := by
  let k := quo j b
  have front := pw_le_pw b (quotient_bound C b j hb hj)
  have hk : Γ ⊢[PRAAx] le (k*b) j :=
    le_congr (mul_comm b k) (.eqRefl _) (floor_bounds j b hb).andE₁
  exact le_trans (le_congr (.eqRefl _) (pw_mul two k b) front)
    (power_monotone_length two _ _ (le_succ_self one) hk)

theorem exponent_bound (C b j : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hj : Γ ⊢[PRAAx] le (threshold C b) j) :
    let R := pw two j
    Γ ⊢[PRAAx] le (pw (C*succ j*(R*R)) b) (pw R (two*b+one)) := by
  let R := pw two j
  have square : Γ ⊢[PRAAx] pw (R*R) b ≐ pw R (two*b) :=
    (pw_mul_base R R b).eqTrans ((pw_add R b b).eqSymm.eqTrans
      (congrAp2 powF (by ipra_ring) (.eqRefl R)))
  have rhs : Γ ⊢[PRAAx] pw R (two*b+one) ≐ R*pw (R*R) b :=
    (pw_add R (two*b) one).eqTrans
      ((congrMul square.eqSymm (pw_one R)).eqTrans (mul_comm _ _))
  exact le_congr (pw_mul_base _ _ b).eqSymm rhs.eqSymm
    (LeanProofs.IPRA.Common.mul_le_mul (powered_bound C b j hb hj) (le_refl (pw (R*R) b)))

theorem actual_Barnes_upper_order_threshold_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (let C := var 0
       let b := var 1
       let j := var 2
       let R := pw two j
       le one b ⟶ le (threshold C b) j ⟶
         le (C*succ j) (pw two (quo j b)) ⋏
           le (pw (C*succ j*(R*R)) b) (pw R (two*b+one))) :=
  closeUniv 3 (.impI (.impI (.andI (quotient_bound _ _ _ Prf.hyp1 Prf.hyp0)
    (exponent_bound _ _ _ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.BarnesUpperOrderThreshold
