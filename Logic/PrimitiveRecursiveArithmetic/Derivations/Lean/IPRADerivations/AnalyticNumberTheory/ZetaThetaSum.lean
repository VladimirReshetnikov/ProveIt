import IPRADerivations.AnalyticNumberTheory.ZetaPrecision

/-!
# The theta majorant sums to at most one (`zeta_functional_equation_ipra`)

Packet: `analytic-number-theory/zeta_functional_equation_ipra`, `finite_contract.md`: "The finite sum `psi_N`
satisfies `psi_N ≤ 1` and `|psi_N'| ≤ 1`. Indeed, `4n²2^{−3n²} ≤ 2^{−n}`, because `n² ≤ 4^{n−1}` and `n² ≥ n`.
Summing the last bound gives 1."

The majorant partial sums `Σ_{n=1}^{k} 4n² 2^{−3n²}` are kept over their common denominator `2^{3k²}`:
`S_k = Σ_{n<k} 4(n+1)² 2^{3k² − 3(n+1)²}`, computed by one recursion (`Sk`, `S_zero`, `S_succ`)

  `S_0 = 0`,  `S_{k+1} = 2^{6k+3} S_k + 4(k+1)²`   (as `3(k+1)² = 3k² + 6k + 3`).

* `theta_sum`: `2^k S_k + 2^{3k²} ≤ 2^{3k²} 2^k`, i.e. `Σ_{n=1}^{k} 4n² 2^{−3n²} ≤ 1 − 2^{−k}` — one QF induction
  whose step is `ZetaFiniteContract.theta_term` (`4n² 2^n ≤ 2^{3n²}`) at `n = k + 1`;
* `theta_sum_le_one`: `S_k ≤ 2^{3k²}`, i.e. the majorant sum is at most `1` for every `k`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.ZetaThetaSum

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.ZetaFiniteContract (theta_term)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The step over `0 = k`, `1 = S_k`: `2^{6k+3} S_k + 4(k+1)²`. -/
def stepS : PTm 3 := var 1 * pw two (num 6 * var 0 + num 3) + num 4 * (succ (var 0) * succ (var 0))

/-- `S_k = Σ_{n<k} 4(n+1)² 2^{3k² − 3(n+1)²}`. -/
def Sk (k : PTm n) : PTm n := ap2 (rec2 zero stepS) k zero

ipra_subst Sk

theorem S_zero : Γ ⊢[PRAAx] Sk (zero : PTm n) ≐ zero := by
  unfold Sk; simpa using rec2_zero (Γ := Γ) (zero : PTm 1) stepS (zero : PTm n)

theorem S_succ (k : PTm n) :
    Γ ⊢[PRAAx] Sk (succ k) ≐ Sk k * pw two (num 6 * k + num 3) + num 4 * (succ k * succ k) := by
  unfold Sk; simpa [stepS] using rec2_succ (Γ := Γ) (zero : PTm 1) stepS k (zero : PTm n)

/-- The invariant `2^k S_k + 2^{3k²} ≤ 2^{3k²} 2^k`. -/
def thInv (k : PTm n) : Fm PTm n :=
  le (pw two k * Sk k + pw two (num 3 * (k * k))) (pw two (num 3 * (k * k)) * pw two k)

ipra_subst thInv [subst_ap2]

/-- `Σ_{n=1}^{k} 4n² 2^{−3n²} ≤ 1 − 2^{−k}`, cleared over `2^{3k²}`. -/
theorem theta_sum (k : PTm n) :
    Γ ⊢[PRAAx] le (pw two k * Sk k + pw two (num 3 * (k * k))) (pw two (num 3 * (k * k)) * pw two k) := by
  have hall : Γ ⊢[PRAAx] Fm.all (thInv (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · rw [subst_thInv]
      simp only [Syn.subst_var, Syn.inst_zero]
      have e0 := natEq (S_zero (Γ := Γ) (n := n))
      have z : Γ ⊢[PRAAx] pw two (num 3 * (zero * zero)) ≐ one :=
        (congrPw2 (show Γ ⊢[PRAAx] num 3 * (zero * zero) ≐ (zero : PTm n) by ipra_ring)).eqTrans
          (pw_zero _)
      have e1 := natEq z
      have e2 := natEq (pw_zero (Γ := Γ) (two : PTm n))
      show Γ ⊢[PRAAx] le (pw two zero * Sk zero + pw two (num 3 * (zero * zero)))
        (pw two (num 3 * (zero * zero)) * pw two zero)
      ipra_le 0 with 𝔞 (pw two zero) * e1 - 𝔞 (pw two zero) * e0 + e2 - e1
    · rw [subst_thInv]
      simp only [Syn.subst_var, Syn.repl_zero]
      let Δ : List (Fm PTm (n + 1)) := thInv (var 0) :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] le (pw two (var 0) * Sk (var 0) + pw two (num 3 * (var 0 * var 0)))
          (pw two (num 3 * (var 0 * var 0)) * pw two (var 0)) := Prf.hyp0
      have th := theta_term (Γ := Δ) (var 0)
      have eS := natEq (S_succ (Γ := Δ) (var 0))
      have eP := natEq (pw_succ (Γ := Δ) two (var 0))
      have eE := natEq ((congrPw2 (Γ := Δ) (show Δ ⊢[PRAAx] num 3 * (succ (var 0) * succ (var 0)) ≐
          num 3 * (var 0 * var 0) + (num 6 * var 0 + num 3) by ipra_ring)).eqTrans
        (pw_add (Γ := Δ) two (num 3 * (var 0 * var 0)) (num 6 * var 0 + num 3)))
      show Δ ⊢[PRAAx] le (pw two (succ (var 0)) * Sk (succ (var 0)) + pw two (num 3 * (succ (var 0) * succ (var 0))))
        (pw two (num 3 * (succ (var 0) * succ (var 0))) * pw two (succ (var 0)))
      ipra_le 2 * 𝔞 (pw two (num 6 * var 0 + num 3)) * sl ih + sl th with
        (𝔞 (pw two (num 3 * (succ (var 0) * succ (var 0)))) -
            𝔞 (Sk (var 0)) * 𝔞 (pw two (num 6 * var 0 + num 3))) * eP -
          𝔞 (pw two (succ (var 0))) * eS + (2 * 𝔞 (pw two (var 0)) - 2) * eE
  have h := Prf.allE k hall
  rw [subst_thInv] at h
  simp only [Syn.subst_var, Syn.inst_zero] at h
  exact h

/-- The theta majorant sums to at most `1`: `S_k ≤ 2^{3k²}`. -/
theorem theta_sum_le_one (k : PTm n) : Γ ⊢[PRAAx] le (Sk k) (pw two (num 3 * (k * k))) := by
  have t := theta_sum (Γ := Γ) k
  have pos := DiophantineNumberTheory.FLTMultiples.pw_pos (Γ := Γ) one k
  have hP : Γ ⊢[PRAAx] le (pw two k * Sk k) (pw two k * pw two (num 3 * (k * k))) := by
    ipra_le sl t + 𝔞 (pw two (num 3 * (k * k)))
  exact mul_le_cancel (le_congr (congrMul pos (.eqRefl _)) (congrMul pos (.eqRefl _)) hP)

end LeanProofs.IPRA.AnalyticNumberTheory.ZetaThetaSum
