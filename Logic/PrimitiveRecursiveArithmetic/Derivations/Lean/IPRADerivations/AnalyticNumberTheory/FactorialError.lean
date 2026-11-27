import IPRADerivations.AnalyticNumberTheory.ErrorEquation

/-!
# The error equation in factorial form (`pnt_ipra_constructive_2026-11-14`, `sb:error-equation`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, Lemma `sb:error-equation`. In the
weighted identity (`sb:weighted-sum`) the error `E_R(m)` is needed at every integer `m = ⌊x/n⌋`, so it is restated
without the factorial denominators of `ErrorEquation`. Splitting `R = ψ − id`, the identity-part is
`Σ_{j≤m} Λ(j) ⌊m/j⌋ = L_w(m!)` (`FactorialLambda.factorial_lambda`), and

  `|ψ(m) u_m + Σ_{d≤m} Λ(d) ψ(⌊m/d⌋) − F m u_m − F Σ_{j≤m} Λ(j) ⌊m/j⌋| ≤ 4096 F² m`

(`ferr_upper`, `ferr_lower`). The ingredients:

* `lfact_zero`, `pf_zero`/`pf_step`, `lfact_P`: `L_w(m!) + m S(K) ≤ Σ_{k<m} S(K(k+1))` (closed QF induction with
  `HarmonicChebyshev.harmonic_lw`), hence `lfact_upper`: `L_w(m!) + mF ≤ m u_m + S(m, F)`;
* `S_le`: `S(m, F) ≤ mF`;
* `HarmonicMertensLower.fact_lower`: `m u_m ≤ L_w(m!) + mF + m² ⌊F/K⌋`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.FactorialError

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB inst2_h)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (S_mono wt harmonic_lw)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertensLower (fact_lower)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSquareSum (U)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSum (P P_succ Hl log_sum)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt (Lam Lw)
open LeanProofs.IPRA.AnalyticNumberTheory.ErrorEquation (T2 cheb_upper cheb_lower hKx' hxx' eU')
open LeanProofs.IPRA.AnalyticNumberTheory.FourthRootSum (Q4)
open LeanProofs.IPRA.Analysis.Products (fact)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## `L_w(m!)` against `Σ u_k` -/

theorem lfact_zero (y : PTm n) : Γ ⊢[PRAAx] Lw wt (fact zero) y ≐ zero := by
  refine (factorial_lambda wt zero y).eqTrans ((sum_succ' _ _ _).eqTrans ((congrAdd (sum_zero _ _)
    (FL_at wt _ _ _)).eqTrans ((congrAdd (.eqRefl _) (zero_mul_l (lam_zero wt _) _)).eqTrans (add_zero _))))

/-- `L_w(k!) + k S(K) ≤ Σ_{j<k} S(K(j+1))`. -/
abbrev Pf (k K L : PTm n) : Fm PTm n :=
  le (Lw wt (fact k) (pairT K (fact L)) + k * S K (fact L)) (P k K (fact L))

theorem pf_zero (K L : PTm n) : Γ ⊢[PRAAx] Pf zero K L := by
  have l0 := natEq (lfact_zero (Γ := Γ) (pairT K (fact L)))
  have p0 := natEq (sum_zero (Γ := Γ) HarmonicLogSum.PB (pairT K (fact L)))
  ipra_le 0 with p0 - l0

theorem pf_step {k K L N0 : PTm n} (h : Γ ⊢[PRAAx] Hl (succ k) K L N0) (ih : Γ ⊢[PRAAx] Pf k K L) :
    Γ ⊢[PRAAx] Pf (succ k) K L := by
  have hK := Prf.andE₁ h
  have hL := Prf.andE₁ (Prf.andE₂ h)
  have hk := Prf.andE₂ (Prf.andE₂ h)
  have hs : Γ ⊢[PRAAx] succ k ≐ succ (pred (succ k)) := congrSucc (pred_succ _).eqSymm
  have hl := harmonic_lw (lt_zero_of_pos hs) hK (le_trans (le_scale K hk) hL)
  have lf : Γ ⊢[PRAAx] Lw wt (fact (succ k)) (pairT K (fact L)) ≐
      Lw wt (fact k) (pairT K (fact L)) + Lw wt (succ k) (pairT K (fact L)) :=
    (congrLw (w := wt) _ (fact_succ k zero)).eqTrans (lw_mul (w := wt) (Primes.fact_pos k) hs)
  have ef := natEq lf
  have ep := natEq (P_succ (Γ := Γ) k K (fact L))
  ipra_le sl ih + sl hl with ep - ef

/-- Variables: `0 = k`, `1 = K`, `2 = L`, `3 = N`. -/
private abbrev pfF : Fm PTm 4 := Hl (var 0) (var 1) (var 2) (var 3) ⟶ Pf (var 0) (var 1) (var 2)

private theorem pf₀ : ([] : List (Fm PTm 4)) ⊢[PRAAx] pfF := by
  ipra_ind (⟨⟨le_QF _ _, le_QF _ _, le_QF _ _⟩, le_QF _ _⟩) [subst_le, subst_ap2, subst_ap1, subst_pairT]
  · exact .impI (pf_zero _ _)
  · refine .impI ?_
    have h := (Prf.hyp0 : (Hl (succ (var 0)) (var 1) (var 2) (var 3) :: [pfF]) ⊢[PRAAx]
      Hl (succ (var 0)) (var 1) (var 2) (var 3))
    have h' : (Hl (succ (var 0)) (var 1) (var 2) (var 3) :: [pfF]) ⊢[PRAAx] Hl (var 0) (var 1) (var 2) (var 3) :=
      .andI (Prf.andE₁ h) (.andI (Prf.andE₁ (Prf.andE₂ h)) (le_trans (le_succ_self _) (Prf.andE₂ (Prf.andE₂ h))))
    exact pf_step h (Prf.impE Prf.hyp1 h')

theorem lfact_P {m K L : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hL : Γ ⊢[PRAAx] le (K * m) L) :
    Γ ⊢[PRAAx] Pf m K L := by
  have i := inst (Γ := Γ) pf₀ (![m, K, L, m] : Fin 4 → PTm n)
  simp at i
  exact Prf.impE i (.andI hK (.andI hL (le_refl m)))

/-- `L_w(m!) + mF ≤ m u_m + S(m, F)`. -/
theorem lfact_upper {m K L : PTm n} (hm : Γ ⊢[PRAAx] le one m) (hK : Γ ⊢[PRAAx] le one K)
    (hL : Γ ⊢[PRAAx] le (K * m) L) :
    Γ ⊢[PRAAx] le (Lw wt (fact m) (pairT K (fact L)) + m * fact L) (m * U m K (fact L) + S m (fact L)) := by
  have p := lfact_P hK hL
  have ls := Prf.andE₂ (log_sum hK hL)
  have e := natEq (eU' (K := K) (L := L) hm)
  ipra_le sl p + sl ls with 𝔞 m * e

/-- `S(m, F) ≤ mF`. -/
theorem S_le (m F : PTm n) : Γ ⊢[PRAAx] le (S m F) (m * F) :=
  sum_le_const hB (.allI (.impI (by rw [inst2_h]; exact quo_le_self _ _)))

/-! ## The factorial error equation -/

/-- `Σ_{j≤m} Λ(j) ⌊m/j⌋`. -/
abbrev Lq (m K L : PTm n) : PTm n := ap2 (sumF (FLB wt)) (succ m) (pairT m (pairT K (fact L)))

section Err
variable {x K L : PTm n} (hx : Γ ⊢[PRAAx] le one x) (hK : Γ ⊢[PRAAx] le one K) (hx4 : Γ ⊢[PRAAx] le (Q4 x) K)
  (hL : Γ ⊢[PRAAx] le (K * Q4 x) L) (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * x))) L)
include hx hK hx4 hL hP

/-- `ψ(x) u_x + Σ_d Λ(d) ψ(⌊x/d⌋) ≤ F x u_x + F Σ_j Λ(j) ⌊x/j⌋ + 4096 F² x`. -/
theorem ferr_upper :
    Γ ⊢[PRAAx] le (Psi wt x (pairT K (fact L)) * U x K (fact L) + T2 x K L)
      (fact L * (x * U x K (fact L)) + fact L * Lq x K L + num 4096 * (fact L * fact L * x)) := by
  have cu := cheb_upper hx hK hx4 hL hP
  have fl := le_scale (fact L) (fact_lower hK (hKx' hL))
  have fe := natEq (factorial_lambda (Γ := Γ) wt x (pairT K (fact L)))
  have eu := natEq (eU' (K := K) (L := L) (Γ := Γ) hx)
  have q1 := mul_le_mul_right (quo (fact L) K) (hxx' hx4)
  have q2 := quo_mul_le (Γ := Γ) (x := fact L) (pos_of_lt_zero hK)
  have fq := le_scale (fact L) (le_trans q1 (le_congr (mul_comm _ _) (.eqRefl _) q2))
  have fx := le_scale (fact L * fact L) hx
  ipra_le sl cu + sl fl + sl fq + sl fx + 1886 * (𝔞 (fact L) * 𝔞 (fact L) * 𝔞 x) with
    𝔞 (fact L) * 𝔞 x * eu - 𝔞 (fact L) * fe

/-- `F x u_x + F Σ_j Λ(j) ⌊x/j⌋ ≤ ψ(x) u_x + Σ_d Λ(d) ψ(⌊x/d⌋) + 4096 F² x`. -/
theorem ferr_lower :
    Γ ⊢[PRAAx] le (fact L * (x * U x K (fact L)) + fact L * Lq x K L)
      (Psi wt x (pairT K (fact L)) * U x K (fact L) + T2 x K L + num 4096 * (fact L * fact L * x)) := by
  have cl := cheb_lower hx hK hx4 hL hP
  have lu := le_scale (fact L) (lfact_upper hx hK (hKx' hL))
  have sx := le_scale (fact L) (S_le (Γ := Γ) x (fact L))
  have fe := natEq (factorial_lambda (Γ := Γ) wt x (pairT K (fact L)))
  ipra_le sl cl + sl lu + sl sx + 1892 * (𝔞 (fact L) * 𝔞 (fact L) * 𝔞 x) with 𝔞 (fact L) * fe

end Err

end LeanProofs.IPRA.AnalyticNumberTheory.FactorialError
