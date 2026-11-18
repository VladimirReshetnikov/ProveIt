import IPRADerivations.Analysis.BaselSquares
import IPRADerivations.Core.OrderCertificates

/-!
# The rational series behind the Robbins bounds

Packet: `analysis/stirling_ipra`, `stirling_ipra.tex`, Section `sec:factorial` (`eq:dseries`, `eq:dcompare`,
`eq:margins`, `eq:telescopers`): for `z = 1/(2n+1)` the difference `d_n = a_n − a_{n+1}` of the Stirling
sequence is named by the partial sums `S_K = ∑_{j=1}^K z^{2j}/(2j+1)`, and

`1/(3(2n+1)²) ≤ S_K ≤ 1/(12n(n+1)) − 2/(15(2n+1)⁴)`,

where the lower bound holds for `K ≥ 1` and the upper bound for `K ≥ 2`; with the telescopers
`g_n = 1/(12n+1)`, `h_n = 1/(12n)` this is `g_n − g_{n+1} + λ_n ≤ S_K ≤ h_n − h_{n+1} − μ_n`.

Write `w = (2n+1)² = v + 1` with `v = 4n(n+1)`. Denominators are cleared by `F = L!` (so that
`g_j = F/(2j+1)` is exact for `2j + 1 ≤ L`) and by `w^K`: `Tr w L K = ∑_{j=1}^K w^{K−j} g_j = w^K F S_K`,
defined by the recursion `Tr (K + 1) = w · Tr K + g_{K+1}`. The statements hold for every `w = v + 1`:

* `robbins_lower`: `w^K F ≤ 3 · Tr (K + 1)`, i.e. `S_{K+1} ≥ 1/(3w)`;
* `upper_inv`: for `K = k + 2`, `15 w² v · Tr K + 5 w² F + 2v w^K F ≤ 5 w^{K+2} F`, i.e.
  `S_K + 1/(3 w^K (w − 1)) ≤ 1/(3(w − 1)) − 2/(15 w²)`: the bound with its geometric tail, which is an
  equality at `K = 2` and is preserved because `3 g_{K+1} ≤ F`;
* `robbins_upper`: `15 w² v · Tr K + 2v w^K F ≤ 5 w² w^K F`, i.e. `S_K ≤ 1/(3v) − 2/(15 w²)`;
* `margin`: `(12n+1)(12n+13) + 23 = 36 (2n+1)² + 24n`, the identity behind
  `1/(3(2n+1)²) = g_n − g_{n+1} + λ_n` (`eq:margins`); `w_eq`: `(2n+1)² = 4n(n+1) + 1`, behind
  `z²/(3(1 − z²)) = 1/(12n(n+1)) = h_n − h_{n+1}`.

The identification of `d_n` with the series (`eq:d`, `eq:dseries`) uses the logarithm names and is not
derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RobbinsSeries

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.BaselSquares (fact_eq)
open LeanProofs.IPRA.Analysis.Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

/-! ## The cleared partial sums -/

/-- `g_j = L!/(2j+1)`. -/
abbrev gq (j L : PTm n) : PTm n := quo (fact L) (succ (two * j))

/-- Step of `Tr`: variables `0 = K`, `1 = Tr K`, `2 = ⟨w, L⟩`. -/
abbrev tStep : PTm 3 := fstT (var 2) * var 1 + quo (fact (sndT (var 2))) (succ (two * succ (var 0)))
abbrev tF : PR 2 := rec2 zero tStep

/-- `Tr w L K = ∑_{j=1}^K w^{K−j} L!/(2j+1)`. -/
abbrev Tr (w L K : PTm n) : PTm n := ap2 tF K (pairT w L)

theorem Tr_zero (w L : PTm n) : Γ ⊢[PRAAx] Tr w L zero ≐ zero := by
  have h := rec2_zero (Γ := Γ) zero tStep (pairT w L)
  simpa using h

theorem Tr_succ (w L K : PTm n) : Γ ⊢[PRAAx] Tr w L (succ K) ≐ w * Tr w L K + gq (succ K) L := by
  have h := rec2_succ (Γ := Γ) zero tStep K (pairT w L)
  have e : Syn.subst ![K, ap2 tF K (pairT w L), pairT w L] tStep =
      fstT (pairT w L) * Tr w L K + quo (fact (sndT (pairT w L))) (succ (two * succ K)) := by
    simp [ConciseIPRA.PTm.subst_succ]
  rw [e] at h
  exact h.eqTrans (congrAdd (congrMul (fst_pair _ _) (.eqRefl _))
    (congrAp2 quoF (congrAp2 factF (snd_pair _ _) (.eqRefl _)) (.eqRefl _)))

/-- `F = (2j + 1) g_j` for `2j + 1 ≤ L`. -/
theorem g_eq {j L : PTm n} (h : Γ ⊢[PRAAx] le (succ (two * j)) L) :
    Γ ⊢[PRAAx] fact L ≐ succ (two * j) * gq j L := fact_eq h

/-! ## The lower bound -/

theorem lower_base {w L : PTm n} (hL : Γ ⊢[PRAAx] le (num 3) L) :
    Γ ⊢[PRAAx] le (pw w zero * fact L) (num 3 * Tr w L (succ zero)) := by
  have h3 : Γ ⊢[PRAAx] le (succ (two * succ zero)) L :=
    le_congr (by apply deriveNat; ipra_simps; ring) (.eqRefl _) hL
  have e := natEq (g_eq h3)
  have t1 := natEq (Tr_succ (Γ := Γ) w L zero); have t0 := natEq (Tr_zero (Γ := Γ) w L)
  have p0 := natEq (pw_zero (Γ := Γ) w)
  ipra_le 0 using
    rw [t1, t0, p0]
    linear_combination -e

theorem lower_step {w L K : PTm n} (ih : Γ ⊢[PRAAx] le (pw w K * fact L) (num 3 * Tr w L (succ K))) :
    Γ ⊢[PRAAx] le (pw w (succ K) * fact L) (num 3 * Tr w L (succ (succ K))) := by
  have t := natEq (Tr_succ (Γ := Γ) w L (succ K))
  have p := natEq (pw_succ (Γ := Γ) w K)
  ipra_le 𝔞 w * sl ih + 3 * 𝔞 (gq (succ (succ K)) L) using rw [t, p]; ring

/-- Variables: `0 = K` (induction), `1 = w`, `2 = L`. -/
private abbrev lowF : Fm PTm 3 :=
  le (num 3) (var 2) ⟶ le (pw (var 1) (var 0) * fact (var 2)) (num 3 * Tr (var 1) (var 2) (succ (var 0)))

private theorem low₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] lowF := by
  refine ind _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
  · simp only [Fm.subst_imp, subst_le, subst_ap2, subst_pairT, PTm.subst_mul, PTm.subst_num,
      Syn.subst_var, Syn.inst_zero, Syn.inst_one, inst_two, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact .impI (lower_base Prf.hyp0)
  · simp only [Fm.subst_imp, subst_le, subst_ap2, subst_pairT, PTm.subst_mul, PTm.subst_num,
      Syn.subst_var, Syn.repl_zero, repl_one, repl_two, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact .impI (lower_step (Prf.impE Prf.hyp1 Prf.hyp0))

/-- `S_{K+1} ≥ 1/(3w)`: `w^K F ≤ 3 · Tr (K + 1)`, for `3 ≤ L`. -/
theorem robbins_lower {w L : PTm n} (hL : Γ ⊢[PRAAx] le (num 3) L) (K : PTm n) :
    Γ ⊢[PRAAx] le (pw w K * fact L) (num 3 * Tr w L (succ K)) := by
  have h := inst (Γ := Γ) low₀ (![K, w, L] : Fin 3 → PTm n)
  simp at h
  exact Prf.impE h hL

/-! ## The upper bound with its geometric tail -/

/-- `15 w² v · Tr K + 5 w² F + 2v w^K F ≤ 5 w^{K+2} F` for `K = k + 2`, `w = v + 1`. -/
abbrev UpInv (k v L : PTm n) : Fm PTm n :=
  le (num 15 * (succ v * succ v) * v * Tr (succ v) L (succ (succ k)) + num 5 * (succ v * succ v) * fact L +
      two * v * (pw (succ v) (succ (succ k)) * fact L))
    (num 5 * (pw (succ v) (succ (succ (succ (succ k)))) * fact L))

theorem upper_base {v L : PTm n} (hL : Γ ⊢[PRAAx] le (succ (two * succ (succ zero))) L) :
    Γ ⊢[PRAAx] UpInv zero v L := by
  have h3 : Γ ⊢[PRAAx] le (succ (two * succ zero)) L :=
    le_trans (le_of_eq_add (d := two) (by apply deriveNat; ipra_simps; ring)) hL
  have e3 := natEq (g_eq h3); have e5 := natEq (g_eq hL)
  have t2 := natEq (Tr_succ (Γ := Γ) (succ v) L (succ zero))
  have t1 := natEq (Tr_succ (Γ := Γ) (succ v) L zero); have t0 := natEq (Tr_zero (Γ := Γ) (succ v) L)
  have p0 := natEq (pw_zero (Γ := Γ) (succ v))
  have p1 := natEq (pw_succ (Γ := Γ) (succ v) zero)
  have p2 := natEq (pw_succ (Γ := Γ) (succ v) (succ zero))
  have p3 := natEq (pw_succ (Γ := Γ) (succ v) (succ (succ zero)))
  have p4 := natEq (pw_succ (Γ := Γ) (succ v) (succ (succ (succ zero))))
  ipra_le 0 using
    rw [t2, t1, t0, p4, p3, p2, p1, p0]
    linear_combination (5 * (𝔞 v + 1) * (𝔞 v + 1) * (𝔞 v + 1) * 𝔞 v) * e3 +
      (3 * (𝔞 v + 1) * (𝔞 v + 1) * 𝔞 v) * e5

theorem upper_step {k v L : PTm n} (hL : Γ ⊢[PRAAx] le (succ (two * succ (succ (succ k)))) L)
    (ih : Γ ⊢[PRAAx] UpInv k v L) : Γ ⊢[PRAAx] UpInv (succ k) v L := by
  have e := natEq (g_eq hL)
  have t := natEq (Tr_succ (Γ := Γ) (succ v) L (succ (succ k)))
  have p3 := natEq (pw_succ (Γ := Γ) (succ v) (succ (succ k)))
  have p5 := natEq (pw_succ (Γ := Γ) (succ v) (succ (succ (succ (succ k)))))
  ipra_le (𝔞 v + 1) * sl ih +
      5 * ((𝔞 v + 1) * (𝔞 v + 1)) * 𝔞 v * (2 * (𝔞 k + 2)) * 𝔞 (gq (succ (succ (succ k))) L) using
    rw [t, p3, p5]
    linear_combination (5 * ((𝔞 v + 1) * (𝔞 v + 1)) * 𝔞 v) * e

/-- Variables: `0 = k` (induction), `1 = v`, `2 = L`. -/
private abbrev upF : Fm PTm 3 :=
  le (succ (two * succ (succ (var 0)))) (var 2) ⟶ UpInv (var 0) (var 1) (var 2)

private theorem up₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] upF := by
  refine ind _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
  · simp only [Fm.subst_imp, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, PTm.subst_num,
      Syn.subst_var, Syn.inst_zero, Syn.inst_one, inst_two, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact .impI (upper_base Prf.hyp0)
  · simp only [Fm.subst_imp, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, PTm.subst_num,
      Syn.subst_var, Syn.repl_zero, repl_one, repl_two, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    refine .impI (upper_step Prf.hyp0 (Prf.impE Prf.hyp1 (le_trans (le_of_eq_add (d := two) ?_) Prf.hyp0)))
    apply deriveNat; ipra_simps; ring

/-- The upper bound with its tail, for `K = k + 2`, `w = v + 1` and `2K + 1 ≤ L`. -/
theorem upper_inv {k v L : PTm n} (hL : Γ ⊢[PRAAx] le (succ (two * succ (succ k))) L) :
    Γ ⊢[PRAAx] UpInv k v L := by
  have h := inst (Γ := Γ) up₀ (![k, v, L] : Fin 3 → PTm n)
  simp at h
  exact Prf.impE h hL

/-- `eq:dcompare`, upper part: `S_K ≤ 1/(3v) − 2/(15 w²)` for `K = k + 2`, `w = v + 1`, cleared:
`15 w² v · Tr K + 2v w^K F ≤ 5 w² w^K F`. -/
theorem robbins_upper {k v L : PTm n} (hL : Γ ⊢[PRAAx] le (succ (two * succ (succ k))) L) :
    Γ ⊢[PRAAx] le (num 15 * (succ v * succ v) * v * Tr (succ v) L (succ (succ k)) +
        two * v * (pw (succ v) (succ (succ k)) * fact L))
      (num 5 * (succ v * succ v) * (pw (succ v) (succ (succ k)) * fact L)) := by
  have u := upper_inv (v := v) hL
  have p3 := natEq (pw_succ (Γ := Γ) (succ v) (succ (succ k)))
  have p4 := natEq (pw_succ (Γ := Γ) (succ v) (succ (succ (succ k))))
  ipra_le sl u + 5 * ((𝔞 v + 1) * (𝔞 v + 1)) * 𝔞 (fact L) using rw [p4, p3]; ring

/-! ## The telescoper identities (`eq:margins`) -/

/-- `(12n+1)(12n+13) + 23 = 36 (2n+1)² + 24n`: with `g_n = 1/(12n+1)` and
`λ_n = (24n − 23)/(3 (2n+1)² (12n+1)(12n+13))`, `1/(3(2n+1)²) = g_n − g_{n+1} + λ_n`. -/
theorem margin (m : PTm n) :
    Γ ⊢[PRAAx] succ (num 12 * m) * (num 12 * m + num 13) + num 23 ≐
      num 36 * (succ (two * m) * succ (two * m)) + num 24 * m := by
  apply deriveNat; ipra_simps; ring

/-- `(2n+1)² = 4n(n+1) + 1`: with `z = 1/(2n+1)` and `h_n = 1/(12n)`,
`z²/(3(1 − z²)) = 1/(12n(n+1)) = h_n − h_{n+1}`. -/
theorem w_eq (m : PTm n) :
    Γ ⊢[PRAAx] succ (two * m) * succ (two * m) ≐ succ (num 4 * (m * succ m)) := by
  apply deriveNat; ipra_simps; ring

/-- `eq:dcompare` at `z = 1/(2n+1)`, for `K = k + 2` and `2K + 1 ≤ L`, with `w = 4n(n+1) + 1 = (2n+1)²`:
`w^{K−1} F ≤ 3 · Tr K` and `15 w² v · Tr K + 2v w^K F ≤ 5 w² w^K F` with `v = 4n(n+1)`, i.e.
`1/(3(2n+1)²) ≤ S_K ≤ 1/(12n(n+1)) − 2/(15(2n+1)⁴)`. -/
theorem robbins_core {m k L : PTm n} (hL : Γ ⊢[PRAAx] le (succ (two * succ (succ k))) L) :
    Γ ⊢[PRAAx] le (pw (succ (num 4 * (m * succ m))) (succ k) * fact L)
        (num 3 * Tr (succ (num 4 * (m * succ m))) L (succ (succ k))) ⋏
      le (num 15 * (succ (num 4 * (m * succ m)) * succ (num 4 * (m * succ m))) * (num 4 * (m * succ m)) *
          Tr (succ (num 4 * (m * succ m))) L (succ (succ k)) +
        two * (num 4 * (m * succ m)) * (pw (succ (num 4 * (m * succ m))) (succ (succ k)) * fact L))
      (num 5 * (succ (num 4 * (m * succ m)) * succ (num 4 * (m * succ m))) *
        (pw (succ (num 4 * (m * succ m))) (succ (succ k)) * fact L)) := by
  have h3 : Γ ⊢[PRAAx] le (num 3) L :=
    le_trans (le_of_eq_add (d := two * succ k) (by apply deriveNat; ipra_simps; ring)) hL
  exact .andI (robbins_lower h3 (succ k)) (robbins_upper hL)

end LeanProofs.IPRA.Analysis.RobbinsSeries
