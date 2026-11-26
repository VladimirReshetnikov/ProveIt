import IPRADerivations.Analysis.Series.RobbinsSeries
import IPRADerivations.Analysis.Integration.Quadrature.BaselQuadrature

/-!
# The Robbins double inequality in difference form

Packet: `analysis/stirling_ipra`, `stirling_ipra.tex`, Section `sec:factorial`, `eq:telescopers`,
`eq:strongtel`, `eq:weaktel`: for the Stirling sequence `a_n = ∑_{j ≤ n} log j − (n + ½) log n + n` and
`m ≥ n ≥ 1`,

`1/(12n+1) − 1/(12m+1) ≤ a_n − a_m ≤ 1/(12n) − 1/(12m)`.

The differences `d_k = a_k − a_{k+1}` are named by the partial sums `S_K(k) = ∑_{j=1}^K z_k^{2j}/(2j+1)`,
`z_k = 1/(2k+1)` (`eq:dseries`; `RobbinsSeries`). For a fixed precision `K = k + 2` the sum
`∑_{s<t} S_K(n + s)`, which names `a_n − a_{n+t}`, is the fraction `As t/(Bs t · F)`:
`Bs t = ∏_{s<t} w_s^K` with `w_s = (2(n+s)+1)²`, and `As (t+1) = As t · w_t^K + Tr_t · Bs t` with the cleared
sums `Tr` of `RobbinsSeries` (`F = L!`, `2K + 1 ≤ L`).

* `vT_le`: `3v · Tr ≤ w^K F`, i.e. `S_K ≤ 1/(3v) = 1/(12m(m+1)) = h_m − h_{m+1}`;
* `robbins_telescope`: for `n = n₀ + 1` and every `t`,
  `12 t · Bs t · F ≤ (12n+1)(12(n+t)+1) · As t` and `12 n (n+t) · As t ≤ t · Bs t · F`, i.e.
  `1/(12n+1) − 1/(12(n+t)+1) ≤ ∑_{s<t} S_K(n+s) ≤ 1/(12n) − 1/(12(n+t))`.

Each step adds one cell of `RobbinsSeries` (`robbins_lower`, `robbins_upper`), with the telescoper identity
`(12m+1)(12m+13) − 36 (2m+1)² = 24m − 23 ≥ 0`. The identification of `d_k` with `(k + ½) log(1 + 1/k) − 1`
(`eq:d`) uses the logarithm names and is not derived.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RobbinsTelescope

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.BaselQuadrature (lift4 inst2_lift4)
open LeanProofs.IPRA.Analysis.RobbinsSeries (Tr robbins_lower robbins_upper)
open LeanProofs.IPRA.Analysis.Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

/-- `v = 4m(m+1)`. -/
abbrev vn (m : PTm n) : PTm n := num 4 * (m * succ m)
/-- `w = (2m+1)² = 4m(m+1) + 1`. -/
abbrev wn (m : PTm n) : PTm n := succ (num 4 * (m * succ m))

/-! ## One cell: `S_K ≤ 1/(3v)` -/

/-- `3v · Tr ≤ w^K F` for `K = k + 2`, `w = v + 1`: the upper Robbins bound without its margin. -/
theorem vT_le {k v L : PTm n} (hL : Γ ⊢[PRAAx] le (succ (two * succ (succ k))) L) :
    Γ ⊢[PRAAx] le (num 3 * v * Tr (succ v) L (succ (succ k))) (pw (succ v) (succ (succ k)) * fact L) := by
  have ru := robbins_upper (v := v) hL
  have h5 : Γ ⊢[PRAAx] num 5 * (succ v * succ v) ≐ succ (num 5 * (v * v) + num 10 * v + num 4) := by
    ipra_ring
  refine mul_le_cancel (d' := num 5 * (v * v) + num 10 * v + num 4)
    (le_congr (congrMul h5 (.eqRefl _)) (congrMul h5 (.eqRefl _)) ?_)
  ipra_le sl ru + 2 * 𝔞 v * (𝔞 (pw (succ v) (succ (succ k))) * 𝔞 (fact L))

/-! ## The telescoped sums -/

/-- `w_t^K` over `(t, n₀, k, L)`, with `m = n₀ + 1 + t`. -/
abbrev Wb : PTm 2 := lift4 (pw (succ (num 4 * ((succ (var 1) + var 0) * succ (succ (var 1) + var 0))))
  (succ (succ (var 2))))

/-- `Tr w_t L K` over `(t, n₀, k, L)`. -/
abbrev Tb : PTm 2 := lift4 (Tr (succ (num 4 * ((succ (var 1) + var 0) * succ (succ (var 1) + var 0)))) (var 3)
  (succ (succ (var 2))))

theorem inst_Wb (t n₀ k L : PTm n) :
    Γ ⊢[PRAAx] inst2 Wb t (pairT n₀ (pairT k L)) ≐ pw (wn (succ n₀ + t)) (succ (succ k)) := by
  have h := inst2_lift4 (Γ := Γ) (pw (succ (num 4 * ((succ (var 1) + var 0) * succ (succ (var 1) + var 0))))
    (succ (succ (var 2)))) t n₀ k L
  simp at h; exact h

theorem inst_Tb (t n₀ k L : PTm n) :
    Γ ⊢[PRAAx] inst2 Tb t (pairT n₀ (pairT k L)) ≐ Tr (wn (succ n₀ + t)) L (succ (succ k)) := by
  have h := inst2_lift4 (Γ := Γ) (Tr (succ (num 4 * ((succ (var 1) + var 0) * succ (succ (var 1) + var 0))))
    (var 3) (succ (succ (var 2)))) t n₀ k L
  simp at h; exact h

/-- `Bs t = ∏_{s<t} w_s^K`. -/
abbrev Bs (t x : PTm n) : PTm n := ap2 (prodF Wb) t x

/-- Step of `As`: variables `0 = t`, `1 = As t`, `2 = x`. -/
abbrev aStep : PTm 3 := var 1 * inst2 Wb (var 0) (var 2) + inst2 Tb (var 0) (var 2) * ap2 (prodF Wb) (var 0) (var 2)
abbrev aF : PR 2 := rec2 zero aStep

/-- `As t`, with `As t/(Bs t · F) = ∑_{s<t} S_K(n + s)`. -/
abbrev As (t x : PTm n) : PTm n := ap2 aF t x

theorem Bs_zero (x : PTm n) : Γ ⊢[PRAAx] Bs zero x ≐ succ zero := prod_zero _ _

theorem Bs_succ (t x : PTm n) : Γ ⊢[PRAAx] Bs (succ t) x ≐ Bs t x * inst2 Wb t x := prod_succ Wb t x

theorem As_zero (x : PTm n) : Γ ⊢[PRAAx] As zero x ≐ zero := by
  have h := rec2_zero (Γ := Γ) zero aStep x
  simpa using h

theorem As_succ (t x : PTm n) :
    Γ ⊢[PRAAx] As (succ t) x ≐ As t x * inst2 Wb t x + inst2 Tb t x * Bs t x := by
  have h := rec2_succ (Γ := Γ) zero aStep t x
  have e : Syn.subst ![t, ap2 aF t x, x] aStep =
      As t x * inst2 Wb t x + inst2 Tb t x * Bs t x := by
    simp [subst_inst2]
  rw [e] at h
  exact h

/-! ## The invariants -/

/-- `1/(12n+1) − 1/(12(n+t)+1) ≤ As t/(Bs t · F)` and `As t/(Bs t · F) ≤ 1/(12n) − 1/(12(n+t))`, `n = n₀ + 1`. -/
abbrev RInv (t n₀ k L : PTm n) : Fm PTm n :=
  le (num 12 * t * (Bs t (pairT n₀ (pairT k L)) * fact L))
      (succ (num 12 * succ n₀) * succ (num 12 * (succ n₀ + t)) * As t (pairT n₀ (pairT k L))) ⋏
    le (num 12 * succ n₀ * (succ n₀ + t) * As t (pairT n₀ (pairT k L)))
      (t * (Bs t (pairT n₀ (pairT k L)) * fact L))

theorem r_base (n₀ k L : PTm n) : Γ ⊢[PRAAx] RInv zero n₀ k L := by
  have a0 := natEq (As_zero (Γ := Γ) (pairT n₀ (pairT k L)))
  refine .andI ?_ ?_
  · ipra_le 0 using rw [a0]; ring
  · ipra_le 0 using rw [a0]; ring

theorem r_step {t n₀ k L : PTm n} (hL : Γ ⊢[PRAAx] le (succ (two * succ (succ k))) L)
    (ih : Γ ⊢[PRAAx] RInv t n₀ k L) : Γ ⊢[PRAAx] RInv (succ t) n₀ k L := by
  have ihL := Prf.andE₁ ih; have ihU := Prf.andE₂ ih
  have h3 : Γ ⊢[PRAAx] le (num 3) L :=
    le_trans (le_of_eq_add (d := two * succ k) (by ipra_ring)) hL
  have rl := robbins_lower (w := wn (succ n₀ + t)) h3 (succ k)
  have hv := vT_le (v := vn (succ n₀ + t)) hL
  have eA := natEq (As_succ (Γ := Γ) t (pairT n₀ (pairT k L)))
  have eB := natEq (Bs_succ (Γ := Γ) t (pairT n₀ (pairT k L)))
  have iW := natEq (inst_Wb (Γ := Γ) t n₀ k L)
  have iT := natEq (inst_Tb (Γ := Γ) t n₀ k L)
  have pW := natEq (pw_succ (Γ := Γ) (wn (succ n₀ + t)) (succ k))
  refine .andI ?_ ?_
  · refine mul_le_cancel (d' := num 12 * (succ n₀ + t)) ?_
    ipra_le (12 * (𝔞 n₀ + 1 + 𝔞 t) + 13) * 𝔞 (pw (wn (succ n₀ + t)) (succ (succ k))) * sl ihL +
        (12 * (𝔞 n₀ + 1) + 1) * 𝔞 (Bs t (pairT n₀ (pairT k L))) *
          ((24 * (𝔞 n₀ + 𝔞 t) + 1) * 𝔞 (Tr (wn (succ n₀ + t)) L (succ (succ k))) +
            12 * 𝔞 (wn (succ n₀ + t)) * sl rl) using
      rw [eA, eB, iW, iT, pW]; ring
  · have em : Γ ⊢[PRAAx] succ n₀ + t ≐ succ (n₀ + t) := by ipra_ring
    refine mul_le_cancel (d' := n₀ + t) (le_congr (congrMul em (.eqRefl _)) (congrMul em (.eqRefl _)) ?_)
    ipra_le (𝔞 n₀ + 1 + 𝔞 t + 1) * 𝔞 (pw (wn (succ n₀ + t)) (succ (succ k))) * sl ihU +
        (𝔞 n₀ + 1) * 𝔞 (Bs t (pairT n₀ (pairT k L))) * sl hv using
      rw [eA, eB, iW, iT]; ring

/-- Variables: `0 = t` (induction), `1 = n₀`, `2 = k`, `3 = L`. -/
private abbrev rF : Fm PTm 4 :=
  le (succ (two * succ (succ (var 2)))) (var 3) ⟶ RInv (var 0) (var 1) (var 2) (var 3)

private theorem r₀ : ([] : List (Fm PTm 4)) ⊢[PRAAx] rF := by
  refine ind _ ⟨le_QF _ _, le_QF _ _, le_QF _ _⟩ ?_ ?_
  · simp only [Fm.subst_imp, Fm.subst_and, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul,
      PTm.subst_num, Syn.subst_var, Syn.inst_zero, Syn.inst_one, inst_two, inst_three,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (r_base _ _ _)
  · simp only [Fm.subst_imp, Fm.subst_and, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul,
      PTm.subst_num, Syn.subst_var, Syn.repl_zero, repl_one, repl_two, repl_three,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (r_step Prf.hyp0 (Prf.impE Prf.hyp1 Prf.hyp0))

/-- `eq:weaktel` and the lower half of `eq:strongtel`, at the precision `K = k + 2` (`2K + 1 ≤ L`), for
`n = n₀ + 1` and every `t`:
`1/(12n+1) − 1/(12(n+t)+1) ≤ ∑_{s<t} S_K(n+s) ≤ 1/(12n) − 1/(12(n+t))`, cleared. -/
theorem robbins_telescope {n₀ k L : PTm n} (hL : Γ ⊢[PRAAx] le (succ (two * succ (succ k))) L) (t : PTm n) :
    Γ ⊢[PRAAx] RInv t n₀ k L := by
  have h := inst (Γ := Γ) r₀ (![t, n₀, k, L] : Fin 4 → PTm n)
  simp at h
  exact Prf.impE h hL

/-- The closed sentence over `t`, `n₀`, `k`, `L`. -/
theorem robbins_telescope_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 rF :=
  closeUniv 4 r₀

end LeanProofs.IPRA.Analysis.RobbinsTelescope
