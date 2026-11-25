import IPRADerivations.Analysis.BohrMollerupUniqueness
import IPRADerivations.Core.LinearCombination

/-!
# The global Euler approximants and their convergence from below

Packet: `analysis/bohr_mollerup_ipra_2026-11-15`, `paper/bohr_mollerup_ipra.tex`, the lemma "explicit
convergence from below": for `x = m + r` with `0 < r ≤ 1` and
`E_n(x) = n! n^x / (x (x + 1) ⋯ (x + n))`,

`E_n(m + r) = P_m(r) A_n(r) ∏_{s=1}^m n/(n + r + s)` (`eq:En-factor`), and
`1 − ∏_{s=1}^m n/(n + r + s) ≤ ∑_{s=1}^m (r + s)/n`,

the two finite steps behind `0 ≤ Γ(x) − E_n(x) ≤ C_m/n`. With `r = a/b` the denominators are cleared by `b`
(`a + b h` for `r + h`), and `n^x = n^m n^r` is common to both sides of `eq:En-factor`:

* `off_at`: the shifted factor `a + b (M + i)`;
* `en_factor` (`eq:En-factor`, cleared): `∏_{i≤N} (a + b (m + i)) · ∏_{h<m} (a + b h) =
  ∏_{h≤N} (a + b h) · ∏_{s<m} (a + b (N + 1 + s))`, by splitting `∏_{h<m+N+1}` in two orders
  (`prod_split`): the denominator of `E_N(m + r)` times `P_m(r)` is the denominator of `A_N(r)` times the
  shifted factors;
* `product_defect` (the finite product inequality `1 − ∏ (1 − d_s) ≤ ∑ d_s` for `1 − d_s = n/(n + c_s)`):
  for factors `g_s = N + c_s` (`s < m`), `N^m ≤ ∏ g_s` and `N ∏ g_s ≤ N^{m+1} + (∑ c_s) ∏ g_s`, i.e.
  `1 − ∏ N/g_s ≤ ∑ c_s / N`.

The comparison with the represented `Γ` and the constant `C_m` are not derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.EulerApproximants

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.BohrMollerupUniqueness (rB rB_at Pq)
open LeanProofs.IPRA.Foundations.MixedRadix (prod_split prod_succ')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The factorization `eq:En-factor` -/

/-- The shifted factor `a + b (M + i)`. -/
theorem off_at (i M a b x : PTm n) :
    Γ ⊢[PRAAx] inst2 (offB rB) i (pairT M (pairT a (pairT b x))) ≐ a + b * (M + i) := by
  rw [inst2_offB]
  exact (congrInst2 rB (congrAdd (fst_pair _ _) (.eqRefl i)) (snd_pair _ _)).eqTrans (rB_at _ a b x)

/-- `eq:En-factor`, cleared: `∏_{i<N+1} (a + b (m + i)) · P_m = P_{N+1} · ∏_{s<m} (a + b (N + 1 + s))`. -/
theorem en_factor (m N a b x : PTm n) :
    Γ ⊢[PRAAx] ap2 (prodF (offB rB)) (succ N) (pairT m (pairT a (pairT b x))) * Pq m a b x ≐
      Pq (succ N) a b x * ap2 (prodF (offB rB)) m (pairT (succ N) (pairT a (pairT b x))) := by
  ipra_lc -natEq (prod_split (Γ := Γ) rB m (succ N) (pairT a (pairT b x))) +
    natEq (congrAp2 (Γ := Γ) (prodF rB) (add_comm m (succ N)) (.eqRefl (pairT a (pairT b x)))) +
    natEq (prod_split (Γ := Γ) rB (succ N) m (pairT a (pairT b x)))

/-! ## The product defect -/

section Defect

variable (g c : PTm 2)

/-- `Q_K = ∏_{s<K} g_s`, `S_K = ∑_{s<K} c_s`. -/
abbrev Qp (K x : PTm n) : PTm n := ap2 (prodF g) K x
abbrev Sc (K x : PTm n) : PTm n := ap2 (sumF c) K x

theorem defect_step {N K x : PTm n} (hg : Γ ⊢[PRAAx] inst2 g K x ≐ N + inst2 c K x)
    (ih₁ : Γ ⊢[PRAAx] le (pw N K) (Qp g K x))
    (ih₂ : Γ ⊢[PRAAx] le (N * Qp g K x) (pw N (succ K) + Sc c K x * Qp g K x)) :
    Γ ⊢[PRAAx] le (pw N (succ K)) (Qp g (succ K) x) ⋏
      le (N * Qp g (succ K) x) (pw N (succ (succ K)) + Sc c (succ K) x * Qp g (succ K) x) := by
  have q := natEq (prod_succ' (Γ := Γ) g K x)
  have s := natEq (sum_succ' (Γ := Γ) c K x)
  have p₁ := natEq (pw_succ (Γ := Γ) N K)
  have p₂ := natEq (pw_succ (Γ := Γ) N (succ K))
  have e := natEq hg
  refine .andI ?_ ?_
  · ipra_le sl ih₁ * (𝔟 N + 𝔟 (inst2 c K x)) + 𝔟 (pw N K) * 𝔟 (inst2 c K x) using
      rw [q, p₁, e]; ring
  · ipra_le sl ih₂ * (𝔟 N + 𝔟 (inst2 c K x)) +
        𝔟 (inst2 c K x) * (sl ih₁ * (𝔟 N + 𝔟 (inst2 c K x)) + 𝔟 (pw N K) * 𝔟 (inst2 c K x)) using
      rw [q, s, p₂, p₁, e]; ring

/-- `1 − ∏ (1 − d_s) ≤ ∑ d_s` for `1 − d_s = N/(N + c_s)`: with `g_s = N + c_s` for `s < m`,
`N^m ≤ ∏_{s<m} g_s` and `N ∏_{s<m} g_s ≤ N^{m+1} + (∑_{s<m} c_s) ∏_{s<m} g_s`. -/
theorem product_defect (N m x : PTm n)
    (hg : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift m) ⟶
      (inst2 g (var 0) (Syn.shift x) ≐ Syn.shift N + inst2 c (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] le (pw N m) (Qp g m x) ⋏ le (N * Qp g m x) (pw N (succ m) + Sc c m x * Qp g m x) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift m) ⟶
      (le (pw (Syn.shift N) (var 0)) (Qp g (var 0) (Syn.shift x)) ⋏
        le (Syn.shift N * Qp g (var 0) (Syn.shift x))
          (pw (Syn.shift N) (succ (var 0)) + Sc c (var 0) (Syn.shift x) * Qp g (var 0) (Syn.shift x)))) := by
    refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _, le_QF _ _⟩ ?_ ?_
    · simp only [Fm.subst_imp, Fm.subst_and, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
        Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      refine .impI ?_
      have q := natEq (prod_zero (Γ := le zero m :: Γ) g x)
      have s := natEq (sum_zero (Γ := le zero m :: Γ) c x)
      have p₀ := natEq (pw_zero (Γ := le zero m :: Γ) N)
      have p₁ := natEq (pw_succ (Γ := le zero m :: Γ) N zero)
      refine .andI ?_ ?_
      · ipra_le 0 using rw [q, p₀]; ring
      · ipra_le 0 using rw [q, s, p₁, p₀]; ring
    · simp only [Fm.subst_imp, Fm.subst_and, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
        Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      refine .impI ?_
      have hk : (le (succ (var 0)) (Syn.shift m) ::
          (le (var 0) (Syn.shift m) ⟶
            (le (pw (Syn.shift N) (var 0)) (Qp g (var 0) (Syn.shift x)) ⋏
              le (Syn.shift N * Qp g (var 0) (Syn.shift x))
                (pw (Syn.shift N) (succ (var 0)) + Sc c (var 0) (Syn.shift x) * Qp g (var 0) (Syn.shift x)))) ::
          Γ.map Fm.shift) ⊢[PRAAx] le (succ (var 0)) (Syn.shift m) := Prf.hyp0
      have ih := Prf.impE Prf.hyp1 (le_trans (le_succ_self _) hk)
      exact defect_step g c (Prf.impE hg.allOpen.wk.wk hk) (Prf.andE₁ ih) (Prf.andE₂ ih)
  have h2 := Prf.allE m hall
  simp only [Fm.subst_imp, Fm.subst_and, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at h2
  exact .impE h2 (le_refl m)

end Defect

end LeanProofs.IPRA.Analysis.EulerApproximants
