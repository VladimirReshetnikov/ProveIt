import IPRADerivations.Combinatorics.FallingFactorial
import IPRADerivations.Probability.Minkowski
import IPRADerivations.Analysis.BaselAverages
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.Powers

/-!
# The binomial sums against the exponential sums, term by term

Packet: `analysis/stirling_ipra`, `stirling_ipra.tex`, Section "A finite proof that `log e = 1`", `eq:EB`:
for `E_m = ∑_{j ≤ m} 1/j!` and `B_m = (1 + 1/m)^m = ∑_{j ≤ m} (1/j!) ∏_{i<j} (1 − i/m)`,

`0 ≤ E_m − B_m ≤ (1/(2m)) ∑_{j=2}^m 1/(j − 2)!`.

The comparison is made term by term. The `j`-th term of `B_m` is `(m)_j / (j! m^j)` with the falling
factorial `(m)_j = ∏_{i<j} (m ∸ i) = j! C(m, j)`, so after clearing `j! m^j` the two inequalities are

* `ff_le_pw`: `(m)_j ≤ m^j`, i.e. the `j`-th term of `B_m` is at most `1/j!`;
* `binomial_exponential_gap`: `2m · m^j + j m^j ≤ 2m · (m)_j + j² m^j`, i.e.
  `m^j − (m)_j ≤ (j (j − 1)/2) m^{j−1}`: the difference of the `j`-th terms is at most
  `(1/(2m)) · 1/(j − 2)!`;
* `binomial_gap`: the same with `(m)_j = j! C(m, j)` for `j ≤ m`.

Both are quantifier-free inductions on `j`; the step of the second is the certificate
`m · (ih) + 2m (m)_j · (j + (m ∸ j) − m) + 2m j · (m^j − (m)_j)`. This is the instance `u_i = i/m` of the
product inequality of `Analysis/WeierstrassProduct`, with the sum `∑_{i<j} i` evaluated. The summation
over `j` and the bound `3/(2m)` are not derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.BinomialExponentialGap

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.StirlingPowers (ff ff_zero ff_succ)
open LeanProofs.IPRA.Combinatorics.FallingFactorial (ff_binom)
open LeanProofs.IPRA.Combinatorics.Binomial (binom)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Probability.Minkowski (le_add_monus)
open LeanProofs.IPRA.Analysis.BaselAverages (monus_le_self)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## `(m)_j ≤ m^j` -/

theorem ff_le_base (m : PTm n) : Γ ⊢[PRAAx] le (ff m zero) (pw m zero) := by
  have f0 := natEq (ff_zero (Γ := Γ) m); have p0 := natEq (pw_zero (Γ := Γ) m)
  ipra_le 0 using rw [f0, p0]; ring

theorem ff_le_step {m j : PTm n} (ih : Γ ⊢[PRAAx] le (ff m j) (pw m j)) :
    Γ ⊢[PRAAx] le (ff m (succ j)) (pw m (succ j)) := by
  have f := natEq (ff_succ (Γ := Γ) m j); have p := natEq (pw_succ (Γ := Γ) m j)
  have hm := monus_le_self (Γ := Γ) m j
  ipra_le 𝔟 (monus m j) * sl ih + 𝔟 (pw m j) * sl hm using rw [f, p]; ring

theorem ff_le_all (m : PTm n) :
    Γ ⊢[PRAAx] Fm.all (le (ff (Syn.shift m) (var 0)) (pw (Syn.shift m) (var 0))) := by
  refine PRA.qfInd _ (le_QF _ _) ?_ ?_
  · simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
      Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact ff_le_base m
  · simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.repl_zero,
      subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact ff_le_step Prf.hyp0

/-- `(m)_j ≤ m^j`: the `j`-th term of `(1 + 1/m)^m` is at most `1/j!`. -/
theorem ff_le_pw (m j : PTm n) : Γ ⊢[PRAAx] le (ff m j) (pw m j) := by
  have a := Prf.allE j (ff_le_all (Γ := Γ) m)
  simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at a
  exact a

/-! ## `m^j − (m)_j ≤ (j (j − 1)/2) m^{j−1}` -/

/-- The gap inequality, with `j m^j` added to both sides and cleared by `2m`. -/
abbrev GapInv (m j : PTm n) : Fm PTm n :=
  le (two * m * pw m j + j * pw m j) (two * m * ff m j + j * j * pw m j)

theorem gap_base (m : PTm n) : Γ ⊢[PRAAx] GapInv m zero := by
  have f0 := natEq (ff_zero (Γ := Γ) m); have p0 := natEq (pw_zero (Γ := Γ) m)
  ipra_le 0 using rw [f0, p0]; ring

theorem gap_step {m j : PTm n} (ih : Γ ⊢[PRAAx] GapInv m j) : Γ ⊢[PRAAx] GapInv m (succ j) := by
  have f := natEq (ff_succ (Γ := Γ) m j); have p := natEq (pw_succ (Γ := Γ) m j)
  have h₁ := le_add_monus (Γ := Γ) m j
  have h₂ := ff_le_pw (Γ := Γ) m j
  ipra_le 𝔟 m * sl ih + 2 * 𝔟 m * 𝔟 (ff m j) * sl h₁ + 2 * 𝔟 m * 𝔟 j * sl h₂ using rw [f, p]; ring

theorem gap_all (m : PTm n) : Γ ⊢[PRAAx] Fm.all (GapInv (Syn.shift m) (var 0)) := by
  refine PRA.qfInd _ (le_QF _ _) ?_ ?_
  · simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
      Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact gap_base m
  · simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.repl_zero,
      subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact gap_step Prf.hyp0

/-- `eq:EB`, term by term: `2m · m^j + j m^j ≤ 2m · (m)_j + j² m^j`. -/
theorem binomial_exponential_gap (m j : PTm n) : Γ ⊢[PRAAx] GapInv m j := by
  have a := Prf.allE j (gap_all (Γ := Γ) m)
  simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at a
  exact a

/-- The same with the binomial coefficient: `2m · m^j + j m^j ≤ 2m · j! C(m, j) + j² m^j` for `j ≤ m`. -/
theorem binomial_gap {m j : PTm n} (h : Γ ⊢[PRAAx] le j m) :
    Γ ⊢[PRAAx] le (two * m * pw m j + j * pw m j) (two * m * (fact j * binom m j) + j * j * pw m j) := by
  have e := natEq (ff_binom h)
  have g := binomial_exponential_gap (Γ := Γ) m j
  ipra_le sl g using rw [e]

/-- `j! C(m, j) ≤ m^j` for `j ≤ m`. -/
theorem binomial_le {m j : PTm n} (h : Γ ⊢[PRAAx] le j m) :
    Γ ⊢[PRAAx] le (fact j * binom m j) (pw m j) :=
  le_congr (ff_binom h) (.eqRefl _) (ff_le_pw m j)

end LeanProofs.IPRA.Analysis.BinomialExponentialGap
