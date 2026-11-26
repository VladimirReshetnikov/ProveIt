import IPRADerivations.Analysis.Stirling.WallisFinite
import IPRADerivations.Probability.Variance

/-!
# The integrals of `(1 − t²)^j` by finite sums

Packet: `analysis/cauchy_residue_ipra`, `report.tex`, "A fast rational construction of `π`", `eq:piapprox`
and `eq:Jrec`: `J_j = ∫_0^1 (1 − t²)^j dt` satisfies `J_0 = 1` and `J_j = (2j/(2j+1)) J_{j−1}`, proved by
"integrating the derivative of `t (1 − t²)^j`"; hence `J_j = (2j)!!/(2j+1)!!`.

Here the integral is the left Riemann sum on the grid `t = i/M`: with `x_i = M² − i²` and
`P_j = ∑_{i<M} x_i^j` (so `P_j = M^{2j+1}` times the Riemann sum), the telescoping of `i · x_i^j` gives, for
`j = j₀ + 1`,

* `rec_up`, `rec_lo` (`eq:Jrec`): `2j M² P_{j−1} − (2j − 1) M^{2j} ≤ (2j + 1) P_j ≤ 2j M² P_{j−1} + (j + 1) M^{2j}`;
* `even_power_integral` (and the closed sentence `even_power_integral_closed`): with the double factorials
  of `WallisFinite`, `da (j+1) · P_j ≤ db j · M^{2j+1} + (j+1) · da (j+1) · M^{2j}` and
  `db j · M^{2j+1} ≤ da (j+1) · P_j + 2j · da (j+1) · M^{2j}`, i.e. the Riemann sum of `(1 − t²)^j` is
  within `2j/M` of `(2j)!!/(2j+1)!!` (it is `q_j` of the Stirling packet).

The cells are exact: with `g = ∑_{r<j} x^{j−1−r} x'^r` (`gd`) and `x − x' = 2i + 1`,
`x^j − x'^j = (2i + 1) g`, `g ≤ j x^{j−1}` (`gd_le`) and `g − j x'^{j−1} = (2i + 1) · kd` (`gd_kd`), so
`cell_up` and `cell_lo` are single certificates, and the partial sums (`u_all`, `l_all`) follow by
quantifier-free induction. No second-order estimate is needed: the lower bound compares with the right
samples `x'^{j−1}`, whose sum differs from the left one by a telescoping term.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.EvenPowerIntegrals

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.BaselCore (lift3 inst2_lift3)
open LeanProofs.IPRA.Algebra.PowerDifference (gd power_diff gd_le)
open LeanProofs.IPRA.Analysis.PowerIncrement (kd gd_kd)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

/-! ## The samples and their sums -/

/-- `x_i = M² − i²`. -/
abbrev xs (i M : PTm n) : PTm n := monus (M * M) (i * i)

/-- `(M² − i²)^j` over `(i, j, M)`. -/
abbrev Pb : PTm 2 := lift3 (pw (monus (var 2 * var 2) (var 0 * var 0)) (var 1))

/-- `∑_{i<k} (M² − i²)^j`. -/
abbrev Ps (j M k : PTm n) : PTm n := ap2 (sumF Pb) k (pairT j M)

theorem inst_Pb (i j M : PTm n) : Γ ⊢[PRAAx] inst2 Pb i (pairT j M) ≐ pw (xs i M) j := by
  have h := inst2_lift3 (Γ := Γ) (pw (monus (var 2 * var 2) (var 0 * var 0)) (var 1)) i j M
  simp at h; exact h

theorem x0_eq (M : PTm n) : Γ ⊢[PRAAx] xs zero M ≐ M * M :=
  (congrMonus (.eqRefl _) (zero_mul zero)).eqTrans (monus_zero _)

/-- `x_i ≤ M²` for `i ≤ M`. -/
theorem x_le_sq {i M : PTm n} (hi : Γ ⊢[PRAAx] le i M) : Γ ⊢[PRAAx] le (xs i M) (M * M) := by
  have a := natEq (eq_add_of_le (le_mul_mono hi hi))
  ipra_le 𝔞 i * 𝔞 i with a

/-- `x_{i+1} ≤ x_i` for `i + 1 ≤ M`. -/
theorem x_anti {i M : PTm n} (hi : Γ ⊢[PRAAx] le (succ i) M) : Γ ⊢[PRAAx] le (xs (succ i) M) (xs i M) := by
  have hi0 : Γ ⊢[PRAAx] le i M := le_trans (le_succ_self i) hi
  have a := natEq (eq_add_of_le (le_mul_mono hi0 hi0))
  have b := natEq (eq_add_of_le (le_mul_mono hi hi))
  ipra_le 2 * 𝔞 i + 1 with b - a

/-! ## One cell -/

section cell

variable {i j₀ M : PTm n}

local notation "x₀" => xs i M
local notation "x₁" => xs (succ i) M

/-- The upper cell inequality: `(2j+1) x^j + i x^j + x'^j ≤ 2j M² x^{j−1} + (i+1) x'^j + x^j + i j x^{j−1}`. -/
theorem cell_up (hi : Γ ⊢[PRAAx] le (succ i) M) :
    Γ ⊢[PRAAx] le (succ (two * succ j₀) * pw x₀ (succ j₀) + i * pw x₀ (succ j₀) + pw x₁ (succ j₀))
      (two * succ j₀ * (M * M) * pw x₀ j₀ + succ i * pw x₁ (succ j₀) + pw x₀ (succ j₀) +
        i * (succ j₀ * pw x₀ j₀)) := by
  have hi0 : Γ ⊢[PRAAx] le i M := le_trans (le_succ_self i) hi
  have a := natEq (eq_add_of_le (le_mul_mono hi0 hi0))
  have b := natEq (eq_add_of_le (le_mul_mono hi hi))
  have hg := gd_le (Γ := Γ) j₀ (le_refl x₀) (x_anti hi)
  have pd := natEq (power_diff (Γ := Γ) x₀ x₁ (succ j₀))
  have px := natEq (pw_succ (Γ := Γ) x₀ j₀)
  ipra_le 𝔞 i * (2 * 𝔞 i + 1) * sl hg using
    linear_combination (2 * (𝔞 j₀ + 1) * 𝔞 (pw x₀ j₀) + 𝔞 i * 𝔞 (gd x₀ x₁ (succ j₀))) * a -
      2 * (𝔞 j₀ + 1) * px - 𝔞 i * pd - (𝔞 i * 𝔞 (gd x₀ x₁ (succ j₀))) * b

/-- The lower cell inequality: `(i+1) x'^j + x^j + 2j M² x'^{j−1} ≤ (2j+1) x^j + i x^j + x'^j`. -/
theorem cell_lo (hi : Γ ⊢[PRAAx] le (succ i) M) :
    Γ ⊢[PRAAx] le (succ i * pw x₁ (succ j₀) + pw x₀ (succ j₀) + two * succ j₀ * (M * M) * pw x₁ j₀)
      (succ (two * succ j₀) * pw x₀ (succ j₀) + i * pw x₀ (succ j₀) + pw x₁ (succ j₀)) := by
  have hi0 : Γ ⊢[PRAAx] le i M := le_trans (le_succ_self i) hi
  have a := natEq (eq_add_of_le (le_mul_mono hi0 hi0))
  have b := natEq (eq_add_of_le (le_mul_mono hi hi))
  have hp := pw_le_pw j₀ (x_anti hi)
  have pd := natEq (power_diff (Γ := Γ) x₀ x₁ (succ j₀))
  have px := natEq (pw_succ (Γ := Γ) x₀ j₀)
  have gk := natEq (gd_kd (Γ := Γ) x₀ x₁ j₀)
  ipra_le 2 * (𝔞 j₀ + 1) * 𝔞 x₀ * sl hp + 2 * (𝔞 i * 𝔞 i) * (2 * 𝔞 i + 1) * 𝔞 (kd x₀ x₁ j₀) +
      𝔞 i * 𝔞 (gd x₀ x₁ (succ j₀)) using
    linear_combination 2 * (𝔞 j₀ + 1) * px + 𝔞 i * pd +
      (𝔞 i * 𝔞 (gd x₀ x₁ (succ j₀)) + 2 * 𝔞 i * 𝔞 i * 𝔞 (kd x₀ x₁ j₀)) * b -
      (𝔞 i * 𝔞 (gd x₀ x₁ (succ j₀)) + 2 * 𝔞 i * 𝔞 i * 𝔞 (kd x₀ x₁ j₀) +
        2 * (𝔞 j₀ + 1) * 𝔞 (pw x₁ j₀)) * a + 2 * 𝔞 i * 𝔞 i * gk

end cell

/-! ## The partial sums -/

/-- `(2j+1) S_j(k) + x_k^j ≤ 2j M² S_{j−1}(k) + k x_k^j + M^{2j} + j k M^{2j−1}`. -/
abbrev UInv (k j₀ M : PTm n) : Fm PTm n :=
  le (succ (two * succ j₀) * Ps (succ j₀) M k + pw (xs k M) (succ j₀))
    (two * succ j₀ * (M * M) * Ps j₀ M k + k * pw (xs k M) (succ j₀) + pw (M * M) (succ j₀) +
      succ j₀ * (k * (M * pw (M * M) j₀)))

/-- `2j M² S_{j−1}(k) + 2j M² x_k^{j−1} + k x_k^j + M^{2j} ≤ (2j+1) S_j(k) + x_k^j + 2j M^{2j}`. -/
abbrev LInv (k j₀ M : PTm n) : Fm PTm n :=
  le (two * succ j₀ * (M * M) * Ps j₀ M k + two * succ j₀ * (M * M) * pw (xs k M) j₀ +
      k * pw (xs k M) (succ j₀) + pw (M * M) (succ j₀))
    (succ (two * succ j₀) * Ps (succ j₀) M k + pw (xs k M) (succ j₀) +
      two * succ j₀ * (M * M) * pw (M * M) j₀)

theorem u_base (j₀ M : PTm n) : Γ ⊢[PRAAx] UInv zero j₀ M := by
  have z1 := natEq (sum_zero (Γ := Γ) Pb (pairT (succ j₀) M))
  have z2 := natEq (sum_zero (Γ := Γ) Pb (pairT j₀ M))
  have e0 := natEq (congrAp2 powF (.eqRefl (succ j₀)) (x0_eq (Γ := Γ) M))
  ipra_le 0 using rw [z1, z2, e0]; ring

theorem l_base (j₀ M : PTm n) : Γ ⊢[PRAAx] LInv zero j₀ M := by
  have z1 := natEq (sum_zero (Γ := Γ) Pb (pairT (succ j₀) M))
  have z2 := natEq (sum_zero (Γ := Γ) Pb (pairT j₀ M))
  have e0 := natEq (congrAp2 powF (.eqRefl (succ j₀)) (x0_eq (Γ := Γ) M))
  have e1 := natEq (congrAp2 powF (.eqRefl j₀) (x0_eq (Γ := Γ) M))
  ipra_le 0 using rw [z1, z2, e0, e1]; ring

theorem u_step {k j₀ M : PTm n} (hk : Γ ⊢[PRAAx] le (succ k) M) (ih : Γ ⊢[PRAAx] UInv k j₀ M) :
    Γ ⊢[PRAAx] UInv (succ k) j₀ M := by
  have hk0 : Γ ⊢[PRAAx] le k M := le_trans (le_succ_self k) hk
  have c := cell_up (j₀ := j₀) hk
  have hb := le_mul_mono hk0 (pw_le_pw j₀ (x_le_sq hk0))
  have e1 := natEq (sum_succ' (Γ := Γ) Pb k (pairT (succ j₀) M))
  have e2 := natEq (inst_Pb (Γ := Γ) k (succ j₀) M)
  have e3 := natEq (sum_succ' (Γ := Γ) Pb k (pairT j₀ M))
  have e4 := natEq (inst_Pb (Γ := Γ) k j₀ M)
  ipra_le sl ih + sl c + (𝔞 j₀ + 1) * sl hb using rw [e1, e2, e3, e4]; ring

theorem l_step {k j₀ M : PTm n} (hk : Γ ⊢[PRAAx] le (succ k) M) (ih : Γ ⊢[PRAAx] LInv k j₀ M) :
    Γ ⊢[PRAAx] LInv (succ k) j₀ M := by
  have c := cell_lo (j₀ := j₀) hk
  have e1 := natEq (sum_succ' (Γ := Γ) Pb k (pairT (succ j₀) M))
  have e2 := natEq (inst_Pb (Γ := Γ) k (succ j₀) M)
  have e3 := natEq (sum_succ' (Γ := Γ) Pb k (pairT j₀ M))
  have e4 := natEq (inst_Pb (Γ := Γ) k j₀ M)
  ipra_le sl ih + sl c using rw [e1, e2, e3, e4]; ring

/-- Variables: `0 = k` (induction), `1 = j₀`, `2 = M`. -/
private abbrev uF : Fm PTm 3 := le (var 0) (var 2) ⟶ UInv (var 0) (var 1) (var 2)
private abbrev lF : Fm PTm 3 := le (var 0) (var 2) ⟶ LInv (var 0) (var 1) (var 2)

private theorem u₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] uF := by
  refine ind _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
  · simp only [Fm.subst_imp, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, PTm.subst_monus,
      Syn.subst_var, Syn.inst_zero, Syn.inst_one, inst_two, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact .impI (u_base _ _)
  · simp only [Fm.subst_imp, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, PTm.subst_monus,
      Syn.subst_var, Syn.repl_zero, repl_one, repl_two, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact .impI (u_step Prf.hyp0 (Prf.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)))

private theorem l₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] lF := by
  refine ind _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
  · simp only [Fm.subst_imp, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, PTm.subst_monus,
      Syn.subst_var, Syn.inst_zero, Syn.inst_one, inst_two, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact .impI (l_base _ _)
  · simp only [Fm.subst_imp, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, PTm.subst_monus,
      Syn.subst_var, Syn.repl_zero, repl_one, repl_two, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact .impI (l_step Prf.hyp0 (Prf.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)))

theorem u_all {k M : PTm n} (j₀ : PTm n) (hk : Γ ⊢[PRAAx] le k M) : Γ ⊢[PRAAx] UInv k j₀ M := by
  have h := inst (Γ := Γ) u₀ (![k, j₀, M] : Fin 3 → PTm n)
  simp at h
  exact Prf.impE h hk

theorem l_all {k M : PTm n} (j₀ : PTm n) (hk : Γ ⊢[PRAAx] le k M) : Γ ⊢[PRAAx] LInv k j₀ M := by
  have h := inst (Γ := Γ) l₀ (![k, j₀, M] : Fin 3 → PTm n)
  simp at h
  exact Prf.impE h hk

/-! ## The recurrence (`eq:Jrec`) -/

/-- `(2j + 1) P_j ≤ 2j M² P_{j−1} + (j + 1) M^{2j}` for `j = j₀ + 1`. -/
theorem rec_up (j₀ M : PTm n) :
    Γ ⊢[PRAAx] le (succ (two * succ j₀) * Ps (succ j₀) M M)
      (two * succ j₀ * (M * M) * Ps j₀ M M + (succ j₀ + one) * pw (M * M) (succ j₀)) := by
  have u := u_all (Γ := Γ) (k := M) j₀ (le_refl M)
  have ex := natEq (pw_succ (Γ := Γ) (xs M M) j₀)
  have em := natEq (monus_self (Γ := Γ) (M * M))
  have ps := natEq (pw_succ (Γ := Γ) (M * M) j₀)
  ipra_le sl u using rw [ex, em, ps]; ring

/-- `2j M² P_{j−1} + M^{2j} ≤ (2j + 1) P_j + 2j M^{2j}` for `j = j₀ + 1`. -/
theorem rec_lo (j₀ M : PTm n) :
    Γ ⊢[PRAAx] le (two * succ j₀ * (M * M) * Ps j₀ M M + pw (M * M) (succ j₀))
      (succ (two * succ j₀) * Ps (succ j₀) M M + two * succ j₀ * pw (M * M) (succ j₀)) := by
  have l := l_all (Γ := Γ) (k := M) j₀ (le_refl M)
  have ex := natEq (pw_succ (Γ := Γ) (xs M M) j₀)
  have em := natEq (monus_self (Γ := Γ) (M * M))
  have ps := natEq (pw_succ (Γ := Γ) (M * M) j₀)
  ipra_le sl l + 2 * (𝔞 j₀ + 1) * (𝔞 M * 𝔞 M) * 𝔞 (pw (xs M M) j₀) using rw [ex, em, ps]; ring

/-! ## The closed form `J_j = (2j)!!/(2j+1)!!` -/

open LeanProofs.IPRA.Analysis.WallisFinite (da db da_zero db_zero da_succ db_succ)

/-- `P_0 = M`. -/
theorem P_zero (M : PTm n) : Γ ⊢[PRAAx] Ps zero M M ≐ M * one := by
  refine LeanProofs.IPRA.Probability.Variance.sum_const_of Pb M one (pairT zero M) (.allI (.impI ?_))
  simp only [shift_pairT]
  have e0 : Syn.shift (zero : PTm n) = zero := by simp [Syn.shift]
  have e1 : Syn.shift (one : PTm n) = one := by simp [Syn.shift]
  rw [e0, e1]
  exact (inst_Pb _ _ _).eqTrans (pw_zero _)

/-- `|P_j/M^{2j+1} − (2j)!!/(2j+1)!!| ≤ 2j/M`, cleared by `(2j+1)!! = da (j+1)`:
`da (j+1) · P_j ≤ db j · M^{2j+1} + (j+1) · da (j+1) · M^{2j}` and
`db j · M^{2j+1} ≤ da (j+1) · P_j + 2j · da (j+1) · M^{2j}`. -/
abbrev QInv (j M : PTm n) : Fm PTm n :=
  le (da (succ j) * Ps j M M) (db j * (M * pw (M * M) j) + succ j * (da (succ j) * pw (M * M) j)) ⋏
    le (db j * (M * pw (M * M) j)) (da (succ j) * Ps j M M + two * j * (da (succ j) * pw (M * M) j))

theorem q_base (M : PTm n) : Γ ⊢[PRAAx] QInv zero M := by
  have a1 := natEq (da_succ (Γ := Γ) zero)
  have a0 := natEq (da_zero (Γ := Γ)); have b0 := natEq (db_zero (Γ := Γ))
  have p0 := natEq (P_zero (Γ := Γ) M); have pz := natEq (pw_zero (Γ := Γ) (M * M))
  refine .andI ?_ ?_
  · ipra_le 1 using rw [a1, a0, b0, p0, pz]; ring
  · ipra_le 0 using rw [a1, a0, b0, p0, pz]; ring

theorem q_step {j M : PTm n} (ih : Γ ⊢[PRAAx] QInv j M) : Γ ⊢[PRAAx] QInv (succ j) M := by
  have ihU := Prf.andE₁ ih; have ihL := Prf.andE₂ ih
  have ru := rec_up (Γ := Γ) j M; have rl := rec_lo (Γ := Γ) j M
  have a2 := natEq (da_succ (Γ := Γ) (succ j)); have b1 := natEq (db_succ (Γ := Γ) j)
  have ps := natEq (pw_succ (Γ := Γ) (M * M) j)
  refine .andI ?_ ?_
  · ipra_le 𝔞 (da (succ j)) * sl ru + (2 * 𝔞 j + 2) * (𝔞 M * 𝔞 M) * sl ihU +
        (2 * 𝔞 j + 2) * 𝔞 (da (succ j)) * 𝔞 (pw (M * M) (succ j)) using
      rw [a2, b1, ps]; ring
  · ipra_le (2 * 𝔞 j + 2) * (𝔞 M * 𝔞 M) * sl ihL + 𝔞 (da (succ j)) * sl rl +
        (4 * 𝔞 j + 5) * 𝔞 (da (succ j)) * 𝔞 (pw (M * M) (succ j)) using
      rw [a2, b1, ps]; ring

/-- Variables: `0 = j` (induction), `1 = M`. -/
private abbrev qF : Fm PTm 2 := QInv (var 0) (var 1)

private theorem q₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] qF := by
  refine ind _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
  · simp only [Fm.subst_and, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul,
      Syn.subst_var, Syn.inst_zero, Syn.inst_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact q_base _
  · simp only [Fm.subst_and, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul,
      Syn.subst_var, Syn.repl_zero, repl_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact q_step Prf.hyp0

/-- `eq:piapprox`/`eq:Jrec` in closed form: the left Riemann sum of `(1 − t²)^j` on `M` cells is within
`2j/M` of `(2j)!!/(2j+1)!!`. -/
theorem even_power_integral (j M : PTm n) : Γ ⊢[PRAAx] QInv j M := by
  have h := inst (Γ := Γ) q₀ (![j, M] : Fin 2 → PTm n)
  simp at h
  exact h

/-- Variables: `0 = j`, `1 = M`. The closed sentence. -/
theorem even_power_integral_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 qF :=
  closeUniv 2 q₀

end LeanProofs.IPRA.Analysis.EvenPowerIntegrals
