import IPRADerivations.Core.Parity

/-!
# Products and rational sequences (`bohr_mollerup_ipra`, `goldbach_euler_ipra`, `stirling_ipra`)

Theorems with the length of a product or sum as a variable of the iPRA formula,
derived by induction. Rational quantities are numerator–denominator pairs defined
by simultaneous recursion, and their equations are stated with denominators cleared.

* `bohr_mollerup_ipra_2026-11-15` (`paper/bohr_mollerup_ipra.tex`), the Pochhammer
  product `P_m(r) = ∏_{j<m} (r + j)`: its shift identity `r P_m(r + 1) = (r + m) P_m(r)`,
  the functional equation `Γ(r + 1) = r Γ(r)` at the level of finite products.
* `goldbach_euler_ipra` (`goldbach_euler_ipra.tex`), the telescoping sum
  `∑_{m=2}^{M} 1/(m(m − 1)) = 1 − 1/M`: with `S_j = ∑_{i=1}^{j} 1/(i(i + 1)) = p_j / q_j`,
  `p_j (j + 1) = q_j j`.
* `stirling_ipra` (`stirling_ipra.tex`), the Wallis product: with
  `w_m = ∏_{k=1}^{m} (2k)² / ((2k − 1)(2k + 1)) = N_m / D_m`,
  `N_m (2m + 1) ((2m)!)² = D_m 16^m (m!)⁴`, i.e. `w_m = 16^m (m!)⁴ / ((2m + 1)((2m)!)²)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.Products

open_ipra

/-- Substitution normal forms for this file. -/
macro "prod_subst" : tactic =>
  `(tactic| simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap2, subst_sim₁, subst_sim₂,
      Syn.subst_var, Syn.inst_zero, Syn.inst_succ, Syn.inst_one, Syn.repl_zero, Syn.repl_succ, repl_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ, PTm.subst_num])

/-! ## The Pochhammer product -/

section Pochhammer

variable {n : ℕ}

/-- `P_m(r) = ∏_{j<m} (r + j)`. -/
abbrev P (m r : PTm n) : PTm n := ap2 (prodF (var 1 + var 0)) m r

/-- `r P_m(r + 1) = (r + m) P_m(r)`; variables `0 = m`, `1 = r`. -/
abbrev pochhammerFormula : Fm PTm 2 :=
  var 1 * P (var 0) (succ (var 1)) ≐ (var 1 + var 0) * P (var 0) (var 1)

theorem pochhammer_shift : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 pochhammerFormula := by
  refine closeUniv 2 (ind _ trivial ?_ ?_)
  · prod_subst
    refine withEq (prod_zero (Γ := ([] : List (Fm PTm 1))) (var 1 + var 0) (succ (var 0))) fun e₁ => ?_
    refine withEq (prod_zero (Γ := ([] : List (Fm PTm 1))) (var 1 + var 0) (var 0)) fun e₂ => ?_
    apply deriveNat; ipra_simps; rw [e₁, e₂]; ring
  · prod_subst
    have h := natEq (Γ := [pochhammerFormula]) Prf.hyp0
    have e₁ := natEq (prod_succ (Γ := [pochhammerFormula]) (var 1 + var 0) (var 0) (succ (var 1)))
    have e₂ := natEq (prod_succ (Γ := [pochhammerFormula]) (var 1 + var 0) (var 0) (var 1))
    simp only [PTm.subst_add, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] at e₁ e₂
    apply deriveNat; ipra_simps
    rw [e₁, e₂]
    linear_combination (V _ 1 + 1 + V _ 0) * h

end Pochhammer

/-! ## The telescoping sum -/

section Telescoping

variable {n : ℕ}

/-- Step variables: `0 = j`, `1 = p_j`, `2 = q_j`, `3` unused:
`p_{j+1} = p_j (j + 1)(j + 2) + q_j`, `q_{j+1} = q_j (j + 1)(j + 2)`. -/
abbrev tStepP : PTm 4 := var 1 * (succ (var 0) * succ (succ (var 0))) + var 2
abbrev tStepQ : PTm 4 := var 2 * (succ (var 0) * succ (succ (var 0)))

abbrev p (j : PTm n) : PTm n := sim₁ zero one tStepP tStepQ j fun _ => zero
abbrev q (j : PTm n) : PTm n := sim₂ zero one tStepP tStepQ j fun _ => zero

/-- `p_j (j + 1) = q_j j`, i.e. `∑_{i=1}^{j} 1/(i(i + 1)) = j/(j + 1)`. -/
abbrev telescopeFormula : Fm PTm 1 := p (var 0) * succ (var 0) ≐ q (var 0) * var 0

theorem telescoping_sum : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 telescopeFormula := by
  refine closeUniv 1 (ind _ trivial ?_ ?_)
  · prod_subst
    refine withEq (sim₁_zero (Γ := ([] : List (Fm PTm 0))) zero one tStepP tStepQ
      (fun _ : Fin 1 => (zero : PTm 0))) fun e₁ => ?_
    refine withEq (sim₂_zero (Γ := ([] : List (Fm PTm 0))) zero one tStepP tStepQ
      (fun _ : Fin 1 => (zero : PTm 0))) fun e₂ => ?_
    apply deriveNat
    simp only [ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at e₁ e₂
    ipra_simps; rw [e₁, e₂]; ring
  · prod_subst
    have h := natEq (Γ := [telescopeFormula]) Prf.hyp0
    have e₁ := natEq (sim₁_succ (Γ := [telescopeFormula]) zero one tStepP tStepQ
      (fun _ : Fin 1 => (zero : PTm 1)) (var 0))
    have e₂ := natEq (sim₂_succ (Γ := [telescopeFormula]) zero one tStepP tStepQ
      (fun _ : Fin 1 => (zero : PTm 1)) (var 0))
    simp only [PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ, Syn.subst_var,
      Fin.cases_zero, finCases_one, finCases_two] at e₁ e₂
    apply deriveNat; ipra_simps
    rw [e₁, e₂]
    linear_combination (V _ 0 + 2) ^ 2 * h

end Telescoping

/-! ## The Wallis product -/

section Wallis

variable {n : ℕ}

/-- Step variables: `0 = m`, `1 = N_m`, `2 = D_m`, `3` unused:
`N_{m+1} = N_m (2m + 2)²`, `D_{m+1} = D_m (2m + 1)(2m + 3)`. -/
abbrev wStepN : PTm 4 := var 1 * (succ (succ (two * var 0)) * succ (succ (two * var 0)))
abbrev wStepD : PTm 4 := var 2 * (succ (two * var 0) * succ (succ (succ (two * var 0))))

abbrev Nw (m : PTm n) : PTm n := sim₁ one one wStepN wStepD m fun _ => zero
abbrev Dw (m : PTm n) : PTm n := sim₂ one one wStepN wStepD m fun _ => zero

/-- `x!`. -/
abbrev fact (x : PTm n) : PTm n := ap2 factF x zero

/-- `N_m (2m + 1) ((2m)!)² = D_m 16^m (m!)⁴`; variable `0 = m`. -/
abbrev wallisFormula : Fm PTm 1 :=
  Nw (var 0) * succ (two * var 0) * (fact (two * var 0) * fact (two * var 0))
    ≐ Dw (var 0) * pw (num 16) (var 0) *
      (fact (var 0) * fact (var 0) * (fact (var 0) * fact (var 0)))

theorem fact_two_succ {Γ : List (Fm PTm n)} (m : PTm n) :
    Γ ⊢[PRAAx] fact (two * succ m) ≐ fact (two * m) * succ (two * m) * succ (succ (two * m)) := by
  have e : Γ ⊢[PRAAx] two * succ m ≐ succ (succ (two * m)) := by
    ipra_ring
  refine (congrAp2 factF e (.eqRefl _)).eqTrans ((fact_succ _ _).eqTrans ?_)
  exact congrMul (fact_succ _ _) (.eqRefl _)

theorem wallis_product : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 wallisFormula := by
  refine closeUniv 1 (ind _ trivial ?_ ?_)
  · prod_subst
    refine withEq (sim₁_zero (Γ := ([] : List (Fm PTm 0))) one one wStepN wStepD
      (fun _ : Fin 1 => (zero : PTm 0))) fun e₁ => ?_
    refine withEq (sim₂_zero (Γ := ([] : List (Fm PTm 0))) one one wStepN wStepD
      (fun _ : Fin 1 => (zero : PTm 0))) fun e₂ => ?_
    refine withEq (congrAp2 (Γ := ([] : List (Fm PTm 0))) factF (mul_zero two) (.eqRefl zero))
      fun e₃ => ?_
    refine withEq (fact_zero (Γ := ([] : List (Fm PTm 0))) (zero : PTm 0)) fun e₄ => ?_
    refine withEq (pw_zero (Γ := ([] : List (Fm PTm 0))) (num 16)) fun e₅ => ?_
    apply deriveNat
    simp only [ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at e₁ e₂
    ipra_simps
    rw [e₁, e₂, e₃, e₄, e₅]; ring
  · prod_subst
    have h := natEq (Γ := [wallisFormula]) Prf.hyp0
    have e₁ := natEq (sim₁_succ (Γ := [wallisFormula]) one one wStepN wStepD
      (fun _ : Fin 1 => (zero : PTm 1)) (var 0))
    have e₂ := natEq (sim₂_succ (Γ := [wallisFormula]) one one wStepN wStepD
      (fun _ : Fin 1 => (zero : PTm 1)) (var 0))
    have e₃ := natEq (fact_two_succ (Γ := [wallisFormula]) (var 0))
    have e₄ := natEq (fact_succ (Γ := [wallisFormula]) (var 0) zero)
    have e₅ := natEq (pw_succ (Γ := [wallisFormula]) (num 16) (var 0))
    simp only [PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero,
      Syn.subst_var, Fin.cases_zero, finCases_one, finCases_two] at e₁ e₂
    apply deriveNat; ipra_simps
    rw [e₁, e₂, e₃, e₄, e₅]
    linear_combination ((2 * V _ 0 + 2) ^ 4 * (2 * V _ 0 + 3) * (2 * V _ 0 + 1)) * h

end Wallis

end LeanProofs.IPRA.Analysis.Products
