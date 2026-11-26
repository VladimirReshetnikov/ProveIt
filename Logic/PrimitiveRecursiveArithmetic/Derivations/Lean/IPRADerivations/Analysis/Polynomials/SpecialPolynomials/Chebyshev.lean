import IPRADerivations.Core.Pairing

/-!
# Chebyshev polynomials (`trigonometric_identities_ipra_2026-11-15`)

The packet defines `T_n` and `U_n` by the recurrences behind `cos (n x) = T_n (cos x)`
(`trigonometric_identities_ipra.tex`). For integer arguments `X ≥ 1`, written
`X = w + 1` so that `X² − 1 = w² + 2w` is a natural number, the pair
`(T_n, U_{n−1})` is defined by simultaneous primitive recursion:
`T₀ = 1`, `U₋₁ = 0`, `T_{n+1} = X T_n + (X² − 1) U_{n−1}`, `U_n = T_n + X U_{n−1}`.
Derived in iPRA, with `n` and `w` variables of the formulas:

* the Pell identity `T_n² = (X² − 1) U_{n−1}² + 1`, by induction on `n`;
* the three-term recurrence `T_{n+2} + T_n = 2X T_{n+1}`, i.e. `T_{n+2} = 2X T_{n+1} − T_n`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.Chebyshev

open_ipra

/-- Step variables: `0 = n`, `1 = T_n`, `2 = U_{n−1}`, `3 = w`. -/
abbrev stepT : PTm 4 := succ (var 3) * var 1 + (var 3 * var 3 + succ one * var 3) * var 2
abbrev stepU : PTm 4 := var 1 + succ (var 3) * var 2

variable {n : ℕ}

abbrev T (j : PTm n) (ps : Fin 1 → PTm n) : PTm n := sim₁ one zero stepT stepU j ps
abbrev U (j : PTm n) (ps : Fin 1 → PTm n) : PTm n := sim₂ one zero stepT stepU j ps

/-- Formula variables: `0 = n`, `1 = w`. -/
abbrev ps₂ : Fin 1 → PTm 2 := fun i => var i.succ

/-- `X² − 1 = w² + 2w`. -/
abbrev Dw : PTm 2 := var 1 * var 1 + succ one * var 1

/-- `T_n² = (X² − 1) U_{n−1}² + 1`. -/
abbrev pellFormula : Fm PTm 2 :=
  T (var 0) ps₂ * T (var 0) ps₂ ≐ Dw * (U (var 0) ps₂ * U (var 0) ps₂) + one

theorem chebyshev_pell : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 pellFormula := by
  refine closeUniv 2 (ind _ trivial ?_ ?_)
  · simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_sim₁, subst_sim₂, Syn.subst_var,
      Syn.inst_zero, Syn.inst_succ, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ,
      inst_two]
    refine withEq (sim₁_zero one zero stepT stepU (fun i : Fin 1 => var i)) fun e₁ => ?_
    refine withEq (sim₂_zero one zero stepT stepU (fun i : Fin 1 => var i)) fun e₂ => ?_
    apply deriveNat
    simp only [ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at e₁ e₂
    ipra_simps
    rw [e₁, e₂]; ring
  · simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_sim₁, subst_sim₂, Syn.subst_var,
      Syn.repl_zero, Syn.repl_succ, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ, repl_one]
    apply deriveNat
    have hm := natEq (Γ := [pellFormula]) Prf.hyp0
    have e₁ := natEq (sim₁_succ (Γ := [pellFormula]) one zero stepT stepU ps₂ (var 0))
    have e₂ := natEq (sim₂_succ (Γ := [pellFormula]) one zero stepT stepU ps₂ (var 0))
    simp only [PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero, Syn.subst_var, Fin.cases_zero, finCases_one, finCases_two,
      finCases_three, ps₂, Fin.succ_zero_eq_one] at e₁ e₂
    ipra_simps
    rw [e₁, e₂]
    linear_combination hm

/-- `T_{n+2} + T_n = 2X T_{n+1}`. -/
abbrev recurrenceFormula : Fm PTm 2 :=
  T (succ (succ (var 0))) ps₂ + T (var 0) ps₂ ≐ succ one * succ (var 1) * T (succ (var 0)) ps₂

theorem chebyshev_recurrence : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 recurrenceFormula := by
  refine closeUniv 2 (deriveNat ?_)
  have e₁ := natEq (sim₁_succ (Γ := []) one zero stepT stepU ps₂ (succ (var 0)))
  have e₂ := natEq (sim₂_succ (Γ := []) one zero stepT stepU ps₂ (var 0))
  have e₃ := natEq (sim₁_succ (Γ := []) one zero stepT stepU ps₂ (var 0))
  simp only [PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero,
    Syn.subst_var, Fin.cases_zero, finCases_one, finCases_two, finCases_three, ps₂,
    Fin.succ_zero_eq_one] at e₁ e₂ e₃
  ipra_simps
  linear_combination e₁ + (V [] 1 * V [] 1 + 2 * V [] 1) * e₂ - (V [] 1 + 1) * e₃

end LeanProofs.IPRA.Analysis.Chebyshev
