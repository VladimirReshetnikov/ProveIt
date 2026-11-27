import IPRADerivations.Core.Pairing
import IPRADerivations.Core.Header

/-!
# Two-term recurrences (`diophantine_ipra_2026-11-15`, `pell_ipra_2026-11-15`, `hurwitz_khinchin_ipra`)

Sequences defined by simultaneous primitive recursion (`Core.Pairing`), with
theorems quantified over the index inside iPRA and derived by induction.

* Pell powers (`diophantine_ipra_2026-11-15/paper/03_stormer.tex`): from a
  solution `(u, v)` of `u² = D v² + 1`, `x₀ = 1`, `y₀ = 0`,
  `x_{m+1} = u x_m + D v y_m`, `y_{m+1} = v x_m + u y_m`. Then for every `m`,
  `x_m² = D y_m² + 1`, and `x_{m+2} + x_m = 2u x_{m+1}`.
* Continued-fraction convergents (`hurwitz_khinchin_ipra/hurwitz.tex`,
  `pell_ipra_2026-11-15`), for every unary symbol `a` of partial quotients:
  `p_{j+1} = a_{j+1} p_j + p_{j−1}` and likewise `q`, with `p₀ = a₀`, `p₋₁ = 1`,
  `q₀ = 1`, `q₋₁ = 0`. The determinant `d_j = p_j q_{j−1} − p_{j−1} q_j` satisfies
  `d_{j+1} = −d_j` and `d_j² = 1`.
* The golden-ratio convergents (`hurwitz_khinchin_ipra`, `N = p² − pq − q²`): for
  consecutive Fibonacci numbers, `(F_{n+1}² − F_{n+1} F_n − F_n²)² = 1`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.Recurrences

open_ipra exports

/-- Substitution normal forms for the formulas of this file. -/
macro "rec_subst" : tactic =>
  `(tactic| simp only [Fm.subst_eq, Fm.subst_imp, PTm.subst_add, PTm.subst_mul, subst_ap1,
      subst_sim₁, subst_sim₂, Syn.subst_var, Syn.inst_zero, Syn.inst_succ, Syn.repl_zero,
      Syn.repl_succ, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ, inst_two, inst_three,
      repl_one, repl_two, repl_three, ZT.subst_eq, ZT.subst_add, ZT.subst_mul, ZT.subst_neg,
      ZT.subst_sub, ZT.subst_sq, ZT.subst_ofNat, ZT.subst_natLit, Fm.subst_and])

/-! ## Pell powers -/

section PellPowers

/-- Step variables: `0 = m`, `1 = x_m`, `2 = y_m`, `3 = u`, `4 = v`, `5 = D`. -/
abbrev pellX : PTm 6 := var 3 * var 1 + var 5 * (var 4 * var 2)
abbrev pellY : PTm 6 := var 4 * var 1 + var 3 * var 2

variable {n : ℕ}

/-- `x_m` and `y_m` for parameters `u, v, D`. -/
abbrev X (m : PTm n) (ps : Fin 3 → PTm n) : PTm n := sim₁ one zero pellX pellY m ps
abbrev Y (m : PTm n) (ps : Fin 3 → PTm n) : PTm n := sim₂ one zero pellX pellY m ps

variable {Γ : List (Fm PTm n)}

theorem X_succ (m : PTm n) (ps : Fin 3 → PTm n) :
    Γ ⊢[PRAAx] X (succ m) ps ≐ ps 0 * X m ps + ps 2 * (ps 1 * Y m ps) := by
  simpa only [PTm.subst_add, PTm.subst_mul, Syn.subst_var, Fin.cases_zero, finCases_one,
    finCases_two, finCases_three, finCases_four, finCases_five] using
    sim₁_succ (Γ := Γ) one zero pellX pellY ps m

theorem Y_succ (m : PTm n) (ps : Fin 3 → PTm n) :
    Γ ⊢[PRAAx] Y (succ m) ps ≐ ps 1 * X m ps + ps 0 * Y m ps := by
  simpa only [PTm.subst_add, PTm.subst_mul, Syn.subst_var, Fin.cases_zero, finCases_one,
    finCases_two, finCases_three, finCases_four, finCases_five] using
    sim₂_succ (Γ := Γ) one zero pellX pellY ps m

theorem X_zero (ps : Fin 3 → PTm n) : Γ ⊢[PRAAx] X zero ps ≐ one := by
  simpa using sim₁_zero (Γ := Γ) one zero pellX pellY ps

theorem Y_zero (ps : Fin 3 → PTm n) : Γ ⊢[PRAAx] Y zero ps ≐ zero := by
  simpa using sim₂_zero (Γ := Γ) one zero pellX pellY ps

theorem congrX (ps : Fin 3 → PTm n) {m m' : PTm n} (h : Γ ⊢[PRAAx] m ≐ m') : Γ ⊢[PRAAx] X m ps ≐ X m' ps := by
  simpa using Prf.eqCongr1 (Γ := Γ) (X (var 0) (fun i => Syn.shift (ps i))) h

theorem congrY (ps : Fin 3 → PTm n) {m m' : PTm n} (h : Γ ⊢[PRAAx] m ≐ m') : Γ ⊢[PRAAx] Y m ps ≐ Y m' ps := by
  simpa using Prf.eqCongr1 (Γ := Γ) (Y (var 0) (fun i => Syn.shift (ps i))) h

/-- One multiplication by a norm-one unit preserves the norm-one equation. -/
theorem norm_step (m : PTm n) (ps : Fin 3 → PTm n)
    (hU : Γ ⊢[PRAAx] ps 0 * ps 0 ≐ ps 2 * (ps 1 * ps 1) + one)
    (hm : Γ ⊢[PRAAx] X m ps * X m ps ≐ ps 2 * (Y m ps * Y m ps) + one) :
    Γ ⊢[PRAAx] X (succ m) ps * X (succ m) ps ≐ ps 2 * (Y (succ m) ps * Y (succ m) ps) + one := by
  have xs := natEq (X_succ (Γ := Γ) m ps)
  have ys := natEq (Y_succ (Γ := Γ) m ps)
  have unit := natEq hU
  have power := natEq hm
  apply deriveNat
  ipra_simps
  rw [xs, ys]
  linear_combination (Groth.ι (Q.mk Γ (X m ps)) ^ 2 - Groth.ι (Q.mk Γ (ps 2)) * Groth.ι (Q.mk Γ (Y m ps)) ^ 2) *
    unit + power

/-- Formula variables: `0 = m`, `1 = u`, `2 = v`, `3 = D`. -/
abbrev ps₄ : Fin 3 → PTm 4 := fun i => var i.succ

abbrev hypU : Fm PTm 4 := var 1 * var 1 ≐ var 3 * (var 2 * var 2) + one

/-- If `u² = D v² + 1` then `x_m² = D y_m² + 1`. -/
abbrev pellPowersFormula : Fm PTm 4 :=
  hypU ⟶ X (var 0) ps₄ * X (var 0) ps₄ ≐ var 3 * (Y (var 0) ps₄ * Y (var 0) ps₄) + one

theorem pell_powers : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 pellPowersFormula := by
  refine closeUniv 4 (ind _ ⟨trivial, trivial⟩ ?_ ?_)
  · rec_subst
    refine .impI ?_
    refine withEq (X_zero (fun i : Fin 3 => var i)) fun e₁ => ?_
    refine withEq (Y_zero (fun i : Fin 3 => var i)) fun e₂ => ?_
    apply deriveNat
    ipra_simps
    rw [e₁, e₂]; ring
  · rec_subst
    exact .impI (norm_step (var 0) ps₄ Prf.hyp0 (Prf.impE Prf.hyp1 Prf.hyp0))

/-- Instantiate the norm-one theorem at literal coded parameters and any internal power index. -/
theorem pell_powers_at (m : PTm n) (ps : Fin 3 → PTm n)
    (hU : Γ ⊢[PRAAx] ps 0 * ps 0 ≐ ps 2 * (ps 1 * ps 1) + one) :
    Γ ⊢[PRAAx] X m ps * X m ps ≐ ps 2 * (Y m ps * Y m ps) + one := by
  have law := inst (Γ := Γ) (Prf.allOpen (Prf.allOpen (Prf.allOpen (Prf.allOpen pell_powers)))) (Fin.cases m ps)
  simp only [pellPowersFormula, hypU, Fm.subst_imp, Fm.subst_eq, PTm.subst_mul, PTm.subst_add,
    subst_sim₁, subst_sim₂, Syn.subst_var, ps₄, Fin.cases_zero, Fin.cases_succ,
    finCases_one, finCases_two, finCases_three, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at law
  exact .impE law hU

/-- If `u² = D v² + 1` then `x_{m+2} + x_m = 2u x_{m+1}`. -/
abbrev pellRecurrenceFormula : Fm PTm 4 :=
  hypU ⟶ X (succ (succ (var 0))) ps₄ + X (var 0) ps₄ ≐ succ one * var 1 * X (succ (var 0)) ps₄

theorem pell_recurrence : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 pellRecurrenceFormula := by
  refine closeUniv 4 (.impI (deriveNat ?_))
  have hU := natEq (Γ := [hypU]) Prf.hyp0
  have e₁ := natEq (X_succ (Γ := [hypU]) (succ (var 0)) ps₄)
  have e₂ := natEq (Y_succ (Γ := [hypU]) (var 0) ps₄)
  have e₃ := natEq (X_succ (Γ := [hypU]) (var 0) ps₄)
  simp only [ps₄, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, fin_succ_two] at e₁ e₂ e₃
  ipra_simps
  linear_combination e₁ + (V _ 3 * V _ 2) * e₂ - V _ 1 * e₃ -
    Groth.ι (Q.mk [hypU] (X (var 0) ps₄)) * hU

end PellPowers

/-! ## Continued-fraction convergents -/

section ContinuedFractions

variable (a : PR 1) {n : ℕ}

/-- Step variables: `0 = j`, `1 = current`, `2 = previous`, `3 = unused`. -/
abbrev cfStep : PTm 4 := ap1 a (succ (var 0)) * var 1 + var 2

/-- `(p_j, p_{j−1})` and `(q_j, q_{j−1})`. -/
abbrev P (j : PTm n) : PTm n := sim₁ (ap1 a zero) one (cfStep a) (var 1) j fun _ => zero
abbrev P' (j : PTm n) : PTm n := sim₂ (ap1 a zero) one (cfStep a) (var 1) j fun _ => zero
abbrev Qc (j : PTm n) : PTm n := sim₁ one zero (cfStep a) (var 1) j fun _ => zero
abbrev Qc' (j : PTm n) : PTm n := sim₂ one zero (cfStep a) (var 1) j fun _ => zero

/-- The determinant `d_j = p_j q_{j−1} − p_{j−1} q_j`. -/
abbrev det (j : PTm n) : ZT n := ZT.ofNat (P a j * Qc' a j) - ZT.ofNat (P' a j * Qc a j)

/-- `d_{j+1} = −d_j`. -/
abbrev detStepFormula : Fm PTm 1 := ZT.eq (det a (succ (var 0))) (-det a (var 0))

theorem det_step : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 (detStepFormula a) := by
  refine closeUniv 1 (ZT.derive ?_)
  have e₁ := natEq (sim₁_succ (Γ := ([] : List (Fm PTm 1))) (ap1 a zero) one (cfStep a) (var 1) (fun _ : Fin 1 => (zero : PTm 1)) (var 0))
  have e₂ := natEq (sim₂_succ (Γ := ([] : List (Fm PTm 1))) (ap1 a zero) one (cfStep a) (var 1) (fun _ : Fin 1 => (zero : PTm 1)) (var 0))
  have e₃ := natEq (sim₁_succ (Γ := ([] : List (Fm PTm 1))) one zero (cfStep a) (var 1) (fun _ : Fin 1 => (zero : PTm 1)) (var 0))
  have e₄ := natEq (sim₂_succ (Γ := ([] : List (Fm PTm 1))) one zero (cfStep a) (var 1) (fun _ : Fin 1 => (zero : PTm 1)) (var 0))
  simp only [PTm.subst_add, PTm.subst_mul, subst_ap1, ConciseIPRA.PTm.subst_succ, Syn.subst_var,
    Fin.cases_zero, finCases_one, finCases_two] at e₁ e₂ e₃ e₄
  ipra_simps
  rw [e₁, e₂, e₃, e₄]
  ring

/-- `d_j² = 1`. -/
abbrev detSqFormula : Fm PTm 1 := ZT.eq (ZT.sq (det a (var 0))) (ZT.natLit 1)

theorem det_sq : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 (detSqFormula a) := by
  refine closeUniv 1 (ind _ trivial ?_ ?_)
  · rec_subst
    apply ZT.derive
    have e₁ := natEq (sim₁_zero (Γ := ([] : List (Fm PTm 0))) (ap1 a zero) one (cfStep a) (var 1) (fun _ : Fin 1 => zero))
    have e₂ := natEq (sim₂_zero (Γ := ([] : List (Fm PTm 0))) (ap1 a zero) one (cfStep a) (var 1) (fun _ : Fin 1 => zero))
    have e₃ := natEq (sim₁_zero (Γ := ([] : List (Fm PTm 0))) one zero (cfStep a) (var 1) (fun _ : Fin 1 => zero))
    have e₄ := natEq (sim₂_zero (Γ := ([] : List (Fm PTm 0))) one zero (cfStep a) (var 1) (fun _ : Fin 1 => zero))
    simp only [subst_ap1, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at e₁ e₂ e₃ e₄
    ipra_simps
    rw [e₁, e₂, e₃, e₄]
    ring
  · rec_subst
    apply ZT.derive
    have h := ZT.toZ_eq (Γ := [detSqFormula a]) Prf.hyp0
    have e₁ := natEq (sim₁_succ (Γ := [detSqFormula a]) (ap1 a zero) one (cfStep a) (var 1)
      (fun _ : Fin 1 => (zero : PTm 1)) (var 0))
    have e₂ := natEq (sim₂_succ (Γ := [detSqFormula a]) (ap1 a zero) one (cfStep a) (var 1)
      (fun _ : Fin 1 => (zero : PTm 1)) (var 0))
    have e₃ := natEq (sim₁_succ (Γ := [detSqFormula a]) one zero (cfStep a) (var 1)
      (fun _ : Fin 1 => (zero : PTm 1)) (var 0))
    have e₄ := natEq (sim₂_succ (Γ := [detSqFormula a]) one zero (cfStep a) (var 1)
      (fun _ : Fin 1 => (zero : PTm 1)) (var 0))
    simp only [PTm.subst_add, PTm.subst_mul, subst_ap1, ConciseIPRA.PTm.subst_succ, Syn.subst_var,
      Fin.cases_zero, finCases_one, finCases_two] at e₁ e₂ e₃ e₄
    ipra_simps
    rw [e₁, e₂, e₃, e₄]
    linear_combination h

end ContinuedFractions

/-! ## Fibonacci numbers -/

section Fibonacci

variable {n : ℕ}

/-- Step variables: `0 = n`, `1 = F_{n+1}`, `2 = F_n`, `3 = unused`. -/
abbrev fibStep : PTm 4 := var 1 + var 2

abbrev Fs (j : PTm n) : PTm n := sim₁ one zero fibStep (var 1) j fun _ => zero
abbrev F (j : PTm n) : PTm n := sim₂ one zero fibStep (var 1) j fun _ => zero

/-- `N = F_{n+1}² − F_{n+1} F_n − F_n²`. -/
abbrev normN (j : PTm n) : ZT n :=
  ZT.ofNat (Fs j * Fs j) - ZT.ofNat (Fs j * F j) - ZT.ofNat (F j * F j)

/-- `N² = 1`. -/
abbrev fibNormFormula : Fm PTm 1 := ZT.eq (ZT.sq (normN (var 0))) (ZT.natLit 1)

theorem fibonacci_norm : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 fibNormFormula := by
  refine closeUniv 1 (ind _ trivial ?_ ?_)
  · rec_subst
    apply ZT.derive
    have e₁ := natEq (sim₁_zero (Γ := ([] : List (Fm PTm 0))) one zero fibStep (var 1) (fun _ : Fin 1 => zero))
    have e₂ := natEq (sim₂_zero (Γ := ([] : List (Fm PTm 0))) one zero fibStep (var 1) (fun _ : Fin 1 => zero))
    simp only [ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at e₁ e₂
    ipra_simps
    rw [e₁, e₂]
    ring
  · rec_subst
    apply ZT.derive
    have h := ZT.toZ_eq (Γ := [fibNormFormula]) Prf.hyp0
    have e₁ := natEq (sim₁_succ (Γ := [fibNormFormula]) one zero fibStep (var 1) (fun _ : Fin 1 => (zero : PTm 1)) (var 0))
    have e₂ := natEq (sim₂_succ (Γ := [fibNormFormula]) one zero fibStep (var 1) (fun _ : Fin 1 => (zero : PTm 1)) (var 0))
    simp only [PTm.subst_add, Syn.subst_var, Fin.cases_zero, finCases_one, finCases_two] at e₁ e₂
    ipra_simps
    rw [e₁, e₂]
    linear_combination h

end Fibonacci

end LeanProofs.IPRA.DiophantineNumberTheory.Recurrences

export_ipra DiophantineNumberTheory.Recurrences (pellX pellY)
