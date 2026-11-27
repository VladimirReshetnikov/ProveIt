import IPRADerivations.Core.Parity

/-!
# Sums of indicators as bounded quantifiers

For a body term `f(i, x)`, the sum `S(N, x) = ∑_{i<N} f(i, x)` (`sumF`) is zero
exactly when every term below `N` is zero:

* `sum_zero_elim`: `S(N, x) = 0` and `i < N` give `f(i, x) = 0`;
* `sum_zero_of_all`: `∀ i, f(i, x) = 0` gives `S(N, x) = 0`.

So a quantifier-free statement about `S(N, x)` expresses a bounded universal
statement, and quantifier-free induction on `N` proves such statements. This is
how the descent proofs of `Algebra.CubeRootTwo` are organised.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Quantifier-free induction on the whole initial segment up to an object-language bound. -/
theorem qfIndAllUpTo (N : PTm n) {P : Fm PTm (n + 1)} (hP : P.QF)
    (base : Γ ⊢[PRAAx] P.subst (Syn.inst zero))
    (step : P :: Γ.map Fm.shift ⊢[PRAAx]
      lt (Syn.var 0) (Syn.shift N) ⟶ P.subst (Syn.repl (succ (Syn.var 0)))) :
    Γ ⊢[PRAAx] Fm.all (le (Syn.var 0) (Syn.shift N) ⟶ P) := by
  let bounded := le (Syn.var 0) (Syn.shift N) ⟶ P
  refine PRA.qfInd bounded ⟨le_QF _ _, hP⟩ ?_ ?_
  · simp only [bounded, Fm.subst_imp, subst_le, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
    exact .impI base.wk
  · simp only [bounded, Fm.subst_imp, subst_le, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
    refine .impI ?_
    have hi := le_trans (le_succ_self (Syn.var 0)) (Prf.hyp0 :
      le (succ (Syn.var 0)) (Syn.shift N) :: bounded :: Γ.map Fm.shift ⊢[PRAAx]
        le (succ (Syn.var 0)) (Syn.shift N))
    exact .impE (.impE (Prf.impI step).wk.wk (.impE Prf.hyp1 hi)) Prf.hyp0

/-- Instantiate bounded induction at any index proved to lie in the initial segment. -/
theorem qfIndAtMost {j N : PTm n} {P : Fm PTm (n + 1)} (hj : Γ ⊢[PRAAx] le j N) (hP : P.QF)
    (base : Γ ⊢[PRAAx] P.subst (Syn.inst zero))
    (step : P :: Γ.map Fm.shift ⊢[PRAAx]
      lt (Syn.var 0) (Syn.shift N) ⟶ P.subst (Syn.repl (succ (Syn.var 0)))) :
    Γ ⊢[PRAAx] P.subst (Syn.inst j) := by
  have atIndex := Prf.allE j (qfIndAllUpTo N hP base step)
  simp only [Fm.subst_imp, subst_le, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at atIndex
  exact .impE atIndex hj

/-- Induction up to an object-language bound, with successor steps needed only below it. -/
theorem qfIndUpTo (N : PTm n) {P : Fm PTm (n + 1)} (hP : P.QF)
    (base : Γ ⊢[PRAAx] P.subst (Syn.inst zero))
    (step : P :: Γ.map Fm.shift ⊢[PRAAx]
      lt (Syn.var 0) (Syn.shift N) ⟶ P.subst (Syn.repl (succ (Syn.var 0)))) :
    Γ ⊢[PRAAx] P.subst (Syn.inst N) :=
  qfIndAtMost (le_refl N) hP base step

/-- `body(i, x)`. -/
def inst2 (body : PTm 2) (i x : PTm n) : PTm n := Syn.subst ![i, x] body

@[simp] theorem subst_inst2 {m : ℕ} (σ : Fin n → PTm m) (body : PTm 2) (i x : PTm n) :
    Syn.subst σ (inst2 body i x) = inst2 body (Syn.subst σ i) (Syn.subst σ x) := by
  simp only [inst2, Syn.subst_subst, subst_vecCons, subst_vecEmpty]

theorem congrInst2 (body : PTm 2) {i i' x x' : PTm n} (h₁ : Γ ⊢[PRAAx] i ≐ i')
    (h₂ : Γ ⊢[PRAAx] x ≐ x') : Γ ⊢[PRAAx] inst2 body i x ≐ inst2 body i' x' :=
  Prf.eqCongr body fun j => by fin_cases j <;> assumption

theorem sum_succ' (body : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF body) (succ N) x ≐ ap2 (sumF body) N x + inst2 body N x :=
  sum_succ body N x

/-- A sum with bound one consists of the term at zero. -/
theorem sum_singleton (body : PTm 2) (x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF body) one x ≐ inst2 body zero x :=
  (sum_succ' body zero x).eqTrans
    ((congrAdd (sum_zero body x) (.eqRefl _)).eqTrans (zero_add _))

/-- A sum with bound two consists of the terms at zero and one. -/
theorem sum_two_terms (body : PTm 2) (x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF body) two x ≐ inst2 body zero x + inst2 body one x :=
  (sum_succ' body one x).eqTrans (congrAdd (sum_singleton body x) (.eqRefl _))

theorem lt_zero_absurd {i : PTm n} (φ : Fm PTm n) (h : Γ ⊢[PRAAx] lt i zero) : Γ ⊢[PRAAx] φ :=
  succ_ne_zero' φ ((monus_zero (succ i)).eqSymm.eqTrans h)

theorem lt_succ_cases {i N : PTm n} (h : Γ ⊢[PRAAx] lt i (succ N)) :
    Γ ⊢[PRAAx] lt i N ⋎ (i ≐ N) :=
  Order.lt_succ_cases h

theorem add_eq_zero_right {x y : PTm n} (h : Γ ⊢[PRAAx] x + y ≐ zero) : Γ ⊢[PRAAx] y ≐ zero :=
  add_eq_zero_left ((add_comm y x).eqTrans h)

/-! ## A summand is bounded by the sum -/

/-- Variables: `0 = M`, `1 = i`, `2 = x`. -/
private abbrev termLeF (f : PTm 2) : Fm PTm 3 :=
  lt (var 1) (var 0) ⟶ le (inst2 f (var 1) (var 2)) (ap2 (sumF f) (var 0) (var 2))

private theorem sum_term_le₀ (f : PTm 2) : ([] : List (Fm PTm 3)) ⊢[PRAAx] termLeF f := by
  ipra_ind (⟨lt_QF _ _, le_QF _ _⟩) [subst_le, subst_lt, subst_ap2, subst_inst2]
  · exact .impI (lt_zero_absurd _ Prf.hyp0)
  · refine .impI ?_
    refine le_congr (.eqRefl _) (sum_succ' f (var 0) (var 2)).eqSymm ?_
    refine .orE (lt_succ_cases Prf.hyp0) ?_ ?_
    · exact le_trans (.impE hyp2 Prf.hyp0) (le_add_right _ _)
    · exact le_congr (congrInst2 f Prf.hyp0.eqSymm (.eqRefl _)) (.eqRefl _) (le_add_left _ _)

/-- A summand below the finite bound is at most the whole sum. -/
theorem sum_term_le (f : PTm 2) {i M x : PTm n} (h : Γ ⊢[PRAAx] lt i M) :
    Γ ⊢[PRAAx] le (inst2 f i x) (ap2 (sumF f) M x) := by
  have t := inst (Γ := Γ) (sum_term_le₀ f) (![M, i, x] : Fin 3 → PTm n)
  simp only [Fm.subst_imp, subst_le, subst_lt, subst_ap2, subst_inst2, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, ConciseIPRA.PTm.subst_zero] at t
  exact .impE t h

/-- `S(N, x) = 0` and `i < N` give `f(i, x) = 0`. -/
theorem sum_zero_elim (body : PTm 2) {N i x : PTm n} (hS : Γ ⊢[PRAAx] ap2 (sumF body) N x ≐ zero)
    (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx] inst2 body i x ≐ zero :=
  (monus_zero _).eqSymm.eqTrans (le_congr (.eqRefl _) hS (sum_term_le body hi))

/-! ## Zero terms give a zero sum -/

/-- `∀ i < N, f(i, x) = 0` gives `S(N, x) = 0`. -/
theorem sum_zero_of_bounded (body : PTm 2) (x N : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ (inst2 body (var 0) (Syn.shift x) ≐ zero))) :
    Γ ⊢[PRAAx] ap2 (sumF body) N x ≐ zero := by
  let P : Fm PTm (n + 1) := ap2 (sumF body) (var 0) (Syn.shift x) ≐ zero
  have atBound : Γ ⊢[PRAAx] P.subst (Syn.inst N) := by
    refine qfIndUpTo N trivial ?_ ?_
    · simpa [P] using sum_zero (Γ := Γ) body x
    · simp only [P, Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_zero]
      refine .impI ((sum_succ' body (var 0) _).eqTrans ?_)
      exact (congrAdd Prf.hyp1 (.impE h.allOpen.wk.wk Prf.hyp0)).eqTrans (add_zero _)
  simpa [P] using atBound

/-- `∀ i, f(i, x) = 0` gives `S(N, x) = 0`. -/
theorem sum_zero_of_all (body : PTm 2) (x : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (inst2 body (var 0) (Syn.shift x) ≐ zero)) (N : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF body) N x ≐ zero := by
  apply sum_zero_of_bounded body x N
  exact .allI (.impI h.allOpen.wk)

end LeanProofs.IPRA
