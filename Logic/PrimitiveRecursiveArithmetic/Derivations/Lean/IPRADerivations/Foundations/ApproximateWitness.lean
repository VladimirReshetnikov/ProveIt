import IPRADerivations.Probability.FiniteLaws
import IPRADerivations.Core.SearchParameters
import IPRADerivations.Core.InductionTactic
import IPRADerivations.Core.Header

/-!
# Finite argmin and approximate witnesses

Packet: `foundations/ipra_finite_use_framework_2026-11-15_v2`,
`sections/09_compactness.tex`, Theorem `thm:approx-witness`.

The candidate indices are `0, …, K`, so the finite family is nonempty.
`argmin` is primitive recursive and selects the least index attaining the
running minimum. The approximate-witness theorem retains the coverage,
modulus and two evaluation-error bounds as explicit object-theory premises.
Residuals and errors are natural numerators over a common positive rational
denominator, supplied by the application.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.ApproximateWitness

open_ipra
open LeanProofs.IPRA.Probability.FiniteLaws (Mn mnF mn_zero mn_succ mn_le)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (monus_succ_of_lt)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Keep the old index except at a strict decrease of the running minimum.
The step variables are `0 = k`, `1 = previous index`, `2 = parameter`. -/
def attainingStep (score : PTm 2) : PTm 3 :=
  var 1 + sg (monus (Mn score (var 0) (var 2))
      (Syn.subst ![succ (var 0), var 2] score)) * monus (succ (var 0)) (var 1)

abbrev attainingF (score : PTm 2) : PR 2 := rec2 zero (attainingStep score)

/-- An explicit index attaining `min_{i≤K} score(i, x)`. -/
abbrev attaining (score : PTm 2) (K x : PTm n) : PTm n := ap2 (attainingF score) K x

theorem attaining_zero (score : PTm 2) (x : PTm n) :
    Γ ⊢[PRAAx] attaining score zero x ≐ zero := by
  simpa using rec2_zero (Γ := Γ) zero (attainingStep score) x

private theorem step_score (score : PTm 2) (k previous x : PTm n) :
    Syn.subst ![k, previous, x] (Syn.subst ![succ (var 0), var 2] score) =
      inst2 score (succ k) x := by
  simp only [inst2, Syn.subst_subst]
  congr 1
  funext i
  fin_cases i <;> simp

theorem attaining_succ (score : PTm 2) (K x : PTm n) :
    Γ ⊢[PRAAx] attaining score (succ K) x ≐ attaining score K x +
      sg (monus (Mn score K x) (inst2 score (succ K) x)) * monus (succ K) (attaining score K x) := by
  have h := rec2_succ (Γ := Γ) zero (attainingStep score) K x
  have e : Syn.subst ![K, attaining score K x, x] (attainingStep score) =
      attaining score K x + sg (monus (Mn score K x) (inst2 score (succ K) x)) *
        monus (succ K) (attaining score K x) := by
    simp only [attainingStep, PTm.subst_add, PTm.subst_mul, PTm.subst_monus,
      step_score, subst_ap2, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
  rw [e] at h
  exact h

private abbrev attainingFormula (score : PTm 2) : Fm PTm 2 :=
  le (attaining score (var 0) (var 1)) (var 0) ⋏
    (inst2 score (attaining score (var 0) (var 1)) (var 1) ≐ Mn score (var 0) (var 1))

private theorem attaining_open (score : PTm 2) :
    ([] : List (Fm PTm 2)) ⊢[PRAAx] attainingFormula score := by
  ipra_ind (⟨le_QF _ _, trivial⟩) [attainingFormula, subst_le, subst_ap2, subst_inst2]
  · have a := attaining_zero (Γ := ([] : List (Fm PTm 1))) score (var 0)
    exact .andI (le_congr a.eqSymm (.eqRefl _) (le_refl _))
      ((congrInst2 score a (.eqRefl _)).eqTrans (mn_zero score _).eqSymm)
  · let Δ : List (Fm PTm 2) := [attainingFormula score]
    have hBound : Δ ⊢[PRAAx] le (attaining score (var 0) (var 1)) (var 0) :=
      Prf.andE₁ Prf.hyp0
    have hValue : Δ ⊢[PRAAx] inst2 score (attaining score (var 0) (var 1)) (var 1) ≐
        Mn score (var 0) (var 1) := Prf.andE₂ Prf.hyp0
    have step := attaining_succ (Γ := Δ) score (var 0) (var 1)
    have minimumStep := mn_succ (Γ := Δ) score (var 0) (var 1)
    refine .orE (lt_or_le (inst2 score (succ (var 0)) (var 1)) (Mn score (var 0) (var 1))) ?_ ?_
    · let C := lt (inst2 score (succ (var 0)) (var 1)) (Mn score (var 0) (var 1)) :: Δ
      have h : C ⊢[PRAAx] lt (inst2 score (succ (var 0)) (var 1)) (Mn score (var 0) (var 1)) := Prf.hyp0
      have bit : C ⊢[PRAAx] sg (monus (Mn score (var 0) (var 1))
          (inst2 score (succ (var 0)) (var 1))) ≐ one :=
        (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (monus_succ_of_lt h))).eqTrans (sg_succ _)
      have a : C ⊢[PRAAx] attaining score (succ (var 0)) (var 1) ≐ succ (var 0) :=
        step.wk.eqTrans ((congrAdd (.eqRefl _) ((congrMul bit (.eqRefl _)).eqTrans (one_mul _))).eqTrans
          (eq_add_of_le (le_trans hBound.wk (le_succ_self _))).eqSymm)
      have v : C ⊢[PRAAx] Mn score (succ (var 0)) (var 1) ≐ inst2 score (succ (var 0)) (var 1) :=
        minimumStep.wk.eqTrans ((congrMonus (eq_add_of_le (le_of_lt h)) (.eqRefl _)).eqTrans (add_monus _ _))
      exact .andI (le_congr a.eqSymm (.eqRefl _) (le_refl _))
        ((congrInst2 score a (.eqRefl _)).eqTrans v.eqSymm)
    · let C := le (Mn score (var 0) (var 1)) (inst2 score (succ (var 0)) (var 1)) :: Δ
      have h : C ⊢[PRAAx] le (Mn score (var 0) (var 1)) (inst2 score (succ (var 0)) (var 1)) := Prf.hyp0
      have bit : C ⊢[PRAAx] sg (monus (Mn score (var 0) (var 1))
          (inst2 score (succ (var 0)) (var 1))) ≐ zero :=
        (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) h)).eqTrans sg_zero
      have a : C ⊢[PRAAx] attaining score (succ (var 0)) (var 1) ≐ attaining score (var 0) (var 1) :=
        step.wk.eqTrans ((congrAdd (.eqRefl _) ((congrMul bit (.eqRefl _)).eqTrans (zero_mul _))).eqTrans (add_zero _))
      have v : C ⊢[PRAAx] Mn score (succ (var 0)) (var 1) ≐ Mn score (var 0) (var 1) :=
        minimumStep.wk.eqTrans ((congrMonus (.eqRefl _) h).eqTrans (monus_zero _))
      exact .andI (le_congr a.eqSymm (.eqRefl _) (le_trans hBound.wk (le_succ_self _)))
        ((congrInst2 score a (.eqRefl _)).eqTrans (hValue.wk.eqTrans v.eqSymm))

theorem attaining_spec (score : PTm 2) (K x : PTm n) :
    Γ ⊢[PRAAx] le (attaining score K x) K ⋏
      (inst2 score (attaining score K x) x ≐ Mn score K x) := by
  have h := inst (Γ := Γ) (attaining_open score) (![K, x] : Fin 2 → PTm n)
  simpa using h

/-- The search body vanishes exactly at the minimum value. Its parameters
are the original data and the computed running minimum. -/
def minimumTest (score : PTm 2) : PTm 3 :=
  monus (inst2 score (var 0) (var 1)) (var 2) +
    monus (var 2) (inst2 score (var 0) (var 1))

/-- The first index attaining the minimum on `0, …, K`. -/
def argmin (score : PTm 2) (K x : PTm n) : PTm n :=
  Search.Finite.mu (minimumTest score) (succ K) ![x, Mn score K x]

@[simp] theorem subst_argmin {m : ℕ} (score : PTm 2) (K x : PTm n) (σ : Fin n → PTm m) :
    Syn.subst σ (argmin score K x) = argmin score (Syn.subst σ K) (Syn.subst σ x) := by
  simp only [argmin, Search.Finite.subst_mu, subst_ap2, ConciseIPRA.PTm.subst_succ]
  congr 2
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => cases i using Fin.cases with
    | zero => exact subst_ap2 σ (mnF score) K x
    | succ i => exact i.elim0

@[simp] theorem minimumTest_at (score : PTm 2) (i x minimum : PTm n) :
    Search.Finite.applyBody (minimumTest score) i ![x, minimum] =
      monus (inst2 score i x) minimum + monus minimum (inst2 score i x) := by
  simp only [minimumTest, Search.Finite.applyBody, PTm.subst_add, PTm.subst_monus,
    subst_inst2, Syn.subst_var, Fin.cases_zero, Fin.cases_succ,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, finCases_one, finCases_two]

private theorem test_zero (score : PTm 2) {i x minimum : PTm n}
    (h : Γ ⊢[PRAAx] inst2 score i x ≐ minimum) :
    Γ ⊢[PRAAx] Search.Finite.applyBody (minimumTest score) i ![x, minimum] ≐ zero := by
  rw [minimumTest_at]
  exact (congrAdd ((congrMonus h (.eqRefl _)).eqTrans (monus_self _))
    ((congrMonus (.eqRefl _) h).eqTrans (monus_self _))).eqTrans (add_zero _)

private theorem value_of_test_zero (score : PTm 2) {i x minimum : PTm n}
    (h : Γ ⊢[PRAAx] Search.Finite.applyBody (minimumTest score) i ![x, minimum] ≐ zero) :
    Γ ⊢[PRAAx] inst2 score i x ≐ minimum := by
  rw [minimumTest_at] at h
  exact le_antisymm (add_eq_zero_left h) (add_eq_zero_left ((add_comm _ _).eqTrans h))

/-- The computed least minimizer lies in range and attains the running minimum. -/
theorem argmin_spec (score : PTm 2) (K x : PTm n) :
    Γ ⊢[PRAAx] le (argmin score K x) K ⋏
      (inst2 score (argmin score K x) x ≐ Mn score K x) := by
  have a := attaining_spec (Γ := Γ) score K x
  have found := Search.Finite.search_found (test_zero score (Prf.andE₂ a))
    (lt_of_le_of_lt (Prf.andE₁ a) (le_refl (succ K)))
  have hBound : Γ ⊢[PRAAx] le (argmin score K x) K :=
    (succ_monus_succ _ _).eqSymm.eqTrans (Prf.andE₁ found)
  exact .andI hBound (value_of_test_zero score (Prf.andE₁ (Prf.andE₂ found)))

/-- Every candidate's score is at least the score at the selected index. -/
theorem argmin_minimal (score : PTm 2) {K i x : PTm n} (hi : Γ ⊢[PRAAx] le i K) :
    Γ ⊢[PRAAx] le (inst2 score (argmin score K x) x) (inst2 score i x) :=
  le_congr (Prf.andE₂ (argmin_spec score K x)).eqSymm (.eqRefl _) (mn_le score hi)

/-- Among all indices attaining the minimum, the selector returns the least. -/
theorem argmin_least (score : PTm 2) {K i x : PTm n} (hi : Γ ⊢[PRAAx] le i K)
    (hValue : Γ ⊢[PRAAx] inst2 score i x ≐ Mn score K x) :
    Γ ⊢[PRAAx] le (argmin score K x) i :=
  Prf.andE₂ (Prf.andE₂ (Search.Finite.search_found (test_zero score hValue)
    (lt_of_le_of_lt hi (le_refl (succ K)))))

/-- A tied candidate cannot occur before the selected minimizing index. -/
theorem argmin_tie (score : PTm 2) {K i x : PTm n} (hi : Γ ⊢[PRAAx] le i K)
    (hValue : Γ ⊢[PRAAx] inst2 score i x ≐ inst2 score (argmin score K x) x) :
    Γ ⊢[PRAAx] le (argmin score K x) i :=
  argmin_least score hi (hValue.eqTrans (Prf.andE₂ (argmin_spec score K x)))

/-- The range and attainment sentence, with `0 = K` and `1 = x`. -/
def argminSpecFormula (score : PTm 2) : Fm PTm 2 :=
  le (argmin score (var 0) (var 1)) (var 0) ⋏
    (inst2 score (argmin score (var 0) (var 1)) (var 1) ≐ Mn score (var 0) (var 1))

/-- Universally closed range and attainment of the primitive-recursive selector. -/
theorem argmin_spec_closed (score : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (argminSpecFormula score) :=
  closeUniv 2 (argmin_spec score (var 0) (var 1))

/-- The minimality sentence, with `0 = K`, `1 = i`, and `2 = x`. -/
def argminMinimalFormula (score : PTm 2) : Fm PTm 3 :=
  le (var 1) (var 0) ⟶
    le (inst2 score (argmin score (var 0) (var 2)) (var 2)) (inst2 score (var 1) (var 2))

/-- Universally closed comparison with every candidate in range. -/
theorem argmin_minimal_closed (score : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (argminMinimalFormula score) :=
  closeUniv 3 (.impI (argmin_minimal score Prf.hyp0))

/-- Substitution-compatible interpretation of the coverage relation. -/
def closeAt (close : Fm PTm 3) (y z x : PTm n) : Fm PTm n := close.subst ![y, z, x]

@[simp] theorem subst_closeAt {m : ℕ} (close : Fm PTm 3) (y z x : PTm n) (σ : Fin n → PTm m) :
    (closeAt close y z x).subst σ = closeAt close (Syn.subst σ y) (Syn.subst σ z) (Syn.subst σ x) := by
  simp only [closeAt, Fm.subst_subst]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Interpret the candidate-domain predicate with the problem data. -/
def domainAt (domain : Fm PTm 2) (y x : PTm n) : Fm PTm n := domain.subst ![y, x]

@[simp] theorem subst_domainAt {m : ℕ} (domain : Fm PTm 2) (y x : PTm n) (σ : Fin n → PTm m) :
    (domainAt domain y x).subst σ = domainAt domain (Syn.subst σ y) (Syn.subst σ x) := by
  simp only [domainAt, Fm.subst_subst]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The point of the net selected by the primitive-recursive least argmin. -/
def selected (net score : PTm 2) (K x : PTm n) : PTm n := inst2 net (argmin score K x) x

@[simp] theorem subst_selected {m : ℕ} (net score : PTm 2) (K x : PTm n) (σ : Fin n → PTm m) :
    Syn.subst σ (selected net score K x) = selected net score (Syn.subst σ K) (Syn.subst σ x) := by
  simp only [selected, subst_inst2, subst_argmin]

/-- Every enumerated net point is in the candidate domain. -/
def netDomain (domain : Fm PTm 2) (net : PTm 2) (K x : PTm n) : Fm PTm n :=
  .all (le (var 0) (Syn.shift K) ⟶
    domainAt domain (inst2 net (var 0) (Syn.shift x)) (Syn.shift x))

/-- A supplied domain witness is covered by some point of the finite net. -/
def coverage (domain : Fm PTm 2) (close : Fm PTm 3) (net : PTm 2)
    (K x witness : PTm n) : Fm PTm n :=
  domainAt domain witness x ⟶ .ex
    (le (var 0) (Syn.shift K) ⋏
      closeAt close (inst2 net (var 0) (Syn.shift x)) (Syn.shift witness) (Syn.shift x))

/-- Coverage within the given radius changes the residual by at most `ω`. -/
def modulus (close : Fm PTm 3) (net residual : PTm 2) (K x witness ω : PTm n) : Fm PTm n :=
  .all (le (var 0) (Syn.shift K) ⟶
    closeAt close (inst2 net (var 0) (Syn.shift x)) (Syn.shift witness) (Syn.shift x) ⟶
    le (inst2 residual (inst2 net (var 0) (Syn.shift x)) (Syn.shift x))
      (inst2 residual (Syn.shift witness) (Syn.shift x) + Syn.shift ω))

/-- The computed score overestimates the true residual by at most `error`. -/
def upperEvaluation (net score residual : PTm 2) (K x error : PTm n) : Fm PTm n :=
  .all (le (var 0) (Syn.shift K) ⟶
    le (inst2 score (var 0) (Syn.shift x))
      (inst2 residual (inst2 net (var 0) (Syn.shift x)) (Syn.shift x) + Syn.shift error))

/-- The true residual exceeds the computed score by at most `error`. -/
def lowerEvaluation (net score residual : PTm 2) (K x error : PTm n) : Fm PTm n :=
  .all (le (var 0) (Syn.shift K) ⟶
    le (inst2 residual (inst2 net (var 0) (Syn.shift x)) (Syn.shift x))
      (inst2 score (var 0) (Syn.shift x) + Syn.shift error))

private theorem subst_under_binder {m : ℕ} (σ : Fin n → PTm m) (t : PTm n) :
    Syn.subst (Syn.up σ) (Syn.shift t) = Syn.shift (Syn.subst σ t) := by
  simp [Syn.subst_shift, Syn.shift_subst]

@[simp] theorem subst_netDomain {m : ℕ} (domain : Fm PTm 2) (net : PTm 2)
    (K x : PTm n) (σ : Fin n → PTm m) :
    (netDomain domain net K x).subst σ = netDomain domain net (Syn.subst σ K) (Syn.subst σ x) := by
  simp only [netDomain, Fm.subst_all, Fm.subst_imp, subst_le, subst_domainAt,
    subst_inst2, subst_under_binder, Syn.subst_var, Syn.up_zero]

@[simp] theorem subst_upperEvaluation {m : ℕ} (net score residual : PTm 2)
    (K x error : PTm n) (σ : Fin n → PTm m) :
    (upperEvaluation net score residual K x error).subst σ =
      upperEvaluation net score residual (Syn.subst σ K) (Syn.subst σ x) (Syn.subst σ error) := by
  simp only [upperEvaluation, Fm.subst_all, Fm.subst_imp, subst_le, subst_inst2,
    PTm.subst_add, subst_under_binder, Syn.subst_var, Syn.up_zero]

@[simp] theorem subst_lowerEvaluation {m : ℕ} (net score residual : PTm 2)
    (K x error : PTm n) (σ : Fin n → PTm m) :
    (lowerEvaluation net score residual K x error).subst σ =
      lowerEvaluation net score residual (Syn.subst σ K) (Syn.subst σ x) (Syn.subst σ error) := by
  simp only [lowerEvaluation, Fm.subst_all, Fm.subst_imp, subst_le, subst_inst2,
    PTm.subst_add, subst_under_binder, Syn.subst_var, Syn.up_zero]

/-- `thm:approx-witness`, with both evaluation-error contributions displayed.
The coverage index, modulus and evaluation bounds are object-theory premises.
`close` may encode a distance bound, with the query and radius packed in `x`. -/
theorem approximate_witness (net score residual : PTm 2) (domain : Fm PTm 2) (close : Fm PTm 3)
    (K x witness η ω errorUpper errorLower : PTm n)
    (hWitness : Γ ⊢[PRAAx] le (inst2 residual witness x) η)
    (hWitnessDomain : Γ ⊢[PRAAx] domainAt domain witness x)
    (hNet : Γ ⊢[PRAAx] netDomain domain net K x)
    (hCoverage : Γ ⊢[PRAAx] coverage domain close net K x witness)
    (hModulus : Γ ⊢[PRAAx] modulus close net residual K x witness ω)
    (hEvaluationUpper : Γ ⊢[PRAAx] upperEvaluation net score residual K x errorUpper)
    (hEvaluationLower : Γ ⊢[PRAAx] lowerEvaluation net score residual K x errorLower) :
    Γ ⊢[PRAAx] le (argmin score K x) K ⋏
      (domainAt domain (selected net score K x) x ⋏
        le (inst2 residual (selected net score K x) x) (η + ω + errorUpper + errorLower)) := by
  have hIndex := Prf.andE₁ (argmin_spec (Γ := Γ) score K x)
  refine .andI hIndex (.andI ?_ ?_)
  · have h := Prf.allE (argmin score K x) hNet
    simp only [Fm.subst_imp, subst_le, subst_domainAt, subst_inst2,
      Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at h
    exact Prf.impE h hIndex
  have hSelected : Γ ⊢[PRAAx] le (inst2 residual (selected net score K x) x)
      (inst2 score (argmin score K x) x + errorLower) := by
    have h := Prf.allE (argmin score K x) hEvaluationLower
    simp only [Fm.subst_imp, subst_le, subst_inst2, subst_argmin, PTm.subst_add,
      Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at h
    exact Prf.impE h hIndex
  refine .exE (.impE hCoverage hWitnessDomain) ?_
  let coverCase := le (var 0) (Syn.shift K) ⋏
    closeAt close (inst2 net (var 0) (Syn.shift x)) (Syn.shift witness) (Syn.shift x)
  let Δ : List (Fm PTm (n + 1)) := coverCase :: Γ.map Fm.shift
  have hBound : Δ ⊢[PRAAx] le (var 0) (Syn.shift K) := Prf.andE₁ Prf.hyp0
  have hNear : Δ ⊢[PRAAx]
      closeAt close (inst2 net (var 0) (Syn.shift x)) (Syn.shift witness) (Syn.shift x) := Prf.andE₂ Prf.hyp0
  have hMinimal : Δ ⊢[PRAAx] le (inst2 score (argmin score (Syn.shift K) (Syn.shift x)) (Syn.shift x))
      (inst2 score (var 0) (Syn.shift x)) := argmin_minimal score hBound
  have hUpper := Prf.impE hEvaluationUpper.allOpen.wk hBound
  have hModulusAt := Prf.impE (Prf.impE hModulus.allOpen.wk hBound) hNear
  have hSelected' : Δ ⊢[PRAAx] le (inst2 residual (selected net score (Syn.shift K) (Syn.shift x)) (Syn.shift x))
      (inst2 score (argmin score (Syn.shift K) (Syn.shift x)) (Syn.shift x) + Syn.shift errorLower) := by
    have h := hSelected.shift.wk (ψ := coverCase)
    simpa only [Fm.shift, subst_le, subst_inst2, subst_selected, subst_argmin, PTm.subst_add, Syn.shift] using h
  have hWitness' : Δ ⊢[PRAAx] le (inst2 residual (Syn.shift witness) (Syn.shift x)) (Syn.shift η) := by
    have h := hWitness.shift.wk (ψ := coverCase)
    simpa only [Fm.shift, subst_le, subst_inst2, Syn.shift] using h
  have residualBound := le_trans hModulusAt (add_le_add_right (Syn.shift ω) hWitness')
  have evaluatedBound := le_trans hUpper (add_le_add_right (Syn.shift errorUpper) residualBound)
  have minimumBound := le_trans hMinimal evaluatedBound
  have result := le_trans hSelected' (add_le_add_right (Syn.shift errorLower) minimumBound)
  simpa only [Fm.shift, subst_le, subst_inst2, subst_selected, PTm.subst_add, Syn.shift, Δ, coverCase] using result


/-- The seven-variable approximate-witness contract. The variable slots are
`K`, problem data, witness, `η`, `ω`, upper error, and lower error. -/
def approximateFormula (net score residual : PTm 2) (domain : Fm PTm 2)
    (close : Fm PTm 3) : Fm PTm 7 :=
  le (inst2 residual (var 2) (var 1)) (var 3) ⟶
  domainAt domain (var 2) (var 1) ⟶
  netDomain domain net (var 0) (var 1) ⟶
  coverage domain close net (var 0) (var 1) (var 2) ⟶
  modulus close net residual (var 0) (var 1) (var 2) (var 4) ⟶
  upperEvaluation net score residual (var 0) (var 1) (var 5) ⟶
  lowerEvaluation net score residual (var 0) (var 1) (var 6) ⟶
    le (argmin score (var 0) (var 1)) (var 0) ⋏
      (domainAt domain (selected net score (var 0) (var 1)) (var 1) ⋏
        le (inst2 residual (selected net score (var 0) (var 1)) (var 1))
          (var 3 + var 4 + var 5 + var 6))

/-- Universally closed `thm:approx-witness`, with every application contract
retained as an object-language implication premise. -/
theorem approximate_witness_closed (net score residual : PTm 2) (domain : Fm PTm 2)
    (close : Fm PTm 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7 (approximateFormula net score residual domain close) := by
  refine closeUniv 7 (.impI (.impI (.impI (.impI (.impI (.impI (.impI ?_)))))))
  exact approximate_witness net score residual domain close
    (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)
    (Prf.hyp (by simp)) (Prf.hyp (by simp)) (Prf.hyp (by simp))
    (Prf.hyp (by simp)) (Prf.hyp (by simp)) (Prf.hyp (by simp)) (Prf.hyp (by simp))


/-- The source theorem from an existential approximate witness. The selector
uses only the finite net and its score table. The original witness is sealed
by existential elimination. -/
theorem approximate_witness_exists (net score residual : PTm 2) (domain : Fm PTm 2)
    (close : Fm PTm 3) (K x η ω errorUpper errorLower : PTm n)
    (hExists : Γ ⊢[PRAAx] .ex (domainAt domain (var 0) (Syn.shift x) ⋏
      le (inst2 residual (var 0) (Syn.shift x)) (Syn.shift η)))
    (hNet : Γ ⊢[PRAAx] netDomain domain net K x)
    (hCoverage : Γ ⊢[PRAAx] .all
      (coverage domain close net (Syn.shift K) (Syn.shift x) (var 0)))
    (hModulus : Γ ⊢[PRAAx] .all
      (domainAt domain (var 0) (Syn.shift x) ⟶
        modulus close net residual (Syn.shift K) (Syn.shift x) (var 0) (Syn.shift ω)))
    (hEvaluationUpper : Γ ⊢[PRAAx] upperEvaluation net score residual K x errorUpper)
    (hEvaluationLower : Γ ⊢[PRAAx] lowerEvaluation net score residual K x errorLower) :
    Γ ⊢[PRAAx] le (argmin score K x) K ⋏
      (domainAt domain (selected net score K x) x ⋏
        le (inst2 residual (selected net score K x) x) (η + ω + errorUpper + errorLower)) := by
  refine .exE hExists ?_
  let witnessCase := domainAt domain (var 0) (Syn.shift x) ⋏
    le (inst2 residual (var 0) (Syn.shift x)) (Syn.shift η)
  let Δ : List (Fm PTm (n + 1)) := witnessCase :: Γ.map Fm.shift
  have hWitness : Δ ⊢[PRAAx] witnessCase := Prf.hyp0
  have netValid : Δ ⊢[PRAAx] netDomain domain net (Syn.shift K) (Syn.shift x) := by
    have h := hNet.shift.wk (ψ := witnessCase)
    simpa only [Fm.shift, subst_netDomain, Syn.shift] using h
  have evaluationUpper : Δ ⊢[PRAAx]
      upperEvaluation net score residual (Syn.shift K) (Syn.shift x) (Syn.shift errorUpper) := by
    have h := hEvaluationUpper.shift.wk (ψ := witnessCase)
    simpa only [Fm.shift, subst_upperEvaluation, Syn.shift] using h
  have evaluationLower : Δ ⊢[PRAAx]
      lowerEvaluation net score residual (Syn.shift K) (Syn.shift x) (Syn.shift errorLower) := by
    have h := hEvaluationLower.shift.wk (ψ := witnessCase)
    simpa only [Fm.shift, subst_lowerEvaluation, Syn.shift] using h
  have result := approximate_witness net score residual domain close
    (Syn.shift K) (Syn.shift x) (var 0) (Syn.shift η) (Syn.shift ω)
    (Syn.shift errorUpper) (Syn.shift errorLower)
    (Prf.andE₂ hWitness) (Prf.andE₁ hWitness) netValid
    hCoverage.allOpen.wk (Prf.impE hModulus.allOpen.wk (Prf.andE₁ hWitness))
    evaluationUpper evaluationLower
  simpa only [Fm.shift, Fm.subst_and, subst_le, subst_domainAt, subst_selected,
    subst_argmin, subst_inst2, PTm.subst_add, Syn.shift, Δ, witnessCase] using result

/-- The existential-witness contract, with variable slots `K`, problem data,
`η`, `ω`, upper error, and lower error. -/
def approximateExistsFormula (net score residual : PTm 2) (domain : Fm PTm 2)
    (close : Fm PTm 3) : Fm PTm 6 :=
  .ex (domainAt domain (var 0) (Syn.shift (var 1)) ⋏
    le (inst2 residual (var 0) (Syn.shift (var 1))) (Syn.shift (var 2))) ⟶
  netDomain domain net (var 0) (var 1) ⟶
  .all (coverage domain close net (Syn.shift (var 0)) (Syn.shift (var 1)) (var 0)) ⟶
  .all (domainAt domain (var 0) (Syn.shift (var 1)) ⟶
    modulus close net residual (Syn.shift (var 0)) (Syn.shift (var 1)) (var 0) (Syn.shift (var 3))) ⟶
  upperEvaluation net score residual (var 0) (var 1) (var 4) ⟶
  lowerEvaluation net score residual (var 0) (var 1) (var 5) ⟶
    le (argmin score (var 0) (var 1)) (var 0) ⋏
      (domainAt domain (selected net score (var 0) (var 1)) (var 1) ⋏
        le (inst2 residual (selected net score (var 0) (var 1)) (var 1))
          (var 2 + var 3 + var 4 + var 5))

/-- Universally closed source theorem, retaining the existence premise. -/
theorem approximate_witness_exists_closed (net score residual : PTm 2) (domain : Fm PTm 2)
    (close : Fm PTm 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6 (approximateExistsFormula net score residual domain close) := by
  refine closeUniv 6 (.impI (.impI (.impI (.impI (.impI (.impI ?_))))))
  exact approximate_witness_exists net score residual domain close
    (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)
    (Prf.hyp (by simp)) (Prf.hyp (by simp)) (Prf.hyp (by simp))
    (Prf.hyp (by simp)) (Prf.hyp (by simp)) (Prf.hyp (by simp))

end LeanProofs.IPRA.Foundations.ApproximateWitness
