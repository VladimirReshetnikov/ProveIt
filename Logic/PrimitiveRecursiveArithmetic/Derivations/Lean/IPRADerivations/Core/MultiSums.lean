import IPRADerivations.Core.BoundedSums

/-!
# Sums and products with two parameters

`∑_{i<N} f(i, p, q)` and `∏_{i<N} f(i, p, q)` for bodies `f : PTm 3` (variables `0 = i`,
`1 = p`, `2 = q`), with:

* the defining equations `sum2_zero`, `sum2_succ`, `prod2_zero`, `prod2_succ`;
* `prod2_congr_bounded`, `sum2_congr_bounded`: bodies that agree below the bound, possibly
  at different parameters, give equal products and sums;
* `prod2_mul`: `∏ f g = ∏ f · ∏ g`;
* `prod2_delta`: `∏_{j<N} F(j, q)^{[c = j]} = F(c, q)` for `c < N`;
* `sum2_delta`: `∑_{i<N} [i = c] = 1` for `c < N`;
* `prod2_one`: a product of ones is one.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Definitions -/

/-- `f(a, b, c)`. -/
def ap3 (f : PR 3) (a b c : PTm n) : PTm n := app f ![a, b, c]

@[simp] theorem subst_ap3 {m : ℕ} (σ : Fin n → PTm m) (f : PR 3) (a b c : PTm n) :
    Syn.subst σ (ap3 f a b c) = ap3 f (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ c) := by
  show app _ _ = app _ _; congr 1; funext i; fin_cases i <;> rfl

theorem congrAp3 (f : PR 3) {a a' b b' c c' : PTm n} (h₁ : Γ ⊢[PRAAx] a ≐ a') (h₂ : Γ ⊢[PRAAx] b ≐ b')
    (h₃ : Γ ⊢[PRAAx] c ≐ c') : Γ ⊢[PRAAx] ap3 f a b c ≐ ap3 f a' b' c' :=
  congrApp f fun i => by fin_cases i <;> assumption

/-- `body(i, p, q)`. -/
def inst3 (body : PTm 3) (i p q : PTm n) : PTm n := Syn.subst ![i, p, q] body

@[simp] theorem subst_inst3 {m : ℕ} (σ : Fin n → PTm m) (body : PTm 3) (i p q : PTm n) :
    Syn.subst σ (inst3 body i p q) = inst3 body (Syn.subst σ i) (Syn.subst σ p) (Syn.subst σ q) := by
  simp only [inst3, Syn.subst_subst]
  congr 1; funext j; fin_cases j <;> rfl

theorem congrInst3 (body : PTm 3) {i i' p p' q q' : PTm n} (h₁ : Γ ⊢[PRAAx] i ≐ i')
    (h₂ : Γ ⊢[PRAAx] p ≐ p') (h₃ : Γ ⊢[PRAAx] q ≐ q') : Γ ⊢[PRAAx] inst3 body i p q ≐ inst3 body i' p' q' :=
  Prf.eqCongr body fun j => by fin_cases j <;> assumption

/-- The body under the recursion: `0 ↦ 0`, `1 ↦ 2`, `2 ↦ 3`. -/
def bodyStep3 (body : PTm 3) : PTm 4 := Syn.subst ![var 0, var 2, var 3] body

def sum2F (body : PTm 3) : PR 3 := recDef zero (var 1 + bodyStep3 body)
def prod2F (body : PTm 3) : PR 3 := recDef (succ zero) (var 1 * bodyStep3 body)

private theorem cases_eq (y p q A : PTm n) :
    (Fin.cases y (Fin.cases A ![p, q]) : Fin 4 → PTm n) = ![y, A, p, q] := by
  funext i; fin_cases i <;> rfl

private theorem cases_eq' (y p q : PTm n) : (Fin.cases y ![p, q] : Fin 3 → PTm n) = ![y, p, q] := by
  funext i; fin_cases i <;> rfl

private theorem step_eq (body : PTm 3) (y p q A : PTm n) :
    Syn.subst ![y, A, p, q] (bodyStep3 body) = inst3 body y p q := by
  simp only [bodyStep3, inst3, Syn.subst_subst]
  congr 1; funext i; fin_cases i <;> rfl

theorem sum2_zero (body : PTm 3) (p q : PTm n) : Γ ⊢[PRAAx] ap3 (sum2F body) zero p q ≐ zero := by
  have h := rec_zero (Γ := Γ) zero (var 1 + bodyStep3 body) ![p, q]
  rw [cases_eq'] at h
  simp only [ConciseIPRA.PTm.subst_zero] at h
  exact h

theorem sum2_succ (body : PTm 3) (y p q : PTm n) :
    Γ ⊢[PRAAx] ap3 (sum2F body) (succ y) p q ≐ ap3 (sum2F body) y p q + inst3 body y p q := by
  have h := rec_succ (Γ := Γ) zero (var 1 + bodyStep3 body) y ![p, q]
  have e₁ : (Fin.cases (succ y) ![p, q] : Fin 3 → PTm n) = ![succ y, p, q] := cases_eq' _ _ _
  have e₂ : (Fin.cases y (Fin.cases (app (recDef zero (var 1 + bodyStep3 body)) (Fin.cases y ![p, q])) ![p, q])
      : Fin 4 → PTm n) = ![y, ap3 (sum2F body) y p q, p, q] := by funext i; fin_cases i <;> rfl
  rw [e₁, e₂, PTm.subst_add, step_eq] at h
  exact h

theorem prod2_zero (body : PTm 3) (p q : PTm n) : Γ ⊢[PRAAx] ap3 (prod2F body) zero p q ≐ one := by
  have h := rec_zero (Γ := Γ) (succ zero) (var 1 * bodyStep3 body) ![p, q]
  rw [cases_eq'] at h
  simp only [ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at h
  exact h

theorem prod2_succ (body : PTm 3) (y p q : PTm n) :
    Γ ⊢[PRAAx] ap3 (prod2F body) (succ y) p q ≐ ap3 (prod2F body) y p q * inst3 body y p q := by
  have h := rec_succ (Γ := Γ) (succ zero) (var 1 * bodyStep3 body) y ![p, q]
  have e₁ : (Fin.cases (succ y) ![p, q] : Fin 3 → PTm n) = ![succ y, p, q] := cases_eq' _ _ _
  have e₂ : (Fin.cases y (Fin.cases (app (recDef (succ zero) (var 1 * bodyStep3 body)) (Fin.cases y ![p, q])) ![p, q])
      : Fin 4 → PTm n) = ![y, ap3 (prod2F body) y p q, p, q] := by funext i; fin_cases i <;> rfl
  rw [e₁, e₂, PTm.subst_mul, step_eq] at h
  exact h

/-! ## Congruence below the bound -/

theorem prod2_congr_bounded (f g : PTm 3) (p q p' q' N : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst3 f (var 0) (Syn.shift p) (Syn.shift q) ≐ inst3 g (var 0) (Syn.shift p') (Syn.shift q')))) :
    Γ ⊢[PRAAx] ap3 (prod2F f) N p q ≐ ap3 (prod2F g) N p' q' := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      (ap3 (prod2F f) (var 0) (Syn.shift p) (Syn.shift q) ≐ ap3 (prod2F g) (var 0) (Syn.shift p') (Syn.shift q'))) := by
    refine PRA.qfInd _ ⟨le_QF _ _, trivial⟩ ?_ ?_
    · simpa using .impI ((prod2_zero (Γ := le zero N :: Γ) f p q).eqTrans (prod2_zero _ _ _).eqSymm)
    · simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap3, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift, ConciseIPRA.PTm.subst_zero]
      have hf := h.allOpen
      refine .impI ?_
      have hle : (le (succ (var 0)) (Syn.shift N) ::
          (le (var 0) (Syn.shift N) ⟶ (ap3 (prod2F f) (var 0) (Syn.shift p) (Syn.shift q) ≐
            ap3 (prod2F g) (var 0) (Syn.shift p') (Syn.shift q'))) ::
          Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift N) :=
        le_trans (le_succ_self _) Prf.hyp0
      refine (prod2_succ f (var 0) _ _).eqTrans (.eqTrans ?_ (prod2_succ g (var 0) _ _).eqSymm)
      exact congrMul (.impE Prf.hyp1 hle) (.impE hf.wk.wk Prf.hyp0)
  have h2 := Prf.allE N hall
  simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap3, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at h2
  exact .impE h2 (le_refl N)

theorem sum2_congr_bounded (f g : PTm 3) (p q p' q' N : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst3 f (var 0) (Syn.shift p) (Syn.shift q) ≐ inst3 g (var 0) (Syn.shift p') (Syn.shift q')))) :
    Γ ⊢[PRAAx] ap3 (sum2F f) N p q ≐ ap3 (sum2F g) N p' q' := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      (ap3 (sum2F f) (var 0) (Syn.shift p) (Syn.shift q) ≐ ap3 (sum2F g) (var 0) (Syn.shift p') (Syn.shift q'))) := by
    refine PRA.qfInd _ ⟨le_QF _ _, trivial⟩ ?_ ?_
    · simpa using .impI ((sum2_zero (Γ := le zero N :: Γ) f p q).eqTrans (sum2_zero _ _ _).eqSymm)
    · simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap3, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift, ConciseIPRA.PTm.subst_zero]
      have hf := h.allOpen
      refine .impI ?_
      have hle : (le (succ (var 0)) (Syn.shift N) ::
          (le (var 0) (Syn.shift N) ⟶ (ap3 (sum2F f) (var 0) (Syn.shift p) (Syn.shift q) ≐
            ap3 (sum2F g) (var 0) (Syn.shift p') (Syn.shift q'))) ::
          Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift N) :=
        le_trans (le_succ_self _) Prf.hyp0
      refine (sum2_succ f (var 0) _ _).eqTrans (.eqTrans ?_ (sum2_succ g (var 0) _ _).eqSymm)
      exact congrAdd (.impE Prf.hyp1 hle) (.impE hf.wk.wk Prf.hyp0)
  have h2 := Prf.allE N hall
  simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap3, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at h2
  exact .impE h2 (le_refl N)

/-! ## Products of products and of ones -/

/-- Variables: `0 = N`, `1 = p`, `2 = q`. -/
private abbrev prodMulF (f g : PTm 3) : Fm PTm 3 :=
  ap3 (prod2F (f * g)) (var 0) (var 1) (var 2) ≐ ap3 (prod2F f) (var 0) (var 1) (var 2) * ap3 (prod2F g) (var 0) (var 1) (var 2)

private theorem prod2_mul₀ (f g : PTm 3) : ([] : List (Fm PTm 3)) ⊢[PRAAx] prodMulF f g := by
  ipra_ind [subst_ap3]
  · refine (prod2_zero _ _ _).eqTrans ?_
    refine withEq (prod2_zero (Γ := []) f (var 0 : PTm 2) (var 1)) fun e₁ =>
      withEq (prod2_zero (Γ := []) g (var 0 : PTm 2) (var 1)) fun e₂ => ?_
    apply deriveNat; ipra_simps; rw [e₁, e₂]; ring
  · have e : inst3 (f * g) (var 0 : PTm 3) (var 1) (var 2) = inst3 f (var 0) (var 1) (var 2) * inst3 g (var 0) (var 1) (var 2) := by
      simp [inst3]
    refine (prod2_succ _ (var 0) _ _).eqTrans ?_
    rw [e]
    refine withEq Prf.hyp0 fun e₁ => withEq (prod2_succ f (var 0) (var 1) (var 2)) fun e₂ =>
      withEq (prod2_succ g (var 0) (var 1) (var 2)) fun e₃ => ?_
    apply deriveNat; ipra_simps; rw [e₁, e₂, e₃]; ring

theorem prod2_mul (f g : PTm 3) (N p q : PTm n) :
    Γ ⊢[PRAAx] ap3 (prod2F (f * g)) N p q ≐ ap3 (prod2F f) N p q * ap3 (prod2F g) N p q := by
  have h := inst (Γ := Γ) (prod2_mul₀ f g) (![N, p, q] : Fin 3 → PTm n)
  simpa using h

/-- Variables: `0 = N`, `1 = p`, `2 = q`. -/
private abbrev prodOneF : Fm PTm 3 := ap3 (prod2F one) (var 0) (var 1) (var 2) ≐ one

private theorem prod2_const_one₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] prodOneF := by
  ipra_ind [subst_ap3]
  · exact prod2_zero _ _ _
  · refine (prod2_succ _ (var 0) _ _).eqTrans ?_
    have e : inst3 (one : PTm 3) (var 0 : PTm 3) (var 1) (var 2) = one := by simp [inst3]
    rw [e]
    exact (congrMul Prf.hyp0 (.eqRefl _)).eqTrans (one_mul _)

/-- A product of ones below the bound is one. -/
theorem prod2_one (f : PTm 3) (p q N : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ (inst3 f (var 0) (Syn.shift p) (Syn.shift q) ≐ one))) :
    Γ ⊢[PRAAx] ap3 (prod2F f) N p q ≐ one := by
  refine (prod2_congr_bounded f one p q p q N ?_).eqTrans ?_
  · have e : inst3 (one : PTm 3) (var 0 : PTm (n + 1)) (Syn.shift p) (Syn.shift q) = one := by simp [inst3]
    rw [e]; exact h
  · have i := inst (Γ := Γ) prod2_const_one₀ (![N, p, q] : Fin 3 → PTm n)
    simpa using i

/-! ## Delta products and sums -/

/-- The body `F(j, q)^{[p = j]}`, for `F` over `0 = j`, `1 = q`. -/
def deltaBody (F : PTm 2) : PTm 3 := pw (Syn.subst ![var 0, var 2] F) (eqb (var 1) (var 0))

theorem inst3_delta (F : PTm 2) (j c x : PTm n) :
    inst3 (deltaBody F) j c x = pw (inst2 F j x) (eqb c j) := by
  simp only [inst3, deltaBody, inst2, subst_ap2, subst_eqb, Syn.subst_subst, Syn.subst_var]
  congr 2; funext i; fin_cases i <;> rfl

theorem eqb_zero_of_lt {a b : PTm n} (h : Γ ⊢[PRAAx] lt a b) : Γ ⊢[PRAAx] eqb a b ≐ zero :=
  eqb_of_ne (.impI (lt_irrefl a _ (lt_congr (.eqRefl _) Prf.hyp0.eqSymm h.wk)))

theorem eqb_zero_of_gt {a b : PTm n} (h : Γ ⊢[PRAAx] lt b a) : Γ ⊢[PRAAx] eqb a b ≐ zero :=
  eqb_of_ne (.impI (lt_irrefl b _ (lt_congr (.eqRefl _) Prf.hyp0 h.wk)))

/-- Variables: `0 = N`, `1 = c`, `2 = x`. -/
private abbrev deltaF (F : PTm 2) : Fm PTm 3 :=
  (lt (var 1) (var 0) ⟶ (ap3 (prod2F (deltaBody F)) (var 0) (var 1) (var 2) ≐ inst2 F (var 1) (var 2))) ⋏
    (le (var 0) (var 1) ⟶ (ap3 (prod2F (deltaBody F)) (var 0) (var 1) (var 2) ≐ one))

private theorem delta₀ (F : PTm 2) : ([] : List (Fm PTm 3)) ⊢[PRAAx] deltaF F := by
  ipra_ind (⟨⟨lt_QF _ _, trivial⟩, ⟨le_QF _ _, trivial⟩⟩) [subst_lt, subst_le, subst_ap3, subst_inst2]
  · exact .andI (.impI (lt_zero_absurd _ Prf.hyp0)) (.impI (prod2_zero _ _ _))
  · have s := prod2_succ (Γ := [deltaF F]) (deltaBody F) (var 0) (var 1) (var 2)
    rw [inst3_delta] at s
    have ih₁ : [deltaF F] ⊢[PRAAx] (lt (var 1) (var 0) ⟶
        (ap3 (prod2F (deltaBody F)) (var 0) (var 1) (var 2) ≐ inst2 F (var 1) (var 2))) := Prf.andE₁ Prf.hyp0
    have ih₂ : [deltaF F] ⊢[PRAAx] (le (var 0) (var 1) ⟶
        (ap3 (prod2F (deltaBody F)) (var 0) (var 1) (var 2) ≐ one)) := Prf.andE₂ Prf.hyp0
    refine .andI (.impI ?_) (.impI ?_)
    · -- `c < N + 1`: `c < N` or `c = N`.
      refine .orE (lt_succ_cases Prf.hyp0) ?_ ?_
      · have z := eqb_zero_of_lt (Prf.hyp0 : (lt (var 1) (var 0) :: lt (var 1) (succ (var 0)) :: [deltaF F]) ⊢[PRAAx] _)
        refine s.wk.wk.eqTrans ((congrMul (.impE ih₁.wk.wk Prf.hyp0) ((congrAp2 powF z (.eqRefl _)).eqTrans
          (pw_zero _))).eqTrans ?_)
        exact (mul_comm _ _).eqTrans (one_mul _)
      · have o := eqb_of_eq (Prf.hyp0 : ((var 1 ≐ var 0) :: lt (var 1) (succ (var 0)) :: [deltaF F]) ⊢[PRAAx] _)
        have p1 := Prf.impE ih₂.wk.wk (le_congr (.eqRefl _)
          (Prf.hyp0 : ((var 1 ≐ var 0) :: lt (var 1) (succ (var 0)) :: [deltaF F]) ⊢[PRAAx] var 1 ≐ var 0).eqSymm
          (le_refl (var 0)))
        refine s.wk.wk.eqTrans ((congrMul p1 ((congrAp2 powF o (.eqRefl _)).eqTrans (pw_one _))).eqTrans ?_)
        exact (one_mul _).eqTrans (congrInst2 F Prf.hyp0.eqSymm (.eqRefl _))
    · -- `N + 1 ≤ c`.
      have l : (le (succ (var 0)) (var 1) :: [deltaF F]) ⊢[PRAAx] le (var 0) (var 1) :=
        le_trans (le_succ_self _) Prf.hyp0
      have z := eqb_zero_of_gt (Prf.hyp0 : (le (succ (var 0)) (var 1) :: [deltaF F]) ⊢[PRAAx] lt (var 0) (var 1))
      refine s.wk.eqTrans ((congrMul (.impE ih₂.wk l) ((congrAp2 powF z (.eqRefl _)).eqTrans (pw_zero _))).eqTrans ?_)
      exact one_mul _

/-- `∏_{j<N} F(j, x)^{[c = j]} = F(c, x)` for `c < N`. -/
theorem prod2_delta (F : PTm 2) {N c x : PTm n} (h : Γ ⊢[PRAAx] lt c N) :
    Γ ⊢[PRAAx] ap3 (prod2F (deltaBody F)) N c x ≐ inst2 F c x := by
  have i := inst (Γ := Γ) (delta₀ F) (![N, c, x] : Fin 3 → PTm n)
  simp only [Fm.subst_and, Fm.subst_imp, Fm.subst_eq, subst_lt, subst_le, subst_ap3, subst_inst2,
    Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at i
  exact .impE (Prf.andE₁ i) h

/-- The body `[i = p]`. -/
abbrev indBody : PTm 3 := eqb (var 0) (var 1)

/-- Variables: `0 = N`, `1 = c`, `2 = x`. -/
private abbrev sumDeltaF : Fm PTm 3 :=
  (lt (var 1) (var 0) ⟶ (ap3 (sum2F indBody) (var 0) (var 1) (var 2) ≐ one)) ⋏
    (le (var 0) (var 1) ⟶ (ap3 (sum2F indBody) (var 0) (var 1) (var 2) ≐ zero))

private theorem sum_delta₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] sumDeltaF := by
  ipra_ind (⟨⟨lt_QF _ _, trivial⟩, ⟨le_QF _ _, trivial⟩⟩) [subst_lt, subst_le, subst_ap3]
  · exact .andI (.impI (lt_zero_absurd _ Prf.hyp0)) (.impI (sum2_zero _ _ _))
  · have s := sum2_succ (Γ := [sumDeltaF]) indBody (var 0) (var 1) (var 2)
    have e : inst3 indBody (var 0 : PTm 3) (var 1) (var 2) = eqb (var 0) (var 1) := by simp [inst3]
    rw [e] at s
    have ih₁ : [sumDeltaF] ⊢[PRAAx] (lt (var 1) (var 0) ⟶ (ap3 (sum2F indBody) (var 0) (var 1) (var 2) ≐ one)) :=
      Prf.andE₁ Prf.hyp0
    have ih₂ : [sumDeltaF] ⊢[PRAAx] (le (var 0) (var 1) ⟶ (ap3 (sum2F indBody) (var 0) (var 1) (var 2) ≐ zero)) :=
      Prf.andE₂ Prf.hyp0
    refine .andI (.impI ?_) (.impI ?_)
    · refine .orE (lt_succ_cases Prf.hyp0) ?_ ?_
      · have z := eqb_zero_of_gt (Prf.hyp0 : (lt (var 1) (var 0) :: lt (var 1) (succ (var 0)) :: [sumDeltaF]) ⊢[PRAAx] _)
        exact s.wk.wk.eqTrans ((congrAdd (.impE ih₁.wk.wk Prf.hyp0) z).eqTrans (add_zero _))
      · have o := eqb_of_eq (Prf.hyp0 : ((var 1 ≐ var 0) :: lt (var 1) (succ (var 0)) :: [sumDeltaF]) ⊢[PRAAx] _).eqSymm
        have p0 := Prf.impE ih₂.wk.wk (le_congr (.eqRefl _)
          (Prf.hyp0 : ((var 1 ≐ var 0) :: lt (var 1) (succ (var 0)) :: [sumDeltaF]) ⊢[PRAAx] var 1 ≐ var 0).eqSymm
          (le_refl (var 0)))
        exact s.wk.wk.eqTrans ((congrAdd p0 o).eqTrans (zero_add _))
    · have l : (le (succ (var 0)) (var 1) :: [sumDeltaF]) ⊢[PRAAx] le (var 0) (var 1) :=
        le_trans (le_succ_self _) Prf.hyp0
      have z := eqb_zero_of_lt (Prf.hyp0 : (le (succ (var 0)) (var 1) :: [sumDeltaF]) ⊢[PRAAx] lt (var 0) (var 1))
      exact s.wk.eqTrans ((congrAdd (.impE ih₂.wk l) z).eqTrans (add_zero _))

/-- `∑_{i<N} [i = c] = 1` for `c < N`. -/
theorem sum2_delta {N c x : PTm n} (h : Γ ⊢[PRAAx] lt c N) :
    Γ ⊢[PRAAx] ap3 (sum2F indBody) N c x ≐ one := by
  have i := inst (Γ := Γ) sum_delta₀ (![N, c, x] : Fin 3 → PTm n)
  simp only [Fm.subst_and, Fm.subst_imp, Fm.subst_eq, subst_lt, subst_le, subst_ap3,
    Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at i
  exact .impE (Prf.andE₁ i) h

end LeanProofs.IPRA
