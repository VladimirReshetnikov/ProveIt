import ConciseIPRA.NativeInherited

/-!
# One introduction rule that is stable under substitution

`GPrf` is the calculus of the package `Research/diagonal_guard`.  It has the
terms and formulas of the kernel and seven rules: hypothesis, the two
computation equations, transport in one term, `QE`, `DE`, and one
introduction

  `dI`: from `Γ, B(t, η) ⊢ B(t, S z)` with `z` fresh infer `D_{x,y} B`,

where `η = z` exactly when the matrix `B` is literally of the diagonal shape
`I(y, y; u.h) = I(y, y; v.k)`, and `η = 0` otherwise.  The test looks at the
matrix only, not at the witness, and substitution for the free variables
neither creates nor destroys the shape (`NFm.isDiag_subst`).  So, unlike the
single introduction of `NativeOneIntro`, this rule commutes with substitution
and `GPrf.subst` is a direct induction.

`gprf_iff_nprf` proves that `GPrf` derives the same sequents as the kernel.

* `D` by cases at a diagonal matrix: its base `B(t, 0)` computes to `0 = 0`,
  so the hypothesis of the case step can be cut and the progress step applies.
* `Q` by progress for an arbitrary equation `E(y) = (s = t)`: with the base
  `E(0)` retained and the diagonal lift
  `H(y) = (I(y, y; u.s) = I(y, y; u.t))`, the equation
  `sel(y, s(0), I(y, y; u.s(y))) = s(y)` holds unconditionally, by cases on `y`.
  It turns `H(z)` into `E(z)` by equational reasoning alone, the given step
  yields `E(S z)`, and one computation turns that into `H(S z)`.  Progress for
  `H` is primitive; `QE` at `S z` and `Q` by cases finish.

The step premise is used at its own variable; nothing is substituted into it.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

variable {n m : ℕ}

namespace Tm

/-- The term is the variable with index `0`. -/
def isV0 : {n : ℕ} → Tm n → Bool
  | _, .var i => i.val == 0
  | _, _ => false

/-- The term is an iterator whose counter and seed are the variable `0`. -/
def isDiag : {n : ℕ} → Tm n → Bool
  | _, .iter c a _ => c.isV0 && a.isV0
  | _, _ => false

theorem isV0_shift (x : Tm n) : (Syn.shift x).isV0 = false := by
  cases x with
  | var i => show ((Fin.succ i).val == 0) = false; simp
  | zero => rfl
  | succ t => rfl
  | iter c a h => rfl

theorem isV0_subst_up (τ : Fin n → Tm m) (c : Tm (n + 1)) :
    (Syn.subst (up τ) c).isV0 = c.isV0 := by
  cases c with
  | var i =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rw [show Syn.subst (up τ) (Tm.var j.succ) = Syn.shift (τ j) from Syn.up_succ τ j,
        isV0_shift]
      show false = ((Fin.succ j).val == 0)
      simp
  | zero => rfl
  | succ t => rfl
  | iter c a h => rfl

theorem isDiag_shift (x : Tm n) : (Syn.shift x).isDiag = false := by
  cases x with
  | var i => rfl
  | zero => rfl
  | succ t => rfl
  | iter c a h =>
    show ((Syn.shift c).isV0 && (Syn.shift a).isV0) = false
    rw [isV0_shift]; rfl

theorem isDiag_subst_up (τ : Fin n → Tm m) (s : Tm (n + 1)) :
    (Syn.subst (up τ) s).isDiag = s.isDiag := by
  cases s with
  | var i =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rw [show Syn.subst (up τ) (Tm.var j.succ) = Syn.shift (τ j) from Syn.up_succ τ j,
        isDiag_shift]
      rfl
  | zero => rfl
  | succ t => rfl
  | iter c a h =>
    show ((Syn.subst (up τ) c).isV0 && (Syn.subst (up τ) a).isV0) = (c.isV0 && a.isV0)
    rw [isV0_subst_up, isV0_subst_up]

theorem eq_var0 {c : Tm (n + 1)} (h : c.isV0 = true) : c = Tm.var 0 := by
  cases c with
  | var i =>
    have e : i = 0 := Fin.ext (by simpa [isV0] using h)
    rw [e]
  | zero => exact Bool.noConfusion h
  | succ t => exact Bool.noConfusion h
  | iter c a k => exact Bool.noConfusion h

end Tm

namespace NFm

/-- The matrix is literally of the shape `I(y, y; u.h) = I(y, y; v.k)`, where
`y` is the variable `0`. -/
def isDiag : {n : ℕ} → NFm n → Bool
  | _, .eq s t => s.isDiag && t.isDiag
  | _, _ => false

/-- The start of the introduction rule: the fresh variable at a diagonal
matrix, `0` otherwise. -/
def dstart (B : NFm (n + 2)) : Tm (n + 1) := if B.isDiag then Syn.var 0 else zero

/-- Substitution for the free variables preserves and reflects the diagonal
shape. -/
theorem isDiag_subst (B : NFm (n + 2)) (σ : Fin n → Tm m) :
    (B.subst (up (up σ))).isDiag = B.isDiag := by
  cases B with
  | eq s t =>
    show ((Syn.subst (up (up σ)) s).isDiag && (Syn.subst (up (up σ)) t).isDiag)
      = (s.isDiag && t.isDiag)
    rw [Tm.isDiag_subst_up, Tm.isDiag_subst_up]
  | Q B => rfl
  | D B => rfl

theorem dstart_subst (B : NFm (n + 2)) (σ : Fin n → Tm m) :
    dstart (B.subst (up (up σ))) = Syn.subst (up σ) (dstart B) := by
  unfold dstart
  rw [isDiag_subst]
  split <;> simp

theorem subst_repl_up (A : NFm (n + 1)) (d : Tm (n + 1)) (σ : Fin n → Tm m) :
    (A.subst (repl d)).subst (up σ) = (A.subst (up σ)).subst (repl (Syn.subst (up σ) d)) := by
  rw [subst_subst, subst_subst]
  refine A.subst_ext fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · rw [repl_succ, Syn.subst_var, up_succ, Syn.subst_repl_shift]

theorem subst_repl_var0 (A : NFm (n + 1)) : A.subst (repl (Syn.var 0)) = A :=
  A.subst_eq_self fun i => by refine Fin.cases ?_ (fun j => ?_) i <;> simp

end NFm

/-- Derivability with one introduction rule whose mode is determined by the
diagonal shape of the matrix. -/
inductive GPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : GPrf Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      GPrf Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      GPrf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  | trOne {n : ℕ} {Γ : List (NFm n)} (h : Tm (n + 1)) {s t u : Tm n}
      (h₁ : GPrf Γ (.eq s t)) (h₂ : GPrf Γ (.eq (Syn.subst (inst s) h) u)) :
      GPrf Γ (.eq u (Syn.subst (inst t) h))
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : GPrf Γ (.Q B)) (h₂ : GPrf Γ (B.subst (inst zero))) : GPrf Γ (B.subst (inst t))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : GPrf Γ (.D B)) (h₂ : GPrf (.Q B :: Γ.map NFm.shift) A.shift) : GPrf Γ A
  /-- DI: from `B(t, η) ⊢ B(t, S z)` with `z` fresh infer `D_{x,y} B`, where
  `η = z` for a diagonal matrix and `η = 0` otherwise. -/
  | dI {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n)
      (h : GPrf ((B.subst (up (inst t))).subst (repl (NFm.dstart B)) :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      GPrf Γ (.D B)

variable {Γ Δ : List (NFm n)} {A : NFm n}

/-- An instance of the diagonal introduction is one of the two introductions of
the reports' calculus, both derived in the kernel. -/
theorem NPrf.ofDIG (B : NFm (n + 2)) (t : Tm n)
    (h : NPrf ((B.subst (up (inst t))).subst (repl (NFm.dstart B)) :: Γ.map NFm.shift)
      ((B.subst (up (inst t))).subst (repl (succ (Syn.var 0))))) : NPrf Γ (.D B) := by
  by_cases hd : B.isDiag = true
  · cases B with
    | eq s₁ s₂ =>
      rw [NFm.dstart, if_pos hd, NFm.subst_repl_var0] at h
      exact .dIProg s₁ s₂ t h
    | Q B => exact Bool.noConfusion hd
    | D B => exact Bool.noConfusion hd
  · rw [NFm.dstart, if_neg hd, ← NFm.shift_subst_inst_zero] at h
    exact .dICase B t h

namespace GPrf

theorem toNPrf (h : GPrf Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => exact .trOne h ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dI B t _ ih => exact .ofDIG B t ih

/-! ### Structural rules, by direct induction -/

theorem hyp0 : GPrf (A :: Γ) A := .hyp List.mem_cons_self

theorem weaken (h : GPrf Γ A) : ∀ {Δ : List (NFm n)}, Γ ⊆ Δ → GPrf Δ A := by
  induction h with
  | hyp h => intro Δ s; exact .hyp (s h)
  | iterZero a h => intro Δ _; exact .iterZero a h
  | iterSucc c a h => intro Δ _; exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => intro Δ s; exact .trOne h (ih₁ s) (ih₂ s)
  | qE t _ _ ih₁ ih₂ => intro Δ s; exact .qE t (ih₁ s) (ih₂ s)
  | dE _ _ ih₁ ih₂ =>
    intro Δ s
    exact .dE (ih₁ s) (ih₂ (List.cons_subset_cons _ (List.map_subset _ s)))
  | dI B t _ ih =>
    intro Δ s
    exact .dI B t (ih (List.cons_subset_cons _ (List.map_subset _ s)))

theorem wk {B : NFm n} (h : GPrf Γ A) : GPrf (B :: Γ) A := h.weaken (List.subset_cons_self _ _)

/-- Substitution of terms for the free variables of a derivation.  The
introduction rule commutes with it because its guard does. -/
theorem subst (h : GPrf Γ A) : ∀ {m : ℕ} (σ : Fin n → Tm m),
    GPrf (Γ.map fun B => B.subst σ) (A.subst σ) := by
  induction h with
  | hyp h => intro m σ; exact .hyp (List.mem_map_of_mem h)
  | iterZero a h => intro m σ; exact .iterZero _ _
  | iterSucc c a h =>
    intro m σ
    simp only [NFm.subst_eq, Tm.subst_iter, Tm.subst_succ, Syn.subst_subst_inst]
    exact .iterSucc _ _ _
  | trOne h _ _ ih₁ ih₂ =>
    intro m σ
    have h₂ := ih₂ σ
    simp only [NFm.subst_eq, Syn.subst_subst_inst] at h₂ ⊢
    exact .trOne _ (ih₁ σ) h₂
  | qE t _ _ ih₁ ih₂ =>
    intro m σ
    have h₂ := ih₂ σ
    rw [NFm.subst_inst] at h₂ ⊢
    exact .qE _ (ih₁ σ) h₂
  | dE _ _ ih₁ ih₂ =>
    intro m σ
    have h := ih₂ (up σ)
    rw [List.map_cons, NFm.map_shift_subst, NFm.shift_subst_up] at h
    exact .dE (ih₁ σ) h
  | dI B t _ ih =>
    intro m σ
    have h := ih (up σ)
    rw [List.map_cons, NFm.map_shift_subst, NFm.subst_repl_succ,
      NFm.subst_repl_up _ (NFm.dstart B) σ, NFm.subst_up_inst, ← NFm.dstart_subst] at h
    exact .dI _ _ h

theorem shift (h : GPrf Γ A) : GPrf (Γ.map NFm.shift) A.shift := h.subst _

theorem cutLift (h : ∀ B ∈ Γ, GPrf Δ B) (C : NFm (n + 1)) :
    ∀ B ∈ C :: Γ.map NFm.shift, GPrf (C :: Δ.map NFm.shift) B := by
  intro B hB
  rcases List.mem_cons.1 hB with rfl | hB
  · exact hyp0
  · obtain ⟨B₀, hB₀, rfl⟩ := List.mem_map.1 hB
    exact (h B₀ hB₀).shift.wk

theorem cut (h : GPrf Γ A) : ∀ {Δ : List (NFm n)}, (∀ B ∈ Γ, GPrf Δ B) → GPrf Δ A := by
  induction h with
  | hyp h => intro Δ hΔ; exact hΔ _ h
  | iterZero a h => intro Δ _; exact .iterZero a h
  | iterSucc c a h => intro Δ _; exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => intro Δ hΔ; exact .trOne h (ih₁ hΔ) (ih₂ hΔ)
  | qE t _ _ ih₁ ih₂ => intro Δ hΔ; exact .qE t (ih₁ hΔ) (ih₂ hΔ)
  | dE _ _ ih₁ ih₂ => intro Δ hΔ; exact .dE (ih₁ hΔ) (ih₂ (cutLift hΔ _))
  | dI B t _ ih => intro Δ hΔ; exact .dI B t (ih (cutLift hΔ _))

theorem cut1 {B : NFm n} (h₁ : GPrf Γ B) (h₂ : GPrf (B :: Γ) A) : GPrf Γ A := by
  refine h₂.cut fun C hC => ?_
  rcases List.mem_cons.1 hC with rfl | hC
  · exact h₁
  · exact .hyp hC

/-! ### Equality -/

theorem eqRefl (t : Tm n) : GPrf Γ (.eq t t) :=
  .trOne (Syn.var 0) (.iterZero t (Syn.var 0)) (.iterZero t (Syn.var 0))

theorem eqSymm {s t : Tm n} (h : GPrf Γ (.eq s t)) : GPrf Γ (.eq t s) :=
  .trOne (Syn.var 0) (eqRefl s) h

theorem eqTrans {s t u : Tm n} (h₁ : GPrf Γ (.eq s t)) (h₂ : GPrf Γ (.eq t u)) :
    GPrf Γ (.eq s u) :=
  .trOne (Syn.var 0) h₂ (eqSymm h₁)

theorem eqCongr (h : Tm (n + 1)) {s t : Tm n} (e : GPrf Γ (.eq s t)) :
    GPrf Γ (.eq (Syn.subst (inst s) h) (Syn.subst (inst t) h)) :=
  .trOne h e (eqRefl _)

theorem selZero (a b : Tm n) : GPrf Γ (.eq (Tm.sel zero a b) a) := .iterZero a _

theorem selSucc (c a b : Tm n) : GPrf Γ (.eq (Tm.sel (succ c) a b) b) := by
  have h := GPrf.iterSucc (Γ := Γ) c a (Syn.shift b)
  rwa [Syn.subst_inst_shift] at h

theorem selCongr₂ (c b : Tm n) {a a' : Tm n} (e : GPrf Γ (.eq a a')) :
    GPrf Γ (.eq (Tm.sel c a b) (Tm.sel c a' b)) := by
  have h := eqCongr (Tm.sel (Syn.shift c) (Syn.var 0) (Syn.shift b)) e
  simpa only [Tm.subst_sel, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using h

theorem selCongr₃ (c a : Tm n) {b b' : Tm n} (e : GPrf Γ (.eq b b')) :
    GPrf Γ (.eq (Tm.sel c a b) (Tm.sel c a b')) := by
  have h := eqCongr (Tm.sel (Syn.shift c) (Syn.shift a) (Syn.var 0)) e
  simpa only [Tm.subst_sel, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using h

/-- `I(S c, a; u.x) = x` when `x` does not mention `u`. -/
theorem iterConst (c a x : Tm n) : GPrf Γ (.eq (iter (succ c) a (Syn.shift x)) x) := by
  have h := GPrf.iterSucc (Γ := Γ) c a (Syn.shift x)
  rwa [Syn.subst_inst_shift] at h

/-! ### `D` by cases, for every matrix -/

theorem diagTermZero {s : Tm (n + 2)} (hs : s.isDiag = true) (t : Tm n) :
    GPrf Γ (.eq (Syn.subst (inst zero) (Syn.subst (up (inst t)) s)) zero) := by
  cases s with
  | var i => exact Bool.noConfusion hs
  | zero => exact Bool.noConfusion hs
  | succ t => exact Bool.noConfusion hs
  | iter c a h =>
    have hc : c.isV0 = true ∧ a.isV0 = true := by simpa [Tm.isDiag] using hs
    rw [Tm.eq_var0 hc.1, Tm.eq_var0 hc.2]
    exact .iterZero zero _

/-- The base of a diagonal matrix is a theorem. -/
theorem diagBase {B : NFm (n + 2)} (hB : B.isDiag = true) (t : Tm n) :
    GPrf Γ ((B.subst (up (inst t))).subst (inst zero)) := by
  cases B with
  | eq s₁ s₂ =>
    have h : s₁.isDiag = true ∧ s₂.isDiag = true := by simpa [NFm.isDiag] using hB
    exact eqTrans (diagTermZero h.1 t) (eqSymm (diagTermZero h.2 t))
  | Q B => exact Bool.noConfusion hB
  | D B => exact Bool.noConfusion hB

/-- `D` by cases: from `B(t, 0) ⊢ B(t, S z)` infer `D_{x,y} B`, for every
matrix. -/
theorem dICase (B : NFm (n + 2)) (t : Tm n)
    (h : GPrf (((B.subst (up (inst t))).subst (inst zero)).shift :: Γ.map NFm.shift)
      ((B.subst (up (inst t))).subst (repl (succ (Syn.var 0))))) : GPrf Γ (.D B) := by
  refine .dI B t ?_
  by_cases hd : B.isDiag = true
  · rw [NFm.dstart, if_pos hd]
    exact (cut1 (diagBase (Γ := Γ) hd t).shift h).wk
  · rw [NFm.dstart, if_neg hd, ← NFm.shift_subst_inst_zero]
    exact h

/-- `Q` by cases: from `B(0) ⊢ B(S z)` infer `Q_y B(y)`. -/
theorem qI (B : NFm (n + 1))
    (h : GPrf ((B.subst (inst zero)).shift :: Γ.map NFm.shift)
      (B.subst (repl (succ (Syn.var 0))))) : GPrf Γ (.Q B) := by
  have hD : GPrf Γ (.D (B.subst (up (fun i => Syn.var i.succ)))) := by
    refine dICase _ zero ?_
    rw [NFm.subst_dummy_inst]
    exact h
  refine .dE hD ?_
  show GPrf (.Q (B.subst (up (fun i => Syn.var i.succ))) :: Γ.map NFm.shift)
    (.Q (B.subst (up (fun i => Syn.var i.succ))))
  exact hyp0

/-- Cases on the last variable. -/
theorem casesVar (E : NFm (n + 1)) (h0 : GPrf Γ (E.subst (inst zero)))
    (hS : GPrf (Γ.map NFm.shift) (E.subst (repl (succ (Syn.var 0))))) :
    GPrf (Γ.map NFm.shift) E := by
  have hQ : GPrf (Γ.map NFm.shift) (.Q (E.subst (up (fun i => Syn.var i.succ)))) :=
    (qI E hS.wk).shift
  have h0' := h0.shift
  rw [NFm.shift_subst_inst_zero, ← NFm.subst_dummy_up_inst] at h0'
  have h := GPrf.qE (Syn.var 0) hQ h0'
  rwa [NFm.subst_up_inst_var] at h

/-! ### `Q` by progress, for every equation -/

/-- The diagonal lift `I(y, y; u.s)` of a term `s(y)`. -/
def lift (s : Tm (n + 1)) : Tm (n + 1) := iter (Syn.var 0) (Syn.var 0) (Syn.shift s)

theorem lift_repl (s : Tm (n + 1)) :
    Syn.subst (repl (succ (Syn.var 0))) (lift s)
      = iter (succ (Syn.var 0)) (succ (Syn.var 0))
          (Syn.shift (Syn.subst (repl (succ (Syn.var 0))) s)) := by
  simp [lift, Syn.subst_up_shift]

/-- `sel(y, s(0), I(y, y; u.s(y))) = s(y)`, unconditionally. -/
theorem liftSel (s : Tm (n + 1)) :
    GPrf (Γ.map NFm.shift)
      (.eq (Tm.sel (Syn.var 0) (Syn.shift (Syn.subst (inst zero) s)) (lift s)) s) := by
  refine casesVar _ ?_ ?_
  · simp only [NFm.subst_eq, Tm.subst_sel, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
    exact selZero _ _
  · simp only [NFm.subst_eq, Tm.subst_sel, Syn.subst_var, Syn.repl_zero,
      Syn.subst_repl_shift, lift_repl]
    exact eqTrans (selSucc _ _ _) (iterConst _ _ _)

/-- `Q` by progress: from `E(z) ⊢ E(S z)` infer `Q_y E(y)`, for every literal
equation `E`. -/
theorem qInd (s t : Tm (n + 1))
    (π : GPrf (NFm.eq s t :: Γ.map NFm.shift) ((NFm.eq s t).subst (repl (succ (Syn.var 0))))) :
    GPrf Γ (.Q (.eq s t)) := by
  -- the retained base and the diagonal lift
  let E0 : NFm n := (NFm.eq s t).subst (inst zero)
  let H : NFm (n + 1) := .eq (lift s) (lift t)
  -- `H(z) ⊢ H(S z)` over the base
  have step : GPrf (H :: (E0 :: Γ).map NFm.shift) (H.subst (repl (succ (Syn.var 0)))) := by
    have sub : Γ.map NFm.shift ⊆ H :: (E0 :: Γ).map NFm.shift := fun X hX =>
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hX)
    have hH : GPrf (H :: (E0 :: Γ).map NFm.shift) (.eq (lift s) (lift t)) := hyp0
    have hE0 : GPrf (H :: (E0 :: Γ).map NFm.shift)
        (.eq (Syn.shift (Syn.subst (inst zero) s)) (Syn.shift (Syn.subst (inst zero) t))) :=
      .hyp (List.mem_cons_of_mem _ List.mem_cons_self)
    have hE : GPrf (H :: (E0 :: Γ).map NFm.shift) (.eq s t) :=
      eqTrans (eqSymm ((liftSel s).weaken sub))
        (eqTrans (selCongr₃ _ _ hH) (eqTrans (selCongr₂ _ _ hE0) ((liftSel t).weaken sub)))
    have hES := cut1 hE (π.weaken (List.cons_subset_cons _ sub))
    simp only [NFm.subst_eq] at hES
    show GPrf _ (.eq (Syn.subst (repl (succ (Syn.var 0))) (lift s))
      (Syn.subst (repl (succ (Syn.var 0))) (lift t)))
    rw [lift_repl, lift_repl]
    exact eqTrans (iterConst _ _ _) (eqTrans hES (eqSymm (iterConst _ _ _)))
  -- primitive progress for the lift, with a dummy witness coordinate
  have hQ : GPrf (E0 :: Γ) (.Q H) := by
    have hD : GPrf (E0 :: Γ) (.D (H.subst (up (fun i => Syn.var i.succ)))) := by
      refine .dI _ zero ?_
      rw [NFm.dstart, if_pos (by rfl), NFm.subst_dummy_inst, NFm.subst_repl_var0]
      exact step
    refine .dE hD ?_
    show GPrf (.Q (H.subst (up (fun i => Syn.var i.succ))) :: (E0 :: Γ).map NFm.shift)
      (.Q (H.subst (up (fun i => Syn.var i.succ))))
    exact hyp0
  -- `E(0) ⊢ E(S z)`, by `QE` at `S z`
  refine qI (.eq s t) ?_
  have h0 : GPrf (E0 :: Γ) (H.subst (inst zero)) :=
    eqTrans (.iterZero zero _) (eqSymm (.iterZero zero _))
  have h0' := h0.shift
  rw [NFm.shift_subst_inst_zero, ← NFm.subst_dummy_up_inst] at h0'
  have h := GPrf.qE (succ (Syn.var 0)) hQ.shift h0'
  rw [NFm.subst_dummy_up_inst] at h
  have h' : GPrf ((E0 :: Γ).map NFm.shift)
      (.eq (Syn.subst (repl (succ (Syn.var 0))) (lift s))
        (Syn.subst (repl (succ (Syn.var 0))) (lift t))) := h
  rw [lift_repl, lift_repl] at h'
  exact eqTrans (eqSymm (iterConst _ _ _)) (eqTrans h' (iterConst _ _ _))

end GPrf

theorem NPrf.toGPrf (h : NPrf Γ A) : GPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => exact .trOne h ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dICase B t _ ih => exact GPrf.dICase B t ih
  | qIInd s t _ ih => exact GPrf.qInd s t ih

/-- **A substitution-stable single introduction suffices**: `GPrf` and the
kernel derive the same sequents. -/
theorem gprf_iff_nprf : GPrf Γ A ↔ NPrf Γ A := ⟨GPrf.toNPrf, NPrf.toGPrf⟩

/-- `GPrf` derives the same sequents as the calculus of the research reports. -/
theorem gprf_iff_iprf : GPrf Γ A ↔ IPrf Γ A := gprf_iff_nprf.trans iprf_iff_nprf.symm

end LeanProofs.ConciseIPRA
