import ConciseIPRA.NativeClausal

/-!
# A one-iterator selector for the single introduction

The package `Research/mirror_core` chooses the mode of the single introduction
by a smaller test than the diagonal one of `NativeDiagonal`: progress exactly
when the matrix is literally of the *mirror* shape

  `a(x, y) = I(y, a(x, y); u.h)`,

an equation whose right-hand side is an iterator counted by `y` and seeded by
the left-hand side.  One iterator occurs in the test instead of two.

* `MiPrf` is the kernel with this introduction in place of its two (seven
  rules), and `miprf_iff_nprf` proves that it derives the same sequents.
* `M6Prf` is the six-rule calculus of the package: hypothesis, reflexivity,
  the two-case Eval, `QE`, `DE` and the mirror introduction
  (`m6prf_iff_nprf`).

The mirror shape is preserved by substitution but can be created by it, when
a substitution identifies the seed with the left-hand side.  So `MiPrf` is not
closed under substitution by a direct induction.  It is closed under
*injective renaming* (`MiPrf.ren`), because an injective renaming reflects
syntactic equality of terms (`Tm.ren_inj`), and that is all that weakening
under a binder and cut need.

Progress for an arbitrary equation `s(y) = t(y)` is recovered through its
mirror lift `M(y) = (s = sel(y, s, t))`, whose base is a computation.  With the
base `s(0) = t(0)` retained, three unconditional equations, each proved by
cases on `y`,

  `sel(y, s(0), s) = s`,  `sel(y, s(0), sel(y, s, t)) = sel(y, s(0), t)`,
  `sel(y, t(0), t) = t`,

turn `M(z)` into `s(z) = t(z)` by equational reasoning.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

variable {n m : ℕ}

namespace Tm

theorem upRen_inj {ξ : Fin n → Fin m} (hξ : Function.Injective ξ) :
    Function.Injective (upRen ξ) := by
  intro i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
  · intro _; rfl
  · intro e
    simp only [upRen_zero, upRen_succ] at e
    exact absurd e.symm (Fin.succ_ne_zero _)
  · intro e
    simp only [upRen_zero, upRen_succ] at e
    exact absurd e (Fin.succ_ne_zero _)
  · intro e
    simp only [upRen_succ, Fin.succ_inj] at e
    rw [hξ e]

/-- An injective renaming reflects syntactic equality. -/
theorem ren_inj (s : Tm n) : ∀ {m : ℕ} {ξ : Fin n → Fin m}, Function.Injective ξ →
    ∀ t : Tm n, ren ξ s = ren ξ t → s = t := by
  induction s with intro m ξ hξ t e
  | var i =>
    cases t <;> simp only [ren, Tm.var.injEq, reduceCtorEq] at e
    rw [hξ e]
  | zero =>
    cases t <;> simp only [ren, reduceCtorEq] at e
    rfl
  | succ a ih =>
    cases t <;> simp only [ren, Tm.succ.injEq, reduceCtorEq] at e
    rw [ih hξ _ e]
  | iter c a h ihc iha ihh =>
    cases t <;> simp only [ren, Tm.iter.injEq, reduceCtorEq] at e
    obtain ⟨e₁, e₂, e₃⟩ := e
    rw [ihc hξ _ e₁, iha hξ _ e₂, ihh (upRen_inj hξ) _ e₃]

end Tm

namespace NFm

/-- The matrix is literally of the shape `a = I(y, a; u.h)`, where `y` is the
variable `0`. -/
def IsMirror (B : NFm (n + 2)) : Prop := ∃ a h, B = .eq a (Tm.iter (Tm.var 0) a h)

open Classical in
/-- The start of the mirror introduction. -/
noncomputable def mstart (B : NFm (n + 2)) : Tm (n + 1) :=
  if IsMirror B then Syn.var 0 else zero

/-- Substitution preserves the mirror shape. -/
theorem IsMirror.subst {B : NFm (n + 2)} (h : IsMirror B) (σ : Fin n → Tm m) :
    IsMirror (B.subst (up (up σ))) := by
  obtain ⟨a, b, rfl⟩ := h
  exact ⟨Syn.subst (up (up σ)) a, Syn.subst (up (up (up σ))) b, by
    rw [NFm.subst_eq, Tm.subst_iter]; rfl⟩

/-- An injective renaming preserves and reflects the mirror shape. -/
theorem isMirror_rn {ξ : Fin n → Fin m} (hξ : Function.Injective ξ) (B : NFm (n + 2)) :
    IsMirror (B.subst (up (up fun i => (Syn.var (ξ i) : Tm m)))) ↔ IsMirror B := by
  refine ⟨?_, fun h => h.subst _⟩
  rintro ⟨a', h', e⟩
  rw [Tm.up_rn, Tm.up_rn] at e
  cases B with
  | eq s t =>
    have e' : NFm.eq (Tm.ren (Tm.upRen (Tm.upRen ξ)) s) (Tm.ren (Tm.upRen (Tm.upRen ξ)) t)
        = .eq a' (Tm.iter (Tm.var 0) a' h') := by
      rw [Tm.ren_eq_sub, Tm.ren_eq_sub]; exact e
    simp only [NFm.eq.injEq] at e'
    obtain ⟨e₁, e₂⟩ := e'
    cases t with
    | var i => simp only [Tm.ren, reduceCtorEq] at e₂
    | zero => simp only [Tm.ren, reduceCtorEq] at e₂
    | succ t => simp only [Tm.ren, reduceCtorEq] at e₂
    | iter c a₀ h₀ =>
      simp only [Tm.ren, Tm.iter.injEq] at e₂
      obtain ⟨ec, ea, _⟩ := e₂
      have hc : c = Tm.var 0 := by
        cases c <;> simp only [Tm.ren, Tm.var.injEq, reduceCtorEq] at ec
        rename_i i
        rw [show i = 0 from (Tm.upRen_inj (Tm.upRen_inj hξ)) (by rw [ec]; rfl)]
      have ha : a₀ = s := Tm.ren_inj a₀ (Tm.upRen_inj (Tm.upRen_inj hξ)) s (by rw [ea, e₁])
      exact ⟨s, h₀, by rw [hc, ha]⟩
  | Q B => simp only [NFm.subst_Q, reduceCtorEq] at e
  | D B => simp only [NFm.subst_D, reduceCtorEq] at e

theorem mstart_rn {ξ : Fin n → Fin m} (hξ : Function.Injective ξ) (B : NFm (n + 2)) :
    mstart (B.subst (up (up fun i => (Syn.var (ξ i) : Tm m))))
      = Syn.subst (up fun i => (Syn.var (ξ i) : Tm m)) (mstart B) := by
  by_cases hm : IsMirror B
  · rw [mstart, if_pos ((isMirror_rn hξ B).2 hm), mstart, if_pos hm]; simp
  · rw [mstart, if_neg (fun h => hm ((isMirror_rn hξ B).1 h)), mstart, if_neg hm]; simp

end NFm

/-- Derivability with one introduction rule whose mode is determined by the
mirror shape of the matrix. -/
inductive MiPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : MiPrf Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      MiPrf Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      MiPrf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  | trOne {n : ℕ} {Γ : List (NFm n)} (h : Tm (n + 1)) {s t u : Tm n}
      (h₁ : MiPrf Γ (.eq s t)) (h₂ : MiPrf Γ (.eq (Syn.subst (inst s) h) u)) :
      MiPrf Γ (.eq u (Syn.subst (inst t) h))
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : MiPrf Γ (.Q B)) (h₂ : MiPrf Γ (B.subst (inst zero))) : MiPrf Γ (B.subst (inst t))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : MiPrf Γ (.D B)) (h₂ : MiPrf (.Q B :: Γ.map NFm.shift) A.shift) : MiPrf Γ A
  /-- DI: from `B(t, η) ⊢ B(t, S z)` with `z` fresh infer `D_{x,y} B`, where
  `η = z` for a mirror matrix and `η = 0` otherwise. -/
  | dI {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n)
      (h : MiPrf ((B.subst (up (inst t))).subst (repl (NFm.mstart B)) :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      MiPrf Γ (.D B)

variable {Γ Δ : List (NFm n)} {A : NFm n}

/-- An instance of the mirror introduction is one of the two introductions of
the reports' calculus. -/
theorem NPrf.ofDIM (B : NFm (n + 2)) (t : Tm n)
    (h : NPrf ((B.subst (up (inst t))).subst (repl (NFm.mstart B)) :: Γ.map NFm.shift)
      ((B.subst (up (inst t))).subst (repl (succ (Syn.var 0))))) : NPrf Γ (.D B) := by
  by_cases hm : B.IsMirror
  · obtain ⟨a, b, rfl⟩ := hm
    rw [NFm.mstart, if_pos ⟨a, b, rfl⟩, NFm.subst_repl_var0] at h
    exact .dIProg _ _ t h
  · rw [NFm.mstart, if_neg hm, ← NFm.shift_subst_inst_zero] at h
    exact .dICase B t h

namespace MiPrf

theorem toNPrf (h : MiPrf Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => exact .trOne h ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dI B t _ ih => exact .ofDIM B t ih

/-! ### Structural rules -/

theorem hyp0 : MiPrf (A :: Γ) A := .hyp List.mem_cons_self

theorem weaken (h : MiPrf Γ A) : ∀ {Δ : List (NFm n)}, Γ ⊆ Δ → MiPrf Δ A := by
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

theorem wk {B : NFm n} (h : MiPrf Γ A) : MiPrf (B :: Γ) A :=
  h.weaken (List.subset_cons_self _ _)

/-- Injective renaming of the free variables of a derivation. -/
theorem ren (h : MiPrf Γ A) : ∀ {m : ℕ} (ξ : Fin n → Fin m), Function.Injective ξ →
    MiPrf (Γ.map fun B => B.subst fun i => (Syn.var (ξ i) : Tm m))
      (A.subst fun i => (Syn.var (ξ i) : Tm m)) := by
  induction h with
  | hyp h => intro m ξ _; exact .hyp (List.mem_map_of_mem h)
  | iterZero a h => intro m ξ _; exact .iterZero _ _
  | iterSucc c a h =>
    intro m ξ _
    simp only [NFm.subst_eq, Tm.subst_iter, Tm.subst_succ, Syn.subst_subst_inst]
    exact .iterSucc _ _ _
  | trOne h _ _ ih₁ ih₂ =>
    intro m ξ hξ
    have h₂ := ih₂ ξ hξ
    simp only [NFm.subst_eq, Syn.subst_subst_inst] at h₂ ⊢
    exact .trOne _ (ih₁ ξ hξ) h₂
  | qE t _ _ ih₁ ih₂ =>
    intro m ξ hξ
    have h₂ := ih₂ ξ hξ
    rw [NFm.subst_inst] at h₂ ⊢
    exact .qE _ (ih₁ ξ hξ) h₂
  | dE _ _ ih₁ ih₂ =>
    intro m ξ hξ
    have h := ih₂ (Tm.upRen ξ) (Tm.upRen_inj hξ)
    rw [← Tm.up_rn, List.map_cons, NFm.map_shift_subst, NFm.shift_subst_up] at h
    exact .dE (ih₁ ξ hξ) h
  | @dI _ Γ B t _ ih =>
    intro m ξ hξ
    have h := ih (Tm.upRen ξ) (Tm.upRen_inj hξ)
    rw [← Tm.up_rn, List.map_cons, NFm.map_shift_subst, NFm.subst_repl_succ,
      NFm.subst_repl_up _ (NFm.mstart B), NFm.subst_up_inst, ← NFm.mstart_rn hξ] at h
    exact .dI _ _ h

theorem shift (h : MiPrf Γ A) : MiPrf (Γ.map NFm.shift) A.shift :=
  h.ren Fin.succ (Fin.succ_injective _)

theorem cutLift (h : ∀ B ∈ Γ, MiPrf Δ B) (C : NFm (n + 1)) :
    ∀ B ∈ C :: Γ.map NFm.shift, MiPrf (C :: Δ.map NFm.shift) B := by
  intro B hB
  rcases List.mem_cons.1 hB with rfl | hB
  · exact hyp0
  · obtain ⟨B₀, hB₀, rfl⟩ := List.mem_map.1 hB
    exact (h B₀ hB₀).shift.wk

theorem cut (h : MiPrf Γ A) : ∀ {Δ : List (NFm n)}, (∀ B ∈ Γ, MiPrf Δ B) → MiPrf Δ A := by
  induction h with
  | hyp h => intro Δ hΔ; exact hΔ _ h
  | iterZero a h => intro Δ _; exact .iterZero a h
  | iterSucc c a h => intro Δ _; exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => intro Δ hΔ; exact .trOne h (ih₁ hΔ) (ih₂ hΔ)
  | qE t _ _ ih₁ ih₂ => intro Δ hΔ; exact .qE t (ih₁ hΔ) (ih₂ hΔ)
  | dE _ _ ih₁ ih₂ => intro Δ hΔ; exact .dE (ih₁ hΔ) (ih₂ (cutLift hΔ _))
  | dI B t _ ih => intro Δ hΔ; exact .dI B t (ih (cutLift hΔ _))

theorem cut1 {B : NFm n} (h₁ : MiPrf Γ B) (h₂ : MiPrf (B :: Γ) A) : MiPrf Γ A := by
  refine h₂.cut fun C hC => ?_
  rcases List.mem_cons.1 hC with rfl | hC
  · exact h₁
  · exact .hyp hC

/-! ### Equality and the selector -/

theorem eqRefl (t : Tm n) : MiPrf Γ (.eq t t) :=
  .trOne (Syn.var 0) (.iterZero t (Syn.var 0)) (.iterZero t (Syn.var 0))

theorem eqSymm {s t : Tm n} (h : MiPrf Γ (.eq s t)) : MiPrf Γ (.eq t s) :=
  .trOne (Syn.var 0) (eqRefl s) h

theorem eqTrans {s t u : Tm n} (h₁ : MiPrf Γ (.eq s t)) (h₂ : MiPrf Γ (.eq t u)) :
    MiPrf Γ (.eq s u) :=
  .trOne (Syn.var 0) h₂ (eqSymm h₁)

theorem eqCongr (h : Tm (n + 1)) {s t : Tm n} (e : MiPrf Γ (.eq s t)) :
    MiPrf Γ (.eq (Syn.subst (inst s) h) (Syn.subst (inst t) h)) :=
  .trOne h e (eqRefl _)

theorem selZero (a b : Tm n) : MiPrf Γ (.eq (Tm.sel zero a b) a) := .iterZero a _

theorem selSucc (c a b : Tm n) : MiPrf Γ (.eq (Tm.sel (succ c) a b) b) := by
  have h := MiPrf.iterSucc (Γ := Γ) c a (Syn.shift b)
  rwa [Syn.subst_inst_shift] at h

theorem selCongr₂ (c b : Tm n) {a a' : Tm n} (e : MiPrf Γ (.eq a a')) :
    MiPrf Γ (.eq (Tm.sel c a b) (Tm.sel c a' b)) := by
  have h := eqCongr (Tm.sel (Syn.shift c) (Syn.var 0) (Syn.shift b)) e
  simpa only [Tm.subst_sel, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using h

theorem selCongr₃ (c a : Tm n) {b b' : Tm n} (e : MiPrf Γ (.eq b b')) :
    MiPrf Γ (.eq (Tm.sel c a b) (Tm.sel c a b')) := by
  have h := eqCongr (Tm.sel (Syn.shift c) (Syn.shift a) (Syn.var 0)) e
  simpa only [Tm.subst_sel, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using h

/-! ### `D` by cases, for every matrix -/

/-- The base of a mirror matrix is a computation. -/
theorem mirrorBase {B : NFm (n + 2)} (hB : B.IsMirror) (t : Tm n) :
    MiPrf Γ ((B.subst (up (inst t))).subst (inst zero)) := by
  obtain ⟨a, b, rfl⟩ := hB
  rw [NFm.subst_eq, NFm.subst_eq, Tm.subst_iter, Tm.subst_iter]
  exact eqSymm (.iterZero _ _)

theorem dICase (B : NFm (n + 2)) (t : Tm n)
    (h : MiPrf (((B.subst (up (inst t))).subst (inst zero)).shift :: Γ.map NFm.shift)
      ((B.subst (up (inst t))).subst (repl (succ (Syn.var 0))))) : MiPrf Γ (.D B) := by
  refine .dI B t ?_
  by_cases hm : B.IsMirror
  · rw [NFm.mstart, if_pos hm]
    exact (cut1 (mirrorBase (Γ := Γ) hm t).shift h).wk
  · rw [NFm.mstart, if_neg hm, ← NFm.shift_subst_inst_zero]
    exact h

theorem qI (B : NFm (n + 1))
    (h : MiPrf ((B.subst (inst zero)).shift :: Γ.map NFm.shift)
      (B.subst (repl (succ (Syn.var 0))))) : MiPrf Γ (.Q B) := by
  have hD : MiPrf Γ (.D (B.subst (up (fun i => Syn.var i.succ)))) := by
    refine dICase _ zero ?_
    rw [NFm.subst_dummy_inst]
    exact h
  refine .dE hD ?_
  show MiPrf (.Q (B.subst (up (fun i => Syn.var i.succ))) :: Γ.map NFm.shift)
    (.Q (B.subst (up (fun i => Syn.var i.succ))))
  exact hyp0

/-- Cases on the last variable. -/
theorem casesVar (E : NFm (n + 1)) (h0 : MiPrf Γ (E.subst (inst zero)))
    (hS : MiPrf (Γ.map NFm.shift) (E.subst (repl (succ (Syn.var 0))))) :
    MiPrf (Γ.map NFm.shift) E := by
  have hQ : MiPrf (Γ.map NFm.shift) (.Q (E.subst (up (fun i => Syn.var i.succ)))) :=
    (qI E hS.wk).shift
  have h0' := h0.shift
  rw [NFm.shift_subst_inst_zero, ← NFm.subst_dummy_up_inst] at h0'
  have h := MiPrf.qE (Syn.var 0) hQ h0'
  rwa [NFm.subst_up_inst_var] at h

/-! ### `Q` by progress, for every equation -/

/-- `sel(y, s(0), s(y)) = s(y)`, unconditionally. -/
theorem selBase (s : Tm (n + 1)) :
    MiPrf (Γ.map NFm.shift)
      (.eq (Tm.sel (Syn.var 0) (Syn.shift (Syn.subst (inst zero) s)) s) s) := by
  refine casesVar _ ?_ ?_
  · simp only [NFm.subst_eq, Tm.subst_sel, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
    exact selZero _ _
  · simp only [NFm.subst_eq, Tm.subst_sel, Syn.subst_var, Syn.repl_zero, Syn.subst_repl_shift]
    exact selSucc _ _ _

/-- `sel(y, s(0), sel(y, s, t)) = sel(y, s(0), t)`, unconditionally. -/
theorem selNest (s t : Tm (n + 1)) :
    MiPrf (Γ.map NFm.shift)
      (.eq (Tm.sel (Syn.var 0) (Syn.shift (Syn.subst (inst zero) s)) (Tm.sel (Syn.var 0) s t))
        (Tm.sel (Syn.var 0) (Syn.shift (Syn.subst (inst zero) s)) t)) := by
  refine casesVar _ ?_ ?_
  · simp only [NFm.subst_eq, Tm.subst_sel, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
    exact eqTrans (selZero _ _) (eqSymm (selZero _ _))
  · simp only [NFm.subst_eq, Tm.subst_sel, Syn.subst_var, Syn.repl_zero, Syn.subst_repl_shift]
    exact eqTrans (selSucc _ _ _) (eqTrans (selSucc _ _ _) (eqSymm (selSucc _ _ _)))

/-- `Q` by progress: from `E(z) ⊢ E(S z)` infer `Q_y E(y)`, for every literal
equation `E`. -/
theorem qInd (s t : Tm (n + 1))
    (π : MiPrf (NFm.eq s t :: Γ.map NFm.shift) ((NFm.eq s t).subst (repl (succ (Syn.var 0))))) :
    MiPrf Γ (.Q (.eq s t)) := by
  -- the retained base and the mirror lift
  let E0 : NFm n := (NFm.eq s t).subst (inst zero)
  let M : NFm (n + 1) := .eq s (Tm.sel (Syn.var 0) s t)
  have step : MiPrf (M :: (E0 :: Γ).map NFm.shift) (M.subst (repl (succ (Syn.var 0)))) := by
    have sub : Γ.map NFm.shift ⊆ M :: (E0 :: Γ).map NFm.shift := fun X hX =>
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hX)
    have hM : MiPrf (M :: (E0 :: Γ).map NFm.shift) (.eq s (Tm.sel (Syn.var 0) s t)) := hyp0
    have hE0 : MiPrf (M :: (E0 :: Γ).map NFm.shift)
        (.eq (Syn.shift (Syn.subst (inst zero) s)) (Syn.shift (Syn.subst (inst zero) t))) :=
      .hyp (List.mem_cons_of_mem _ List.mem_cons_self)
    have hE : MiPrf (M :: (E0 :: Γ).map NFm.shift) (.eq s t) :=
      eqTrans (eqSymm ((selBase s).weaken sub))
        (eqTrans (selCongr₃ _ _ hM) (eqTrans ((selNest s t).weaken sub)
          (eqTrans (selCongr₂ _ _ hE0) ((selBase t).weaken sub))))
    have hES := cut1 hE (π.weaken (List.cons_subset_cons _ sub))
    simp only [NFm.subst_eq] at hES
    show MiPrf _ (.eq (Syn.subst (repl (succ (Syn.var 0))) s)
      (Syn.subst (repl (succ (Syn.var 0))) (Tm.sel (Syn.var 0) s t)))
    simp only [Tm.subst_sel, Syn.subst_var, Syn.repl_zero]
    exact eqTrans hES (eqSymm (selSucc _ _ _))
  -- primitive progress for the lift, with a dummy witness coordinate
  have hQ : MiPrf (E0 :: Γ) (.Q M) := by
    have hD : MiPrf (E0 :: Γ) (.D (M.subst (up (fun i => Syn.var i.succ)))) := by
      have hm : NFm.IsMirror (M.subst (up (fun i => Syn.var i.succ))) :=
        ⟨Syn.subst (up (fun i => Syn.var i.succ)) s,
          Syn.subst (up (up (fun i => Syn.var i.succ))) (Syn.shift t), by
            show NFm.eq (Syn.subst (up (fun i => Syn.var i.succ)) s)
              (Syn.subst (up (fun i => Syn.var i.succ)) (iter (Tm.var 0) s (Syn.shift t))) = _
            rw [Tm.subst_iter]; rfl⟩
      refine .dI _ zero ?_
      rw [NFm.mstart, if_pos hm, NFm.subst_dummy_inst, NFm.subst_repl_var0]
      exact step
    refine .dE hD ?_
    show MiPrf (.Q (M.subst (up (fun i => Syn.var i.succ))) :: (E0 :: Γ).map NFm.shift)
      (.Q (M.subst (up (fun i => Syn.var i.succ))))
    exact hyp0
  -- `E(0) ⊢ E(S z)`, by `QE` at `S z`
  refine qI (.eq s t) ?_
  have h0 : MiPrf (E0 :: Γ) (M.subst (inst zero)) := by
    show MiPrf _ (.eq (Syn.subst (inst zero) s)
      (Syn.subst (inst zero) (Tm.sel (Syn.var 0) s t)))
    simp only [Tm.subst_sel, Syn.subst_var, Syn.inst_zero]
    exact eqSymm (selZero _ _)
  have h0' := h0.shift
  rw [NFm.shift_subst_inst_zero, ← NFm.subst_dummy_up_inst] at h0'
  have h := MiPrf.qE (succ (Syn.var 0)) hQ.shift h0'
  rw [NFm.subst_dummy_up_inst] at h
  have h' : MiPrf ((E0 :: Γ).map NFm.shift)
      (.eq (Syn.subst (repl (succ (Syn.var 0))) s)
        (Syn.subst (repl (succ (Syn.var 0))) (Tm.sel (Syn.var 0) s t))) := h
  simp only [Tm.subst_sel, Syn.subst_var, Syn.repl_zero] at h'
  exact eqTrans h' (selSucc _ _ _)

end MiPrf

theorem NPrf.toMiPrf (h : NPrf Γ A) : MiPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => exact .trOne h ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dICase B t _ ih => exact MiPrf.dICase B t ih
  | qIInd s t _ ih => exact MiPrf.qInd s t ih

/-- **The mirror introduction suffices**: `MiPrf` and the kernel derive the
same sequents. -/
theorem miprf_iff_nprf : MiPrf Γ A ↔ NPrf Γ A := ⟨MiPrf.toNPrf, NPrf.toMiPrf⟩

/-! ### The six-rule calculus of the package -/

/-- Derivability with reflexivity, Eval and the mirror introduction. -/
inductive M6Prf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : M6Prf Γ A
  | refl {n : ℕ} {Γ : List (NFm n)} (t : Tm n) : M6Prf Γ (.eq t t)
  | evalZero {n : ℕ} {Γ : List (NFm n)} (h : Tm (n + 1)) {a t r : Tm n}
      (h₁ : M6Prf Γ (.eq a t)) (h₂ : M6Prf Γ (.eq (iter zero a h) r)) : M6Prf Γ (.eq r t)
  | evalSucc {n : ℕ} {Γ : List (NFm n)} {c a : Tm n} {h : Tm (n + 1)} {t r : Tm n}
      (h₁ : M6Prf Γ (.eq (iter c a h) t)) (h₂ : M6Prf Γ (.eq (iter (succ c) a h) r)) :
      M6Prf Γ (.eq r (Syn.subst (inst t) h))
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : M6Prf Γ (.Q B)) (h₂ : M6Prf Γ (B.subst (inst zero))) : M6Prf Γ (B.subst (inst t))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : M6Prf Γ (.D B)) (h₂ : M6Prf (.Q B :: Γ.map NFm.shift) A.shift) : M6Prf Γ A
  | dI {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n)
      (h : M6Prf ((B.subst (up (inst t))).subst (repl (NFm.mstart B)) :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      M6Prf Γ (.D B)

namespace M6Prf

theorem evalId {s t r : Tm n} (h₁ : M6Prf Γ (.eq s t)) (h₂ : M6Prf Γ (.eq s r)) :
    M6Prf Γ (.eq r t) :=
  .evalZero (Syn.var 0) h₁ (.evalZero (Syn.var 0) h₂ (.refl _))

theorem eqSymm {s t : Tm n} (h : M6Prf Γ (.eq s t)) : M6Prf Γ (.eq t s) := evalId (.refl s) h

theorem eqTrans {s t u : Tm n} (h₁ : M6Prf Γ (.eq s t)) (h₂ : M6Prf Γ (.eq t u)) :
    M6Prf Γ (.eq s u) :=
  evalId h₂ (eqSymm h₁)

theorem iterZero (a : Tm n) (h : Tm (n + 1)) : M6Prf Γ (.eq (iter zero a h) a) :=
  .evalZero h (.refl a) (.refl _)

theorem iterSucc (c a : Tm n) (h : Tm (n + 1)) :
    M6Prf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h)) :=
  .evalSucc (.refl (iter c a h)) (.refl _)

theorem trOne (h : Tm (n + 1)) {s t u : Tm n} (h₁ : M6Prf Γ (.eq s t))
    (h₂ : M6Prf Γ (.eq (Syn.subst (inst s) h) u)) : M6Prf Γ (.eq u (Syn.subst (inst t) h)) :=
  .evalSucc (eqTrans (iterZero s h) h₁)
    (eqTrans (.evalSucc (iterZero s h) (.refl (iter (succ zero) s h))) h₂)

theorem ofMiPrf (h : MiPrf Γ A) : M6Prf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact iterZero a h
  | iterSucc c a h => exact iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => exact trOne h ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dI B t _ ih => exact .dI B t ih

theorem toNPrf (h : M6Prf Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | refl t => exact NPrf.eqRefl t
  | evalZero h _ _ ih₁ ih₂ =>
    exact NPrf.eqTrans (NPrf.eqSymm ih₂) (NPrf.eqTrans (.iterZero _ h) ih₁)
  | @evalSucc _ _ c a h t r _ _ ih₁ ih₂ =>
    exact NPrf.eqTrans (NPrf.eqSymm ih₂) (NPrf.eqTrans (.iterSucc c a h) (NPrf.eqCongr h ih₁))
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dI B t _ ih => exact .ofDIM B t ih

end M6Prf

/-- **Six rules with the mirror introduction** derive the same sequents as the
kernel. -/
theorem m6prf_iff_nprf : M6Prf Γ A ↔ NPrf Γ A :=
  ⟨M6Prf.toNPrf, fun h => M6Prf.ofMiPrf h.toMiPrf⟩

end LeanProofs.ConciseIPRA
