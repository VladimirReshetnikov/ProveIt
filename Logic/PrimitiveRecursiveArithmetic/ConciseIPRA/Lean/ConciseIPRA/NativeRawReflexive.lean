import ConciseIPRA.NativeMirror
import ConciseIPRA.NativeZeroReflexive

/-!
# The reflexive-base introduction on raw terms

`RRPrf` is the raw seven-rule variant of the package `Research/reflexive_base`
(`report.tex`, "The same guard on raw syntax").  Terms and formulas are those
of the kernel, with ordinary substitution and no normalization.  The rules
are hypothesis, the two computation equations, transport in one term, `QE`,
`DE`, and one introduction

  `dI`: from `Γ, B(t, η) ⊢ B(t, S z)` with `z` fresh infer `D_{x,y} B`,

where `η = z` exactly when the zero instance `B(t, 0)` of the matrix is
literally an equation `r = r`, and `η = 0` otherwise.

`rrprf_iff_nprf` proves that `RRPrf` derives the same sequents as the kernel.

* The test is not stable under substitution: a substitution can make the two
  sides of `B(t, 0)` equal.  An injective renaming preserves and reflects it
  (`NFm.isRefl_rn`), which is what weakening under a binder and cut need, as
  in `NativeMirror`.
* `D` by cases at a matrix with a reflexive base: the hypothesis of the case
  step is an instance of reflexivity, so it is cut and the progress step
  applies.
* `Q` by progress for an arbitrary equation `E(y) = (s = t)` uses the
  asymmetric lift of the package,

    `K(y) = (sel(y, t, s) = sel(0, t, s))`,

  whose zero instance is literally reflexive, so progress for `K` is
  primitive.  At a successor `K` computes to `E`.  With the base `E(0)`
  retained, the two decoder equations

    `sel(y, s(0), sel(y, t, s)) = s`,   `sel(y, s(0), sel(0, t, s)) = t`,

  each proved by cases on `y`, turn `K(z)` into `E(z)`.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

variable {n m : ℕ}

namespace NFm

/-- An injective renaming preserves and reflects literal reflexivity. -/
theorem isRefl_rn {ξ : Fin n → Fin m} (hξ : Function.Injective ξ) (X : NFm n) :
    IsRefl (X.subst fun i => (Syn.var (ξ i) : Tm m)) ↔ IsRefl X := by
  constructor
  · rintro ⟨r, e⟩
    cases X with
    | eq a b =>
      simp only [NFm.subst_eq, NFm.eq.injEq] at e
      have hab : a = b := Tm.ren_inj a hξ b (by
        rw [Tm.ren_eq_sub, Tm.ren_eq_sub]
        exact e.1.trans e.2.symm)
      exact ⟨a, by rw [hab]⟩
    | Q B => simp only [NFm.subst_Q, reduceCtorEq] at e
    | D B => simp only [NFm.subst_D, reduceCtorEq] at e
  · rintro ⟨r, rfl⟩
    exact ⟨_, rfl⟩

open Classical in
/-- The start of the raw reflexive-base introduction: the fresh variable when
the zero instance of the matrix is literally reflexive, `0` otherwise. -/
noncomputable def rrs (B : NFm (n + 2)) (t : Tm n) : Tm (n + 1) :=
  if IsRefl ((B.subst (up (inst t))).subst (inst zero)) then Syn.var 0 else zero

theorem rrs_rn {ξ : Fin n → Fin m} (hξ : Function.Injective ξ) (B : NFm (n + 2)) (t : Tm n) :
    rrs (B.subst (up (up fun i => (Syn.var (ξ i) : Tm m))))
        (Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) t)
      = Syn.subst (up fun i => (Syn.var (ξ i) : Tm m)) (rrs B t) := by
  have e : ((B.subst (up (up fun i => (Syn.var (ξ i) : Tm m)))).subst
        (up (inst (Syn.subst (fun i => (Syn.var (ξ i) : Tm m)) t)))).subst (inst zero)
      = ((B.subst (up (inst t))).subst (inst zero)).subst
        fun i => (Syn.var (ξ i) : Tm m) := by
    rw [NFm.subst_inst, NFm.subst_up_inst, Tm.subst_zero]
  by_cases hr : IsRefl ((B.subst (up (inst t))).subst (inst zero))
  · rw [rrs, e, if_pos ((isRefl_rn hξ _).2 hr), rrs, if_pos hr]; simp
  · rw [rrs, e, if_neg (fun h => hr ((isRefl_rn hξ _).1 h)), rrs, if_neg hr]; simp

end NFm

/-- Derivability with one introduction rule whose mode is determined by the
literal reflexivity of the zero instance of the matrix. -/
inductive RRPrf : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : RRPrf Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      RRPrf Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      RRPrf Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  | trOne {n : ℕ} {Γ : List (NFm n)} (h : Tm (n + 1)) {s t u : Tm n}
      (h₁ : RRPrf Γ (.eq s t)) (h₂ : RRPrf Γ (.eq (Syn.subst (inst s) h) u)) :
      RRPrf Γ (.eq u (Syn.subst (inst t) h))
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : RRPrf Γ (.Q B)) (h₂ : RRPrf Γ (B.subst (inst zero))) : RRPrf Γ (B.subst (inst t))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : RRPrf Γ (.D B)) (h₂ : RRPrf (.Q B :: Γ.map NFm.shift) A.shift) : RRPrf Γ A
  /-- DI: from `B(t, η) ⊢ B(t, S z)` with `z` fresh infer `D_{x,y} B`, where
  `η = z` when `B(t, 0)` is literally `r = r` and `η = 0` otherwise. -/
  | dI {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n)
      (h : RRPrf ((B.subst (up (inst t))).subst (repl (NFm.rrs B t)) :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      RRPrf Γ (.D B)

variable {Γ Δ : List (NFm n)} {A : NFm n}

namespace RRPrf

/-- Every rule is a derived rule of the kernel. -/
theorem toNPrf (h : RRPrf Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => exact .trOne h ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dI B t _ ih =>
    by_cases hr : NFm.IsRefl ((B.subst (up (inst t))).subst (inst zero))
    · rw [NFm.rrs, if_pos hr, NFm.subst_repl_var0] at ih
      cases B with
      | eq a b => exact .dIProg _ _ t ih
      | Q B' =>
        obtain ⟨r, e⟩ := hr
        simp only [NFm.subst_Q, reduceCtorEq] at e
      | D B' =>
        obtain ⟨r, e⟩ := hr
        simp only [NFm.subst_D, reduceCtorEq] at e
    · rw [NFm.rrs, if_neg hr, ← NFm.shift_subst_inst_zero] at ih
      exact .dICase B t ih

/-! ### Structural rules -/

theorem hyp0 : RRPrf (A :: Γ) A := .hyp List.mem_cons_self

theorem weaken (h : RRPrf Γ A) : ∀ {Δ : List (NFm n)}, Γ ⊆ Δ → RRPrf Δ A := by
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

theorem wk {B : NFm n} (h : RRPrf Γ A) : RRPrf (B :: Γ) A :=
  h.weaken (List.subset_cons_self _ _)

/-- Injective renaming of the free variables of a derivation. -/
theorem ren (h : RRPrf Γ A) : ∀ {m : ℕ} (ξ : Fin n → Fin m), Function.Injective ξ →
    RRPrf (Γ.map fun B => B.subst fun i => (Syn.var (ξ i) : Tm m))
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
      NFm.subst_repl_up _ (NFm.rrs B t), NFm.subst_up_inst, ← NFm.rrs_rn hξ] at h
    exact .dI _ _ h

theorem shift (h : RRPrf Γ A) : RRPrf (Γ.map NFm.shift) A.shift :=
  h.ren Fin.succ (Fin.succ_injective _)

theorem cutLift (h : ∀ B ∈ Γ, RRPrf Δ B) (C : NFm (n + 1)) :
    ∀ B ∈ C :: Γ.map NFm.shift, RRPrf (C :: Δ.map NFm.shift) B := by
  intro B hB
  rcases List.mem_cons.1 hB with rfl | hB
  · exact hyp0
  · obtain ⟨B₀, hB₀, rfl⟩ := List.mem_map.1 hB
    exact (h B₀ hB₀).shift.wk

theorem cut (h : RRPrf Γ A) : ∀ {Δ : List (NFm n)}, (∀ B ∈ Γ, RRPrf Δ B) → RRPrf Δ A := by
  induction h with
  | hyp h => intro Δ hΔ; exact hΔ _ h
  | iterZero a h => intro Δ _; exact .iterZero a h
  | iterSucc c a h => intro Δ _; exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => intro Δ hΔ; exact .trOne h (ih₁ hΔ) (ih₂ hΔ)
  | qE t _ _ ih₁ ih₂ => intro Δ hΔ; exact .qE t (ih₁ hΔ) (ih₂ hΔ)
  | dE _ _ ih₁ ih₂ => intro Δ hΔ; exact .dE (ih₁ hΔ) (ih₂ (cutLift hΔ _))
  | dI B t _ ih => intro Δ hΔ; exact .dI B t (ih (cutLift hΔ _))

theorem cut1 {B : NFm n} (h₁ : RRPrf Γ B) (h₂ : RRPrf (B :: Γ) A) : RRPrf Γ A := by
  refine h₂.cut fun C hC => ?_
  rcases List.mem_cons.1 hC with rfl | hC
  · exact h₁
  · exact .hyp hC

/-! ### Equality and the selector -/

theorem eqRefl (t : Tm n) : RRPrf Γ (.eq t t) :=
  .trOne (Syn.var 0) (.iterZero t (Syn.var 0)) (.iterZero t (Syn.var 0))

theorem eqSymm {s t : Tm n} (h : RRPrf Γ (.eq s t)) : RRPrf Γ (.eq t s) :=
  .trOne (Syn.var 0) (eqRefl s) h

theorem eqTrans {s t u : Tm n} (h₁ : RRPrf Γ (.eq s t)) (h₂ : RRPrf Γ (.eq t u)) :
    RRPrf Γ (.eq s u) :=
  .trOne (Syn.var 0) h₂ (eqSymm h₁)

theorem eqCongr (h : Tm (n + 1)) {s t : Tm n} (e : RRPrf Γ (.eq s t)) :
    RRPrf Γ (.eq (Syn.subst (inst s) h) (Syn.subst (inst t) h)) :=
  .trOne h e (eqRefl _)

theorem selZero (a b : Tm n) : RRPrf Γ (.eq (Tm.sel zero a b) a) := .iterZero a _

theorem selSucc (c a b : Tm n) : RRPrf Γ (.eq (Tm.sel (succ c) a b) b) := by
  have h := RRPrf.iterSucc (Γ := Γ) c a (Syn.shift b)
  rwa [Syn.subst_inst_shift] at h

theorem selCongr₃ (c a : Tm n) {b b' : Tm n} (e : RRPrf Γ (.eq b b')) :
    RRPrf Γ (.eq (Tm.sel c a b) (Tm.sel c a b')) := by
  have h := eqCongr (Tm.sel (Syn.shift c) (Syn.shift a) (Syn.var 0)) e
  simpa only [Tm.subst_sel, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using h

/-! ### `D` by cases, for every matrix -/

theorem dICase (B : NFm (n + 2)) (t : Tm n)
    (h : RRPrf (((B.subst (up (inst t))).subst (inst zero)).shift :: Γ.map NFm.shift)
      ((B.subst (up (inst t))).subst (repl (succ (Syn.var 0))))) : RRPrf Γ (.D B) := by
  refine .dI B t ?_
  by_cases hr : NFm.IsRefl ((B.subst (up (inst t))).subst (inst zero))
  · -- the base is an instance of reflexivity
    rw [NFm.rrs, if_pos hr]
    have hb : RRPrf Γ ((B.subst (up (inst t))).subst (inst zero)) := by
      obtain ⟨r, e⟩ := hr
      rw [e]
      exact eqRefl r
    exact (cut1 hb.shift h).wk
  · rw [NFm.rrs, if_neg hr, ← NFm.shift_subst_inst_zero]
    exact h

theorem qI (B : NFm (n + 1))
    (h : RRPrf ((B.subst (inst zero)).shift :: Γ.map NFm.shift)
      (B.subst (repl (succ (Syn.var 0))))) : RRPrf Γ (.Q B) := by
  have hD : RRPrf Γ (.D (B.subst (up (fun i => Syn.var i.succ)))) := by
    refine dICase _ zero ?_
    rw [NFm.subst_dummy_inst]
    exact h
  refine .dE hD ?_
  show RRPrf (.Q (B.subst (up (fun i => Syn.var i.succ))) :: Γ.map NFm.shift)
    (.Q (B.subst (up (fun i => Syn.var i.succ))))
  exact hyp0

/-- Cases on the last variable. -/
theorem casesVar (E : NFm (n + 1)) (h0 : RRPrf Γ (E.subst (inst zero)))
    (hS : RRPrf (Γ.map NFm.shift) (E.subst (repl (succ (Syn.var 0))))) :
    RRPrf (Γ.map NFm.shift) E := by
  have hQ : RRPrf (Γ.map NFm.shift) (.Q (E.subst (up (fun i => Syn.var i.succ)))) :=
    (qI E hS.wk).shift
  have h0' := h0.shift
  rw [NFm.shift_subst_inst_zero, ← NFm.subst_dummy_up_inst] at h0'
  have h := RRPrf.qE (Syn.var 0) hQ h0'
  rwa [NFm.subst_up_inst_var] at h

/-! ### `Q` by progress, for every equation -/

/-- The first decoder: `sel(y, s(0), sel(y, t, s)) = s`, unconditionally. -/
theorem decS (s t : Tm (n + 1)) :
    RRPrf (Γ.map NFm.shift)
      (.eq (Tm.sel (Syn.var 0) (Syn.shift (Syn.subst (inst zero) s))
        (Tm.sel (Syn.var 0) t s)) s) := by
  refine casesVar _ ?_ ?_
  · simp only [NFm.subst_eq, Tm.subst_sel, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
    exact selZero _ _
  · simp only [NFm.subst_eq, Tm.subst_sel, Syn.subst_var, Syn.repl_zero, Syn.subst_repl_shift]
    exact eqTrans (selSucc _ _ _) (selSucc _ _ _)

/-- The second decoder: `sel(y, s(0), sel(0, t, s)) = t`, from the base
`s(0) = t(0)`. -/
theorem decT (s t : Tm (n + 1)) :
    RRPrf (((NFm.eq s t).subst (inst zero) :: Γ).map NFm.shift)
      (.eq (Tm.sel (Syn.var 0) (Syn.shift (Syn.subst (inst zero) s))
        (Tm.sel zero t s)) t) := by
  refine casesVar _ ?_ ?_
  · simp only [NFm.subst_eq, Tm.subst_sel, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
      Tm.subst_zero]
    exact eqTrans (selZero _ _) hyp0
  · simp only [NFm.subst_eq, Tm.subst_sel, Syn.subst_var, Syn.repl_zero, Syn.subst_repl_shift,
      Tm.subst_zero]
    exact eqTrans (selSucc _ _ _) (selZero _ _)

/-- `Q` by progress: from `E(z) ⊢ E(S z)` infer `Q_y E(y)`, for every literal
equation `E`. -/
theorem qInd (s t : Tm (n + 1))
    (π : RRPrf (NFm.eq s t :: Γ.map NFm.shift) ((NFm.eq s t).subst (repl (succ (Syn.var 0))))) :
    RRPrf Γ (.Q (.eq s t)) := by
  -- the retained base and the asymmetric lift
  let E0 : NFm n := (NFm.eq s t).subst (inst zero)
  let K : NFm (n + 1) := .eq (Tm.sel (Syn.var 0) t s) (Tm.sel zero t s)
  have step : RRPrf (K :: (E0 :: Γ).map NFm.shift) (K.subst (repl (succ (Syn.var 0)))) := by
    have sub : Γ.map NFm.shift ⊆ K :: (E0 :: Γ).map NFm.shift := fun X hX =>
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hX)
    have hK : RRPrf (K :: (E0 :: Γ).map NFm.shift)
        (.eq (Tm.sel (Syn.var 0) t s) (Tm.sel zero t s)) := hyp0
    have hE : RRPrf (K :: (E0 :: Γ).map NFm.shift) (.eq s t) :=
      eqTrans (eqSymm ((decS s t).weaken sub))
        (eqTrans (selCongr₃ _ _ hK) (decT s t).wk)
    have hES := cut1 hE (π.weaken (List.cons_subset_cons _ sub))
    simp only [NFm.subst_eq] at hES
    show RRPrf _ (.eq (Syn.subst (repl (succ (Syn.var 0))) (Tm.sel (Syn.var 0) t s))
      (Syn.subst (repl (succ (Syn.var 0))) (Tm.sel zero t s)))
    simp only [Tm.subst_sel, Syn.subst_var, Syn.repl_zero, Tm.subst_zero]
    exact eqTrans (selSucc _ _ _) (eqTrans hES (eqSymm (selZero _ _)))
  -- the zero instance of the lift is literally reflexive
  have hK0 : (NFm.eq (Tm.sel (Syn.var 0) t s) (Tm.sel zero t s)).subst (inst zero)
      = .eq (Tm.sel zero (Syn.subst (inst zero) t) (Syn.subst (inst zero) s))
        (Tm.sel zero (Syn.subst (inst zero) t) (Syn.subst (inst zero) s)) := by
    simp only [NFm.subst_eq, Tm.subst_sel, Syn.subst_var, Syn.inst_zero, Tm.subst_zero]
  -- primitive progress for the lift, with a dummy witness coordinate
  have hQ : RRPrf (E0 :: Γ) (.Q K) := by
    have hD : RRPrf (E0 :: Γ) (.D (K.subst (up (fun i => Syn.var i.succ)))) := by
      have hr : NFm.IsRefl (((K.subst (up (fun i => Syn.var i.succ))).subst
          (up (inst zero))).subst (inst zero)) := by
        rw [NFm.subst_dummy_inst]
        exact ⟨_, hK0⟩
      refine .dI _ zero ?_
      rw [NFm.rrs, if_pos hr, NFm.subst_dummy_inst, NFm.subst_repl_var0]
      exact step
    refine .dE hD ?_
    show RRPrf (.Q (K.subst (up (fun i => Syn.var i.succ))) :: (E0 :: Γ).map NFm.shift)
      (.Q (K.subst (up (fun i => Syn.var i.succ))))
    exact hyp0
  -- `E(0) ⊢ E(S z)`, by `QE` at `S z`
  refine qI (.eq s t) ?_
  have h0 : RRPrf (E0 :: Γ) (K.subst (inst zero)) := by
    show RRPrf _ ((NFm.eq (Tm.sel (Syn.var 0) t s) (Tm.sel zero t s)).subst (inst zero))
    rw [hK0]
    exact eqRefl _
  have h0' := h0.shift
  rw [NFm.shift_subst_inst_zero, ← NFm.subst_dummy_up_inst] at h0'
  have h := RRPrf.qE (succ (Syn.var 0)) hQ.shift h0'
  rw [NFm.subst_dummy_up_inst] at h
  have h' : RRPrf ((E0 :: Γ).map NFm.shift)
      (.eq (Syn.subst (repl (succ (Syn.var 0))) (Tm.sel (Syn.var 0) t s))
        (Syn.subst (repl (succ (Syn.var 0))) (Tm.sel zero t s))) := h
  simp only [Tm.subst_sel, Syn.subst_var, Syn.repl_zero, Tm.subst_zero] at h'
  exact eqTrans (eqSymm (selSucc _ _ _)) (eqTrans h' (selZero _ _))

end RRPrf

theorem NPrf.toRRPrf (h : NPrf Γ A) : RRPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => exact .trOne h ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dICase B t _ ih => exact RRPrf.dICase B t ih
  | qIInd s t _ ih => exact RRPrf.qInd s t ih

/-- **The reflexive-base introduction suffices on raw terms**: `RRPrf` and the
kernel derive the same sequents. -/
theorem rrprf_iff_nprf : RRPrf Γ A ↔ NPrf Γ A := ⟨RRPrf.toNPrf, NPrf.toRRPrf⟩

/-- The seven raw rules derive a sequent exactly when iPRA proves its
reading. -/
theorem rrprf_iff_pra : RRPrf Γ A ↔ (Γ.map NFm.toPRA ⊢[PRAAx] A.toPRA) :=
  rrprf_iff_nprf.trans native_iff_pra

end LeanProofs.ConciseIPRA
