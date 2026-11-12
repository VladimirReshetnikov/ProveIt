import ConciseIPRA.NativeFullFive
import ConciseIPRA.NativeUniformClauses

/-!
# Three rule families with clauses on full normal forms

`WDPrf` is the calculus of the package `Research/witness_discharge` in its own
form.  Its formulas are equations and `D` over terms in full normal form, a
context is a list of clauses with at most one antecedent, and every context
contains the fixed reflexivity clause `[; y. y = y]`.  There are three rule
families:

* **Use**: from the antecedent of a clause of the context, if it has one,
  infer the full normal form of an instance of its consequent;
* **Intro**: from `B(t, η) ⊢ B(t, S z)` with `z` fresh infer `D_{x,y} B`, with
  the start `η` of `NativeOneIntro`;
* **Name**: from `D_{x,y} B`, and from `b = t` and `F` under the clause
  `[B(b, 0); y.B(b, y)]` with `b` fresh, infer the full normal form of
  `F[t/b]`, which must not mention `b`.

There is no `Q`, no computation rule, no transport rule, no reflexivity rule
and no separate elimination of `D`.

* `WDPrf.qfree`: from `Q`-free clauses only `Q`-free formulas are derivable;
* `wdprf_iff_nprf`: the kernel derives a sequent exactly when `WDPrf` derives
  the full normal form of its `Q`-free form (`NFm.unQ`) from the reflexivity
  clause and the corresponding assumptions;
* `wdprf_iff_nprf_of_qfree`: the same statement for `Q`-free sequents, where
  the `Q`-free form is the formula itself.

Soundness reads a clause as a native formula.  Completeness translates the
five-rule calculus `N5Prf` of `NativeFullFive`, which has formulas as
hypotheses and `Q` in the language: a hypothesis is kept as a derivation of
its `Q`-free form, the hypothesis `Q_y B(b, y)` of Name is the opened clause
(`WDPrf.ofClause`), and `QE` is Name at the fresh variable itself followed by a
use of that clause (`WDPrf.qE`).  The structural rules that this needs,
weakening and renaming, are direct inductions.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm
open Tm (zero succ iter)

variable {n m : ℕ}

namespace NFm

theorem qfree_full (A : NFm n) : A.full.QFree ↔ A.QFree := by
  induction A with
  | eq s t => exact Iff.rfl
  | Q B _ => exact Iff.rfl
  | D B ih => exact ih

/-- The `Q`-free form commutes with full normalization. -/
theorem unQ_full (A : NFm n) : unQ A.full = (unQ A).full := by
  induction A with
  | eq s t => rfl
  | Q B ih =>
    show NFm.D ((unQ B.full).subst (up fun i => Syn.var i.succ))
      = .D ((unQ B).subst (up fun i => Syn.var i.succ)).full
    rw [ih, Tm.up_rn Fin.succ, NFm.full_rn]
  | D B ih => exact congrArg NFm.D ih

/-- Full normalization commutes with a dummy witness coordinate. -/
theorem full_dummy (M : NFm (n + 1)) :
    (M.subst (up fun i => Syn.var i.succ)).full = M.full.subst (up fun i => Syn.var i.succ) := by
  rw [Tm.up_rn Fin.succ, NFm.full_rn]

end NFm

namespace UCl

def subst (c : UCl n) (σ : Fin n → Tm m) : UCl m :=
  ⟨c.ante.map fun A => A.subst σ, c.cons.subst (up σ)⟩

theorem subst_up_shift (c : UCl n) (σ : Fin n → Tm m) :
    c.shift.subst (up σ) = (c.subst σ).shift := by
  obtain ⟨a, b⟩ := c
  cases a with
  | none => exact congrArg (UCl.mk none) (NFm.subst_dummy_comm b σ).symm
  | some A =>
    show (⟨some (A.shift.subst (up σ)),
        (b.subst (up fun i => Syn.var i.succ)).subst (up (up σ))⟩ : UCl (m + 1))
      = ⟨some (A.subst σ).shift, (b.subst (up σ)).subst (up fun i => Syn.var i.succ)⟩
    rw [NFm.shift_subst_up, NFm.subst_dummy_comm]

theorem map_shift_subst (Γ : List (UCl n)) (σ : Fin n → Tm m) :
    (Γ.map shift).map (fun c => c.subst (up σ)) = (Γ.map fun c => c.subst σ).map shift := by
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun c _ => subst_up_shift c σ

theorem asm_subst (A : NFm n) (σ : Fin n → Tm m) : (asm A).subst σ = asm (A.subst σ) :=
  congrArg (UCl.mk none) (NFm.shift_subst_up A σ)

theorem map_toN_shift (Γ : List (UCl n)) :
    (Γ.map shift).map (fun c => c.toCl.toN) = (Γ.map fun c => c.toCl.toN).map NFm.shift := by
  rw [List.map_map, List.map_map]
  refine List.map_congr_left fun c _ => ?_
  show c.shift.toCl.toN = c.toCl.toN.shift
  rw [toCl_shift]
  exact Cl.toN_subst c.toCl _

theorem refl_mem_lift {Δ : List (UCl n)} (hr : refl ∈ Δ) (c : UCl (n + 1)) :
    refl ∈ c :: Δ.map shift :=
  List.mem_cons_of_mem _ (by rw [← refl_shift]; exact List.mem_map_of_mem hr)

end UCl

/-- Derivability with Use, Intro and Name on full normal forms. -/
inductive WDPrf : {n : ℕ} → List (UCl n) → NFm n → Prop
  /-- Use: from the antecedent of a clause, if it has one, infer the full
  normal form of an instance of its consequent. -/
  | use {n : ℕ} {Γ : List (UCl n)} {c : UCl n} (t : Tm n) (hc : c ∈ Γ)
      (h : ∀ A, c.ante = some A → WDPrf Γ A) : WDPrf Γ (c.cons.subst (inst t)).full
  /-- Intro: from `B(t, η) ⊢ B(t, S z)` with `z` fresh infer `D_{x,y} B`. -/
  | intro {n : ℕ} {Γ : List (UCl n)} (B : NFm (n + 2)) (t : Tm n) (hB : B.full = B)
      (hQ : B.QFree) (ht : t.full = t)
      (h : WDPrf (UCl.asm ((B.subst (up (inst t))).subst (repl (NFm.start B t))).full
          :: Γ.map UCl.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0)))).full) :
      WDPrf Γ (.D B)
  /-- Name: from `D_{x,y} B`, and from `b = t` and `F` under the clause
  `[B(b, 0); y.B(b, y)]` with `b` fresh, infer `F[t/b]`, which does not
  mention `b`. -/
  | name {n : ℕ} {Γ : List (UCl n)} {B : NFm (n + 2)} {A : NFm n} (F : NFm (n + 1))
      (t : Tm (n + 1)) (h₁ : WDPrf Γ (.D B))
      (h₂ : WDPrf (⟨some (B.subst (inst zero)).full, B⟩ :: Γ.map UCl.shift)
        (.eq (Syn.var 0) t))
      (h₃ : WDPrf (⟨some (B.subst (inst zero)).full, B⟩ :: Γ.map UCl.shift) F)
      (hA : (F.subst (repl t)).full = A.shift) : WDPrf Γ A

namespace WDPrf

variable {Γ Δ : List (UCl n)} {A : NFm n}

/-- From `Q`-free clauses only `Q`-free formulas are derivable. -/
theorem qfree (h : WDPrf Γ A) :
    (∀ c ∈ Γ, (∀ X, c.ante = some X → X.QFree) ∧ c.cons.QFree) → A.QFree := by
  induction h with
  | use t hc _ _ =>
    exact fun hΓ => (NFm.qfree_full _).2 ((NFm.qfree_subst _ _).2 (hΓ _ hc).2)
  | intro B t hB hQ ht _ _ => exact fun _ => hQ
  | @name _ Γ B A F t _ _ _ hA ih₁ _ ih₃ =>
    intro hΓ
    have hB : B.QFree := ih₁ hΓ
    have hF : F.QFree := ih₃ fun c hc => by
      rcases List.mem_cons.1 hc with rfl | hc
      · exact ⟨fun X hX => Option.some.inj hX ▸
          (NFm.qfree_full _).2 ((NFm.qfree_subst _ _).2 hB), hB⟩
      · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
        refine ⟨fun X hX => ?_, (NFm.qfree_subst _ _).2 (hΓ d hd).2⟩
        obtain ⟨X₀, hX₀, rfl⟩ := Option.map_eq_some_iff.1 hX
        exact (NFm.qfree_subst _ _).2 ((hΓ d hd).1 X₀ hX₀)
    have k := (NFm.qfree_full _).2 ((NFm.qfree_subst F (repl t)).2 hF)
    rw [hA] at k
    exact (NFm.qfree_subst A _).1 k

/-- Reflexivity, by the fixed clause. -/
theorem refl (hr : UCl.refl ∈ Γ) (t : Tm n) : WDPrf Γ (.eq t.full t.full) :=
  WDPrf.use (c := UCl.refl) t hr (fun A hA => by cases hA)

/-- An ordinary assumption of the context holds. -/
theorem asmHyp {X : NFm n} (hX : X.full = X) (h : UCl.asm X ∈ Γ) : WDPrf Γ X := by
  have k := WDPrf.use (c := UCl.asm X) zero h (fun A hA => by cases hA)
  have e : ((UCl.asm X).cons.subst (inst zero)).full = X := by
    show (X.shift.subst (inst zero)).full = X
    rw [NFm.subst_inst_shift, hX]
  rwa [e] at k

/-! ### Structural rules -/

theorem weaken (h : WDPrf Γ A) : ∀ {Δ : List (UCl n)}, Γ ⊆ Δ → WDPrf Δ A := by
  induction h with
  | use t hc _ ih => intro Δ s; exact .use t (s hc) fun A hA => ih A hA s
  | intro B t hB hQ ht _ ih =>
    intro Δ s
    exact .intro B t hB hQ ht (ih (List.cons_subset_cons _ (List.map_subset _ s)))
  | name F t _ _ _ hA ih₁ ih₂ ih₃ =>
    intro Δ s
    exact .name F t (ih₁ s) (ih₂ (List.cons_subset_cons _ (List.map_subset _ s)))
      (ih₃ (List.cons_subset_cons _ (List.map_subset _ s))) hA

theorem wk {c : UCl n} (h : WDPrf Γ A) : WDPrf (c :: Γ) A :=
  h.weaken (List.subset_cons_self _ _)

/-- Renaming of the free variables of a derivation. -/
theorem ren (h : WDPrf Γ A) : ∀ {m : ℕ} (ξ : Fin n → Fin m),
    WDPrf (Γ.map fun c => c.subst fun i => (Syn.var (ξ i) : Tm m))
      (A.subst fun i => (Syn.var (ξ i) : Tm m)) := by
  induction h with
  | @use _ Γ c t hc _ ih =>
    intro m ξ
    rw [← NFm.full_rn _ ξ, NFm.subst_inst]
    refine .use (c := c.subst fun i => (Syn.var (ξ i) : Tm m)) _
      (List.mem_map_of_mem (f := fun c : UCl _ => c.subst fun i => (Syn.var (ξ i) : Tm m)) hc)
      fun A hA => ?_
    obtain ⟨A₀, hA₀, rfl⟩ := Option.map_eq_some_iff.1 hA
    exact ih A₀ hA₀ ξ
  | @intro _ Γ B t hB hQ ht _ ih =>
    intro m ξ
    have h := ih (Tm.upRen ξ)
    rw [List.map_cons, UCl.asm_subst, ← NFm.full_rn _ (Tm.upRen ξ),
      ← NFm.full_rn _ (Tm.upRen ξ), ← Tm.up_rn, UCl.map_shift_subst, NFm.subst_repl_succ,
      NFm.subst_repl_up _ (NFm.start B t), NFm.subst_up_inst, ← NFm.start_rn] at h
    refine .intro _ _ ?_ ((NFm.qfree_subst _ _).2 hQ) ?_ h
    · rw [Tm.up_rn ξ, Tm.up_rn, NFm.full_rn, hB]
    · rw [Tm.full_rn, ht]
  | @name _ Γ B A F t _ _ _ hA ih₁ ih₂ ih₃ =>
    intro m ξ
    have e : ((⟨some (B.subst (inst zero)).full, B⟩ : UCl _) :: Γ.map UCl.shift).map
          (fun c => c.subst fun i => (Syn.var (Tm.upRen ξ i) : Tm (m + 1)))
        = ⟨some ((B.subst (up (up fun i => (Syn.var (ξ i) : Tm m)))).subst (inst zero)).full,
            B.subst (up (up fun i => (Syn.var (ξ i) : Tm m)))⟩
          :: (Γ.map fun c => c.subst fun i => (Syn.var (ξ i) : Tm m)).map UCl.shift := by
      have e1 : (⟨some (B.subst (inst zero)).full, B⟩ : UCl _).subst
            (fun i => (Syn.var (Tm.upRen ξ i) : Tm (m + 1)))
          = ⟨some ((B.subst (up (up fun i => (Syn.var (ξ i) : Tm m)))).subst (inst zero)).full,
              B.subst (up (up fun i => (Syn.var (ξ i) : Tm m)))⟩ := by
        show (⟨some ((B.subst (inst zero)).full.subst _), B.subst (up _)⟩ : UCl _) = _
        rw [← NFm.full_rn _ (Tm.upRen ξ), ← Tm.up_rn, NFm.subst_inst]
        rfl
      rw [List.map_cons, e1, ← Tm.up_rn, UCl.map_shift_subst]
    have h₂ := ih₂ (Tm.upRen ξ)
    have h₃ := ih₃ (Tm.upRen ξ)
    rw [e] at h₂ h₃
    refine .name (F.subst fun i => (Syn.var (Tm.upRen ξ i) : Tm (m + 1)))
      (Syn.subst (fun i => (Syn.var (Tm.upRen ξ i) : Tm (m + 1))) t) (ih₁ ξ) h₂ h₃ ?_
    have k : (F.subst (repl t)).full.subst (fun i => (Syn.var (Tm.upRen ξ i) : Tm (m + 1)))
        = A.shift.subst (fun i => (Syn.var (Tm.upRen ξ i) : Tm (m + 1))) := by rw [hA]
    rw [← NFm.full_rn _ (Tm.upRen ξ), ← Tm.up_rn, NFm.subst_repl_up, NFm.shift_subst_up] at k
    rw [← Tm.up_rn]
    exact k

theorem shift (h : WDPrf Γ A) : WDPrf (Γ.map UCl.shift) A.shift := h.ren Fin.succ

/-! ### Derived rules -/

/-- Elimination of `D`, by Name at the fresh variable itself. -/
theorem dE {B : NFm (n + 2)} (hr : UCl.refl ∈ Γ) (h₁ : WDPrf Γ (.D B))
    (h₂ : WDPrf (⟨some (B.subst (inst zero)).full, B⟩ :: Γ.map UCl.shift) A.shift)
    (hA : A.full = A) : WDPrf Γ A := by
  have r := WDPrf.refl (UCl.refl_mem_lift hr ⟨some (B.subst (inst zero)).full, B⟩) (Syn.var 0)
  rw [Tm.full_var] at r
  refine .name A.shift (Syn.var 0) h₁ r h₂ ?_
  rw [NFm.subst_repl_var, NFm.full_shift, hA]

/-- The clause opened by Name gives the `D` formula that stands for `Q`. -/
theorem ofClause (M : NFm (n + 1)) (hM : M.full = M) (hQ : M.QFree)
    (hc : (⟨some (M.subst (inst zero)).full, M⟩ : UCl n) ∈ Γ) :
    WDPrf Γ (.D (M.subst (up fun i => Syn.var i.succ))) := by
  refine .intro _ (succ zero) (by rw [NFm.full_dummy, hM]) ((NFm.qfree_subst _ _).2 hQ) rfl ?_
  rw [NFm.start_of_not (fun h => by cases h.2), NFm.subst_dummy_inst]
  have ha : WDPrf (UCl.asm (M.subst (repl zero)).full :: Γ.map UCl.shift)
      (M.subst (inst zero)).full.shift := by
    rw [← NFm.full_shift, NFm.shift_subst_inst_zero]
    exact asmHyp (NFm.full_idem _) List.mem_cons_self
  have k : WDPrf (UCl.asm (M.subst (repl zero)).full :: Γ.map UCl.shift)
      ((M.subst (up fun i => Syn.var i.succ)).subst (inst (succ (Syn.var 0)))).full :=
    WDPrf.use (c := (⟨some (M.subst (inst zero)).full, M⟩ : UCl n).shift)
      (succ (Syn.var 0)) (List.mem_cons_of_mem _ (List.mem_map_of_mem hc))
      (fun A hA => by obtain rfl := Option.some.inj hA; exact ha)
  rwa [NFm.subst_dummy_up_inst _ (succ (Syn.var 0))] at k

/-- `QE`, for the `D` formula that stands for `Q`. -/
theorem qE (hr : UCl.refl ∈ Γ) (M : NFm (n + 1)) (t : Tm n)
    (h₁ : WDPrf Γ (.D (M.subst (up fun i => Syn.var i.succ))))
    (h₂ : WDPrf Γ (M.subst (inst zero)).full) : WDPrf Γ (M.subst (inst t)).full := by
  refine dE hr h₁ ?_ (NFm.full_idem _)
  have ha : WDPrf (⟨some ((M.subst (up fun i => Syn.var i.succ)).subst (inst zero)).full,
        M.subst (up fun i => Syn.var i.succ)⟩ :: Γ.map UCl.shift)
      ((M.subst (up fun i => Syn.var i.succ)).subst (inst zero)).full := by
    rw [NFm.subst_dummy_up_inst, ← NFm.shift_subst_inst_zero, NFm.full_shift]
    exact h₂.shift.wk
  have k : WDPrf (⟨some ((M.subst (up fun i => Syn.var i.succ)).subst (inst zero)).full,
        M.subst (up fun i => Syn.var i.succ)⟩ :: Γ.map UCl.shift)
      ((M.subst (up fun i => Syn.var i.succ)).subst (inst (Syn.shift t))).full :=
    WDPrf.use (Syn.shift t) List.mem_cons_self
      (fun A hA => by obtain rfl := Option.some.inj hA; exact ha)
  rwa [NFm.subst_dummy_up_inst _ (Syn.shift t), ← NFm.shift_subst_inst, NFm.full_shift] at k

/-! ### Soundness in the kernel -/

theorem toNPrf (h : WDPrf Γ A) : NPrf (Γ.map fun c => c.toCl.toN) A := by
  induction h with
  | @use _ Γ c t hc _ ih =>
    refine (equivFull _).mp (NPrf.allE t (NPrf.impE
      (.hyp (List.mem_map_of_mem (f := fun c : UCl _ => c.toCl.toN) hc)) ?_))
    obtain ⟨a, b⟩ := c
    cases a with
    | none => exact NPrf.eqRefl zero
    | some X => exact ih X rfl
  | @intro _ Γ B t _ _ _ _ ih =>
    rw [List.map_cons, UCl.map_toN_shift] at ih
    exact .ofDI B t ((equivFull _).mpr
      (NPrf.cut1 (NPrf.asmClause ((equivFull _).mp NPrf.hyp0)) (NPrf.wkUnder ih)))
  | @name _ Γ B A F t _ _ _ hA ih₁ ih₂ ih₃ =>
    rw [List.map_cons, UCl.map_toN_shift] at ih₂ ih₃
    have cl : NPrf (.Q B :: (Γ.map fun c => c.toCl.toN).map NFm.shift)
        (NFm.imp (B.subst (inst zero)).full (NFm.all B)) :=
      NPrf.impI (NPrf.impE ((NPrf.qComp (NEquiv.refl B)).mpr NPrf.hyp0).wk
        ((equivFull _).mpr NPrf.hyp0))
    have k₂ := NPrf.cut1 cl (NPrf.wkUnder ih₂)
    have k₃ := NPrf.cut1 cl (NPrf.wkUnder ih₃)
    refine .dE ih₁ ?_
    have tr := NPrf.tr (F.subst (Fin.cases (Syn.var 0) fun i => Syn.var i.succ.succ)) k₂
      (by rw [NFm.subst_hole_inst, NFm.subst_repl_var]; exact k₃)
    rw [NFm.subst_hole_inst] at tr
    rw [← hA]
    exact (equivFull _).mp tr

/-- The invariant of the translation from the five-rule calculus, under one
more variable and one more clause. -/
theorem lift {Γ : List (NFm n)} (s : ∀ X ∈ Γ, WDPrf Δ (NFm.unQ X).full) {X' : NFm (n + 1)}
    {c' : UCl (n + 1)} (h' : WDPrf (c' :: Δ.map UCl.shift) (NFm.unQ X').full) :
    ∀ X ∈ X' :: Γ.map NFm.shift, WDPrf (c' :: Δ.map UCl.shift) (NFm.unQ X).full := by
  intro X hX
  rcases List.mem_cons.1 hX with rfl | hX
  · exact h'
  · obtain ⟨X₀, hX₀, rfl⟩ := List.mem_map.1 hX
    rw [NFm.unQ_shift, NFm.full_shift]
    exact (s X₀ hX₀).shift.wk

end WDPrf

/-! ### Completeness, from the five-rule calculus -/

/-- Every derivation with five rules, formulas as hypotheses and `Q` in the
language is a derivation with three rule families and clauses, once the
reflexivity clause is in the context and every hypothesis is derivable. -/
theorem N5Prf.toWD {Γ : List (NFm n)} {A : NFm n} (h : N5Prf Γ A) :
    ∀ {Δ : List (UCl n)}, UCl.refl ∈ Δ → (∀ X ∈ Γ, WDPrf Δ (NFm.unQ X).full) →
      WDPrf Δ (NFm.unQ A).full := by
  induction h with
  | hyp h => intro Δ _ s; exact s _ h
  | refl t =>
    intro Δ hr _
    show WDPrf Δ (.eq t.full.full t.full.full)
    rw [Tm.full_idem]
    exact WDPrf.refl hr t
  | @name _ Γ B A F t _ _ _ hA ih₁ ih₂ ih₃ =>
    intro Δ hr s
    have hM : (NFm.unQ B).full.full = (NFm.unQ B).full := NFm.full_idem _
    have hr' := UCl.refl_mem_lift hr
      ⟨some ((NFm.unQ B).full.subst (inst zero)).full, (NFm.unQ B).full⟩
    have s' := WDPrf.lift s (X' := .Q B)
      (c' := ⟨some ((NFm.unQ B).full.subst (inst zero)).full, (NFm.unQ B).full⟩) (by
        show WDPrf _ (.D ((NFm.unQ B).subst (up fun i => Syn.var i.succ)).full)
        rw [NFm.full_dummy]
        exact WDPrf.ofClause _ hM ((NFm.qfree_full _).2 (NFm.qfree_unQ B)) List.mem_cons_self)
    have h₂ : WDPrf _ (.eq (Tm.full (Syn.var 0)) t.full) := ih₂ hr' s'
    rw [Tm.full_var] at h₂
    refine .name (NFm.unQ F).full t.full (ih₁ hr s) h₂ (ih₃ hr' s') ?_
    have k : ((NFm.unQ F).subst (repl t)).full = (NFm.unQ A).shift := by
      rw [← NFm.unQ_subst, ← NFm.unQ_full, hA, NFm.unQ_shift]
    rw [← NFm.full_shift, ← k, NFm.full_idem]
    refine NFm.full_subst_congr (NFm.full_idem _) fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Tm.full_idem t
    · rfl
  | @qE _ Γ B t _ _ ih₁ ih₂ =>
    intro Δ hr s
    have e : ∀ u : Tm _, (NFm.unQ (B.subst (inst u)).full).full
        = ((NFm.unQ B).full.subst (inst u)).full := fun u => by
      rw [NFm.unQ_full, NFm.full_idem, NFm.unQ_subst]
      exact NFm.full_subst_congr (NFm.full_idem _).symm fun _ => rfl
    have h₁ : WDPrf Δ (.D ((NFm.unQ B).full.subst (up fun i => Syn.var i.succ))) := by
      rw [← NFm.full_dummy]
      exact ih₁ hr s
    rw [e]
    exact WDPrf.qE hr _ t h₁ (by rw [← e]; exact ih₂ hr s)
  | @dI _ Γ B t hB ht _ ih =>
    intro Δ hr s
    have hB' : (NFm.unQ B).full = NFm.unQ B := by rw [← NFm.unQ_full, hB]
    have e : ∀ {k : ℕ} (ρ : Fin _ → Tm k),
        (NFm.unQ ((B.subst (up (inst t))).subst ρ).full).full
          = (((NFm.unQ B).subst (up (inst t))).subst ρ).full := fun ρ => by
      rw [NFm.unQ_full, NFm.full_idem, NFm.unQ_subst, NFm.unQ_subst]
    show WDPrf Δ (.D (NFm.unQ B).full)
    rw [hB']
    refine .intro (NFm.unQ B) t hB' (NFm.qfree_unQ B) ht ?_
    rw [NFm.start_unQ]
    have k := ih (UCl.refl_mem_lift hr
        (UCl.asm (((NFm.unQ B).subst (up (inst t))).subst (repl (NFm.start B t))).full))
      (WDPrf.lift s (by rw [e]; exact WDPrf.asmHyp (NFm.full_idem _) List.mem_cons_self))
    rwa [e] at k

variable {Γ : List (NFm n)} {A : NFm n}

/-- **Three rule families with clauses.**  The kernel derives a sequent exactly
when Use, Intro and Name derive the full normal form of its `Q`-free form from
the reflexivity clause and the corresponding assumptions. -/
theorem wdprf_iff_nprf :
    WDPrf (UCl.refl :: Γ.map fun X => UCl.asm (NFm.unQ X).full) (NFm.unQ A).full ↔ NPrf Γ A := by
  constructor
  · intro h
    refine (NEquiv.unQ A).mp ((equivFull _).mpr (h.toNPrf.cut fun C hC => ?_))
    rw [List.map_cons, List.mem_cons] at hC
    rcases hC with rfl | hC
    · exact NPrf.impI (NPrf.allI (NPrf.eqRefl _))
    · rw [List.map_map, List.mem_map] at hC
      obtain ⟨X, hX, rfl⟩ := hC
      exact NPrf.asmClause ((equivFull _).mp ((NEquiv.unQ X).mpr (.hyp hX)))
  · intro h
    have k := (n5prf_iff_nprf.2 h).toWD
      (Δ := UCl.refl :: Γ.map fun X => UCl.asm (NFm.unQ X).full) List.mem_cons_self
      fun Y hY => by
        obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hY
        rw [NFm.unQ_full, NFm.full_idem]
        exact WDPrf.asmHyp (NFm.full_idem _) (List.mem_cons_of_mem _
          (List.mem_map_of_mem (f := fun X => UCl.asm (NFm.unQ X).full) hX))
    rwa [NFm.unQ_full, NFm.full_idem] at k

/-- On `Q`-free sequents the three rule families derive exactly what the kernel
derives, up to full normal forms. -/
theorem wdprf_iff_nprf_of_qfree (hΓ : ∀ X ∈ Γ, X.QFree) (hA : A.QFree) :
    WDPrf (UCl.refl :: Γ.map fun X => UCl.asm X.full) A.full ↔ NPrf Γ A := by
  have e : (Γ.map fun X => UCl.asm (NFm.unQ X).full) = Γ.map fun X => UCl.asm X.full :=
    List.map_congr_left fun X hX => by rw [NFm.unQ_of_qfree X (hΓ X hX)]
  rw [← wdprf_iff_nprf, e, NFm.unQ_of_qfree A hA]

/-- The three rule families prove a sequent in this form exactly when iPRA
proves its reading. -/
theorem wdprf_iff_pra :
    WDPrf (UCl.refl :: Γ.map fun X => UCl.asm (NFm.unQ X).full) (NFm.unQ A).full
      ↔ (Γ.map NFm.toPRA ⊢[PRAAx] A.toPRA) :=
  wdprf_iff_nprf.trans native_iff_pra

end LeanProofs.ConciseIPRA
