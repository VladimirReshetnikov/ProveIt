import ConciseIPRA.NativeModels

/-!
# The shape of the witness of `DI`

The introduction of `D` by cases names a witness, an arbitrary term.
`DWPrf z v` is the kernel in which that witness is restricted by its shape:
the literal `0` is allowed if `z` holds and a variable if `v` holds; no other
term is allowed.  Both restrictions taken alone are incomplete.

* `dwprf_zero_incomplete`: with the literal `0` alone the calculus does not
  derive `D_{x,y} (sel(y, 1, x) = 1)`, which the kernel derives at the witness
  `1`.  The calculus is sound for the standard reading in which `D_{x,y} B`
  means `B(0, 0) → ∀y B(0, y)` (`DWPrf.sound`).
* `dwprf_var_incomplete`: with variables alone the calculus derives no
  formula `D B` in the empty context without free variables, while the kernel
  derives `D_{x,y} (0 = 0)`.  The proof is syntactic: in such a context every
  derivable formula is an equation or a closure over an equation
  (`DWPrf.simple`), since the first `D` of a derivation needs a variable for
  its witness and the first variable needs a `D` or an equation.

Whether the two shapes together are enough is further question 2 of the
README; it is not settled here.  That calculus is closed under renaming and
not, as far as is known, under substitution.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

variable {n : ℕ}

/-- The admissible witnesses: the literal `0` if `z`, a variable if `v`. -/
def Tm.IsWit (z v : Bool) : {n : ℕ} → Tm n → Prop
  | _, .var _ => v = true
  | _, .zero => z = true
  | _, .succ _ => False
  | _, .iter _ _ _ => False

/-- The kernel with the witness of `DI` restricted by its shape. -/
inductive DWPrf (z v : Bool) : {n : ℕ} → List (NFm n) → NFm n → Prop
  | hyp {n : ℕ} {Γ : List (NFm n)} {A : NFm n} (h : A ∈ Γ) : DWPrf z v Γ A
  | iterZero {n : ℕ} {Γ : List (NFm n)} (a : Tm n) (h : Tm (n + 1)) :
      DWPrf z v Γ (.eq (iter zero a h) a)
  | iterSucc {n : ℕ} {Γ : List (NFm n)} (c a : Tm n) (h : Tm (n + 1)) :
      DWPrf z v Γ (.eq (iter (succ c) a h) (Syn.subst (inst (iter c a h)) h))
  | trOne {n : ℕ} {Γ : List (NFm n)} (h : Tm (n + 1)) {s t u : Tm n}
      (h₁ : DWPrf z v Γ (.eq s t)) (h₂ : DWPrf z v Γ (.eq (Syn.subst (inst s) h) u)) :
      DWPrf z v Γ (.eq u (Syn.subst (inst t) h))
  | qE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 1)} (t : Tm n)
      (h₁ : DWPrf z v Γ (.Q B)) (h₂ : DWPrf z v Γ (B.subst (inst zero))) :
      DWPrf z v Γ (B.subst (inst t))
  | dE {n : ℕ} {Γ : List (NFm n)} {B : NFm (n + 2)} {A : NFm n}
      (h₁ : DWPrf z v Γ (.D B)) (h₂ : DWPrf z v (.Q B :: Γ.map NFm.shift) A.shift) :
      DWPrf z v Γ A
  | dICase {n : ℕ} {Γ : List (NFm n)} (B : NFm (n + 2)) (t : Tm n) (hw : t.IsWit z v)
      (h : DWPrf z v (((B.subst (up (inst t))).subst (inst zero)).shift :: Γ.map NFm.shift)
        ((B.subst (up (inst t))).subst (repl (succ (var 0))))) :
      DWPrf z v Γ (.D B)
  | qIInd {n : ℕ} {Γ : List (NFm n)} (s₁ s₂ : Tm (n + 1))
      (h : DWPrf z v (NFm.eq s₁ s₂ :: Γ.map NFm.shift)
        ((NFm.eq s₁ s₂).subst (repl (succ (var 0))))) :
      DWPrf z v Γ (.Q (.eq s₁ s₂))

variable {z v : Bool} {Γ : List (NFm n)} {A : NFm n}

theorem DWPrf.toNPrf (h : DWPrf z v Γ A) : NPrf Γ A := by
  induction h with
  | hyp h => exact .hyp h
  | iterZero a h => exact .iterZero a h
  | iterSucc c a h => exact .iterSucc c a h
  | trOne h _ _ ih₁ ih₂ => exact .trOne h ih₁ ih₂
  | qE t _ _ ih₁ ih₂ => exact .qE t ih₁ ih₂
  | dE _ _ ih₁ ih₂ => exact .dE ih₁ ih₂
  | dICase B t _ _ ih => exact .dICase B t ih
  | qIInd s t _ ih => exact .qIInd s t ih

/-! ### The literal `0` alone -/

/-- With the literal `0` as the only witness the calculus is sound for every
reading that satisfies the conditions of the other seven rules and reads
`D_{x,y} B` as true whenever `B(0, 0)` implies `B(0, S z)` for all `z`. -/
theorem DWPrf.sound {S : Sem} (hS : S.Sound { Rules.all with dICase := false })
    (hD : ∀ P : ℕ → ℕ → Prop, (∀ y, P 0 0 → P 0 (y + 1)) → S.d P)
    (h : DWPrf true false Γ A) : ∀ ρ : Fin n → ℕ, (∀ X ∈ Γ, X.sat S ρ) → A.sat S ρ := by
  induction h with intro ρ hΓ
  | hyp h => exact hΓ _ h
  | iterZero a h => exact hS.iterZero rfl _ _
  | iterSucc c a h =>
    show S.eqv _ ((Syn.subst (inst (iter c a h)) h).val S ρ)
    rw [Tm.val_subst, Tm.val_inst]
    exact hS.iterSucc rfl _ _ _
  | trOne h _ _ ih₁ ih₂ =>
    have e₂ := ih₂ ρ hΓ
    simp only [NFm.sat, Tm.val_subst, Tm.val_inst] at e₂ ⊢
    exact hS.trOne rfl (fun x => h.val S (Fin.cases x ρ)) _ _ _ (ih₁ ρ hΓ) e₂
  | @qE _ Γ B t _ _ ih₁ ih₂ =>
    have h₂ := ih₂ ρ hΓ
    rw [NFm.sat_inst] at h₂ ⊢
    have hq : S.q fun y => B.sat S (Fin.cases y ρ) := ih₁ ρ hΓ
    exact hS.qE rfl _ _ hq h₂
  | @dE _ Γ B A _ _ ih₁ ih₂ =>
    refine hS.dE rfl _ _ (ih₁ ρ hΓ) fun b hq => ?_
    rw [← NFm.sat_shift S A b ρ]
    refine ih₂ (Fin.cases b ρ) fun X hX => ?_
    rcases List.mem_cons.1 hX with rfl | hX
    · exact hq
    · obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
      rw [NFm.sat_shift]
      exact hΓ Y hY
  | @dICase _ Γ B t hw _ ih =>
    cases t with
    | var i => cases hw
    | succ t => cases hw
    | iter c a g => cases hw
    | zero =>
      refine hD _ fun y h0 => ?_
      have h := ih (Fin.cases y ρ) fun X hX => by
        rcases List.mem_cons.1 hX with rfl | hX
        · rw [NFm.sat_shift, NFm.sat_inst, NFm.sat_up_inst]
          exact h0
        · obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
          rw [NFm.sat_shift]
          exact hΓ Y hY
      rw [NFm.sat_repl, NFm.sat_up_inst] at h
      exact h
  | @qIInd _ Γ s₁ s₂ _ ih =>
    refine hS.qIInd rfl (fun y => s₁.val S (Fin.cases y ρ)) (fun y => s₂.val S (Fin.cases y ρ))
      fun y hy => ?_
    have h := ih (Fin.cases y ρ) fun X hX => by
      rcases List.mem_cons.1 hX with rfl | hX
      · exact hy
      · obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
        rw [NFm.sat_shift]
        exact hΓ Y hY
    simp only [NFm.subst_eq, NFm.sat, Tm.val_subst, Tm.val_repl] at h
    exact h

/-- **The literal `0` alone is not enough.**  The kernel derives
`D_{x,y} (sel(y, 1, x) = 1)` at the witness `1`; with the witness `0` only it
is not derivable, by the standard reading with `D_{x,y} B` read at `x = 0`. -/
theorem dwprf_zero_incomplete :
    NPrf ([] : List (NFm 0)) (.D (.eq (Tm.sel (Syn.var 0) Tm.one (Syn.var 1)) Tm.one))
      ∧ ¬ DWPrf true false ([] : List (NFm 0))
        (.D (.eq (Tm.sel (Syn.var 0) Tm.one (Syn.var 1)) Tm.one)) := by
  refine ⟨.dICase _ Tm.one (NPrf.selSucc (Syn.var 0) Tm.one Tm.one), fun h => ?_⟩
  have hS : Sem.Sound { Sem.std with d := fun P => P 0 0 → ∀ y, P 0 y }
      { Rules.all with dICase := false } :=
    { Sem.std_sound _ with
      dE := fun _ _ _ hd H => H 0 hd
      dICase := fun e => absurd e (by decide) }
  have k := h.sound hS (fun P H h0 y => by
    cases y with
    | zero => exact h0
    | succ y => exact H y h0) (fun i => i.elim0) (fun _ hX => nomatch hX)
  exact Nat.zero_ne_one (k rfl 1)

/-! ### Variables alone -/

/-- An equation or a closure over an equation. -/
def NFm.Simple : {n : ℕ} → NFm n → Prop
  | _, .eq _ _ => True
  | _, .Q (.eq _ _) => True
  | _, _ => False

/-- With variables as the only witnesses, a context without free variables
that consists of equations and closures over equations derives only such
formulas. -/
theorem DWPrf.simple (h : DWPrf false true Γ A) :
    n = 0 → (∀ C ∈ Γ, C.Simple) → A.Simple := by
  induction h with intro hn hΓ
  | hyp h => exact hΓ _ h
  | iterZero a h => trivial
  | iterSucc c a h => trivial
  | trOne h _ _ ih₁ ih₂ => trivial
  | @qE _ Γ B t _ _ ih₁ ih₂ =>
    cases B with
    | eq a b => trivial
    | Q B' => exact (ih₁ hn hΓ).elim
    | D B' => exact (ih₁ hn hΓ).elim
  | dE _ _ ih₁ ih₂ => exact (ih₁ hn hΓ).elim
  | dICase B t hw _ ih =>
    subst hn
    cases t with
    | var i => exact i.elim0
    | zero => cases hw
    | succ t => cases hw
    | iter c a g => cases hw
  | qIInd s₁ s₂ _ ih => trivial

/-- **Variables alone are not enough.**  The kernel derives `D_{x,y} (0 = 0)`
in the empty context; with variables as the only witnesses no formula `D B`
is derivable there. -/
theorem dwprf_var_incomplete :
    NPrf ([] : List (NFm 0)) (.D (.eq zero zero))
      ∧ ¬ DWPrf false true ([] : List (NFm 0)) (.D (.eq zero zero)) :=
  ⟨.dICase _ zero (NPrf.eqRefl zero), fun h => h.simple rfl (fun _ hX => nomatch hX)⟩

end LeanProofs.ConciseIPRA
