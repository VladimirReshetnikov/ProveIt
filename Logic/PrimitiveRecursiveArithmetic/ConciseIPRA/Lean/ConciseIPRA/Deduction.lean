import ConciseIPRA.Syntax

/-!
# Intuitionistic natural deduction with equality

`Prf Ax Γ φ` is derivability of `φ` from the hypotheses `Γ` in intuitionistic
first-order logic with equality over the theory `Ax`.  Everything is scoped:
a sequent lives over a fixed number `n` of free variables, and the quantifier
rules move between `n` and `n + 1`.

A theory is a family of open axioms.  The axiom rule instantiates the free
variables of an axiom by arbitrary terms, so an axiom is read universally and
derivability is closed under substitution for every theory (`Prf.subst`).

Equality is governed by reflexivity and a simultaneous Leibniz rule: two
pointwise provably equal substitutions may be exchanged in any formula.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm

variable {T : ℕ → Type} [Syn T]

/-- A theory: a family of open axioms, one set for each number of free
variables. -/
abbrev Theory (T : ℕ → Type) := (k : ℕ) → Fm T k → Prop

/-- Intuitionistic natural deduction with equality over a theory. -/
inductive Prf (Ax : Theory T) : {n : ℕ} → List (Fm T n) → Fm T n → Prop
  | hyp {n : ℕ} {Γ : List (Fm T n)} {φ : Fm T n} (h : φ ∈ Γ) : Prf Ax Γ φ
  | ax {n k : ℕ} {Γ : List (Fm T n)} {φ : Fm T k} (h : Ax k φ) (σ : Fin k → T n) :
      Prf Ax Γ (φ.subst σ)
  | botE {n : ℕ} {Γ : List (Fm T n)} (φ : Fm T n) (h : Prf Ax Γ Fm.bot) : Prf Ax Γ φ
  | andI {n : ℕ} {Γ : List (Fm T n)} {φ ψ : Fm T n}
      (h₁ : Prf Ax Γ φ) (h₂ : Prf Ax Γ ψ) : Prf Ax Γ (φ ⋏ ψ)
  | andE₁ {n : ℕ} {Γ : List (Fm T n)} {φ ψ : Fm T n} (h : Prf Ax Γ (φ ⋏ ψ)) : Prf Ax Γ φ
  | andE₂ {n : ℕ} {Γ : List (Fm T n)} {φ ψ : Fm T n} (h : Prf Ax Γ (φ ⋏ ψ)) : Prf Ax Γ ψ
  | orI₁ {n : ℕ} {Γ : List (Fm T n)} {φ ψ : Fm T n} (h : Prf Ax Γ φ) : Prf Ax Γ (φ ⋎ ψ)
  | orI₂ {n : ℕ} {Γ : List (Fm T n)} {φ ψ : Fm T n} (h : Prf Ax Γ ψ) : Prf Ax Γ (φ ⋎ ψ)
  | orE {n : ℕ} {Γ : List (Fm T n)} {φ ψ χ : Fm T n} (h : Prf Ax Γ (φ ⋎ ψ))
      (h₁ : Prf Ax (φ :: Γ) χ) (h₂ : Prf Ax (ψ :: Γ) χ) : Prf Ax Γ χ
  | impI {n : ℕ} {Γ : List (Fm T n)} {φ ψ : Fm T n} (h : Prf Ax (φ :: Γ) ψ) :
      Prf Ax Γ (φ ⟶ ψ)
  | impE {n : ℕ} {Γ : List (Fm T n)} {φ ψ : Fm T n}
      (h₁ : Prf Ax Γ (φ ⟶ ψ)) (h₂ : Prf Ax Γ φ) : Prf Ax Γ ψ
  | allI {n : ℕ} {Γ : List (Fm T n)} {φ : Fm T (n + 1)}
      (h : Prf Ax (Γ.map Fm.shift) φ) : Prf Ax Γ (Fm.all φ)
  | allE {n : ℕ} {Γ : List (Fm T n)} {φ : Fm T (n + 1)} (t : T n)
      (h : Prf Ax Γ (Fm.all φ)) : Prf Ax Γ (φ.subst (inst t))
  | exI {n : ℕ} {Γ : List (Fm T n)} {φ : Fm T (n + 1)} (t : T n)
      (h : Prf Ax Γ (φ.subst (inst t))) : Prf Ax Γ (Fm.ex φ)
  | exE {n : ℕ} {Γ : List (Fm T n)} {φ : Fm T (n + 1)} {ψ : Fm T n}
      (h₁ : Prf Ax Γ (Fm.ex φ)) (h₂ : Prf Ax (φ :: Γ.map Fm.shift) ψ.shift) : Prf Ax Γ ψ
  | eqRefl {n : ℕ} {Γ : List (Fm T n)} (t : T n) : Prf Ax Γ (t ≐ t)
  | eqSubst {n k : ℕ} {Γ : List (Fm T n)} (φ : Fm T k) (σ σ' : Fin k → T n)
      (h₁ : ∀ i, Prf Ax Γ (σ i ≐ σ' i)) (h₂ : Prf Ax Γ (φ.subst σ)) :
      Prf Ax Γ (φ.subst σ')

@[inherit_doc] scoped notation:20 Γ:21 " ⊢[" Ax "] " φ:20 => Prf Ax Γ φ

namespace Fm

variable {n m : ℕ}

theorem map_shift_subst (Γ : List (Fm T n)) (σ : Fin n → T m) :
    (Γ.map Fm.shift).map (fun φ => φ.subst (up σ))
      = (Γ.map (fun φ => φ.subst σ)).map Fm.shift := by
  induction Γ with
  | nil => rfl
  | cons φ Γ ih => simp only [List.map_cons, ih, Fm.shift_subst_up]

/-- Opening a binder and instantiating it by its own variable is the identity. -/
theorem subst_up_succ_inst (φ : Fm T (n + 1)) :
    (φ.subst (up (fun i => var i.succ))).subst (inst (var 0)) = φ := by
  have e : (fun i => Syn.subst (inst (var 0 : T (n + 1)))
      (up (fun j : Fin n => (var j.succ : T (n + 1))) i)) = var := by
    refine funext (Fin.cases ?_ fun j => ?_) <;> simp
  rw [Fm.subst_subst, e, Fm.subst_id]

end Fm

namespace Prf

variable {Ax : Theory T} {n m : ℕ} {Γ Δ : List (Fm T n)} {φ ψ χ : Fm T n}

/-- Derivability is closed under substitution of terms for free variables and
under weakening of the context, in one induction. -/
theorem substWeaken (h : Γ ⊢[Ax] φ) : ∀ {m : ℕ} (σ : Fin n → T m) {Δ : List (Fm T m)},
    Γ.map (fun ψ => ψ.subst σ) ⊆ Δ → (Δ ⊢[Ax] φ.subst σ) := by
  induction h with intro m σ Δ s
  | hyp h => exact .hyp (s (List.mem_map_of_mem h))
  | ax h ρ => rw [Fm.subst_subst]; exact .ax h _
  | botE φ _ ih => exact .botE _ (ih σ s)
  | andI _ _ ih₁ ih₂ => exact .andI (ih₁ σ s) (ih₂ σ s)
  | andE₁ _ ih => exact .andE₁ (ih σ s)
  | andE₂ _ ih => exact .andE₂ (ih σ s)
  | orI₁ _ ih => exact .orI₁ (ih σ s)
  | orI₂ _ ih => exact .orI₂ (ih σ s)
  | orE _ _ _ ih ih₁ ih₂ =>
    exact .orE (ih σ s) (ih₁ σ (List.cons_subset_cons _ s)) (ih₂ σ (List.cons_subset_cons _ s))
  | impI _ ih => exact .impI (ih σ (List.cons_subset_cons _ s))
  | impE _ _ ih₁ ih₂ => exact .impE (ih₁ σ s) (ih₂ σ s)
  | allI _ ih =>
    exact .allI (ih (up σ) (by rw [Fm.map_shift_subst]; exact List.map_subset _ s))
  | allE t _ ih => rw [Fm.subst_inst]; exact .allE _ (ih σ s)
  | exI t _ ih =>
    have h := ih σ s
    rw [Fm.subst_inst] at h
    exact .exI _ h
  | exE _ _ ih₁ ih₂ =>
    have h := ih₂ (up σ) (Δ := _ :: Δ.map Fm.shift) (by
      rw [List.map_cons, Fm.map_shift_subst]
      exact List.cons_subset_cons _ (List.map_subset _ s))
    rw [Fm.shift_subst_up] at h
    exact .exE (ih₁ σ s) h
  | eqRefl t => exact .eqRefl _
  | eqSubst φ ρ ρ' _ _ ih₁ ih₂ =>
    have h := ih₂ σ s
    rw [Fm.subst_subst] at h ⊢
    exact .eqSubst φ _ _ (fun i => ih₁ i σ s) h

/-- Weakening. -/
theorem weaken (h : Γ ⊢[Ax] φ) {Δ : List (Fm T n)} (s : Γ ⊆ Δ) : Δ ⊢[Ax] φ := by
  simpa using h.substWeaken var (Δ := Δ) (by simpa using s)

/-- Derivability is closed under substitution of terms for free variables. -/
theorem subst (h : Γ ⊢[Ax] φ) {m : ℕ} (σ : Fin n → T m) :
    Γ.map (fun ψ => ψ.subst σ) ⊢[Ax] φ.subst σ :=
  h.substWeaken σ (List.Subset.refl _)

/-- Derivability is closed under weakening by a fresh variable. -/
theorem shift (h : Γ ⊢[Ax] φ) : Γ.map Fm.shift ⊢[Ax] φ.shift :=
  h.subst _

theorem liftCons (s : ∀ ψ ∈ Γ, Δ ⊢[Ax] ψ) (χ : Fm T n) :
    ∀ ψ ∈ χ :: Γ, (χ :: Δ ⊢[Ax] ψ) :=
  List.forall_mem_cons.2 ⟨.hyp List.mem_cons_self, fun ψ hψ => (s ψ hψ).weaken (by simp)⟩

/-- Simultaneous cut: the hypotheses may be replaced by anything deriving them.
Each hypothesis is discharged by an implication and restored by modus ponens. -/
theorem trans (h : Γ ⊢[Ax] φ) {Δ : List (Fm T n)} (s : ∀ ψ ∈ Γ, Δ ⊢[Ax] ψ) : Δ ⊢[Ax] φ := by
  induction Γ generalizing φ with
  | nil => exact h.weaken (List.nil_subset _)
  | cons ψ Γ ih =>
    exact .impE (ih (.impI h) fun χ hχ => s χ (List.mem_cons_of_mem _ hχ))
      (s ψ List.mem_cons_self)

/-! ### Structural conveniences -/

theorem hyp0 : φ :: Γ ⊢[Ax] φ := .hyp List.mem_cons_self

theorem hyp1 : ψ :: φ :: Γ ⊢[Ax] φ := .hyp (List.mem_cons_of_mem _ List.mem_cons_self)

theorem wk (h : Γ ⊢[Ax] φ) : ψ :: Γ ⊢[Ax] φ := h.weaken (List.subset_cons_self _ _)

/-- A closed derivation may be used under any hypotheses. -/
theorem ofNil (h : [] ⊢[Ax] φ) : Γ ⊢[Ax] φ := h.weaken (List.nil_subset _)

theorem impTrans (h₁ : Γ ⊢[Ax] φ ⟶ ψ) (h₂ : Γ ⊢[Ax] ψ ⟶ χ) : Γ ⊢[Ax] φ ⟶ χ :=
  .impI (.impE h₂.wk (.impE h₁.wk hyp0))

/-- An axiom, used as stated. -/
theorem axm (h : Ax n φ) : Γ ⊢[Ax] φ := by
  simpa only [Fm.subst_id] using Prf.ax (Γ := Γ) h var

/-- Universal elimination onto the bound variable itself. -/
theorem allOpen {φ : Fm T (n + 1)} (h : Γ ⊢[Ax] Fm.all φ) : Γ.map Fm.shift ⊢[Ax] φ := by
  have h' := Prf.allE (var 0) h.shift
  rwa [Fm.subst_up_succ_inst] at h'

/-! ### Biimplication -/

theorem iffI (h₁ : Γ ⊢[Ax] φ ⟶ ψ) (h₂ : Γ ⊢[Ax] ψ ⟶ φ) : Γ ⊢[Ax] Fm.iff φ ψ := .andI h₁ h₂

theorem iffMp (h : Γ ⊢[Ax] Fm.iff φ ψ) (h₁ : Γ ⊢[Ax] φ) : Γ ⊢[Ax] ψ := .impE (.andE₁ h) h₁

theorem iffMpr (h : Γ ⊢[Ax] Fm.iff φ ψ) (h₁ : Γ ⊢[Ax] ψ) : Γ ⊢[Ax] φ := .impE (.andE₂ h) h₁

theorem iffRefl (φ : Fm T n) : Γ ⊢[Ax] Fm.iff φ φ := .andI (.impI hyp0) (.impI hyp0)

theorem iffSymm (h : Γ ⊢[Ax] Fm.iff φ ψ) : Γ ⊢[Ax] Fm.iff ψ φ := .andI (.andE₂ h) (.andE₁ h)

theorem iffTrans (h₁ : Γ ⊢[Ax] Fm.iff φ ψ) (h₂ : Γ ⊢[Ax] Fm.iff ψ χ) : Γ ⊢[Ax] Fm.iff φ χ :=
  .andI (impTrans (.andE₁ h₁) (.andE₁ h₂)) (impTrans (.andE₂ h₂) (.andE₂ h₁))

/-! ### Equality -/

/-- Leibniz' rule for one variable. -/
theorem eqSubst1 (φ : Fm T (n + 1)) {s t : T n} (h : Γ ⊢[Ax] s ≐ t)
    (hφ : Γ ⊢[Ax] φ.subst (inst s)) : Γ ⊢[Ax] φ.subst (inst t) :=
  .eqSubst φ (inst s) (inst t) (fun i => Fin.cases h (fun _ => .eqRefl _) i) hφ

theorem eqSymm {s t : T n} (h : Γ ⊢[Ax] s ≐ t) : Γ ⊢[Ax] t ≐ s := by
  simpa using eqSubst1 (Fm.eq (var 0) (Syn.shift s)) h (by simpa using Prf.eqRefl s)

theorem eqTrans {s t u : T n} (h₁ : Γ ⊢[Ax] s ≐ t) (h₂ : Γ ⊢[Ax] t ≐ u) : Γ ⊢[Ax] s ≐ u := by
  simpa using eqSubst1 (Fm.eq (Syn.shift s) (var 0)) h₂ (by simpa using h₁)

/-- Congruence: provably equal substitutions give provably equal instances of a
term. -/
theorem eqCongr {k : ℕ} (t : T k) {σ σ' : Fin k → T n} (h : ∀ i, Γ ⊢[Ax] σ i ≐ σ' i) :
    Γ ⊢[Ax] Syn.subst σ t ≐ Syn.subst σ' t := by
  simpa [Syn.subst_shift] using Prf.eqSubst (Fm.eq (var 0) (Syn.shift t))
    (Fin.cases (Syn.subst σ t) σ) (Fin.cases (Syn.subst σ t) σ')
    (fun i => Fin.cases (.eqRefl _) h i)
    (by simpa [Syn.subst_shift] using Prf.eqRefl (Ax := Ax) (Γ := Γ) (Syn.subst σ t))

/-- Congruence for one variable. -/
theorem eqCongr1 (u : T (n + 1)) {s t : T n} (h : Γ ⊢[Ax] s ≐ t) :
    Γ ⊢[Ax] Syn.subst (inst s) u ≐ Syn.subst (inst t) u :=
  eqCongr u fun i => Fin.cases h (fun _ => .eqRefl _) i

end Prf

end LeanProofs.ConciseIPRA
