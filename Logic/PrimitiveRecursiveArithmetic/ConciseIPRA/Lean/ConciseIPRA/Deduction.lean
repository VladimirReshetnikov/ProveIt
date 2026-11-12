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
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [Fm.subst_subst, e, Fm.subst_id]

end Fm

namespace Prf

variable {Ax : Theory T} {n m : ℕ} {Γ Δ : List (Fm T n)} {φ ψ χ : Fm T n}

/-- Weakening. -/
theorem weaken (h : Γ ⊢[Ax] φ) : ∀ {Δ : List (Fm T n)}, Γ ⊆ Δ → (Δ ⊢[Ax] φ) := by
  induction h with
  | hyp h => intro Δ s; exact .hyp (s h)
  | ax h σ => intro Δ s; exact .ax h σ
  | botE φ _ ih => intro Δ s; exact .botE φ (ih s)
  | andI _ _ ih₁ ih₂ => intro Δ s; exact .andI (ih₁ s) (ih₂ s)
  | andE₁ _ ih => intro Δ s; exact .andE₁ (ih s)
  | andE₂ _ ih => intro Δ s; exact .andE₂ (ih s)
  | orI₁ _ ih => intro Δ s; exact .orI₁ (ih s)
  | orI₂ _ ih => intro Δ s; exact .orI₂ (ih s)
  | orE _ _ _ ih ih₁ ih₂ =>
    intro Δ s
    exact .orE (ih s) (ih₁ (List.cons_subset_cons _ s)) (ih₂ (List.cons_subset_cons _ s))
  | impI _ ih => intro Δ s; exact .impI (ih (List.cons_subset_cons _ s))
  | impE _ _ ih₁ ih₂ => intro Δ s; exact .impE (ih₁ s) (ih₂ s)
  | allI _ ih => intro Δ s; exact .allI (ih (List.map_subset _ s))
  | allE t _ ih => intro Δ s; exact .allE t (ih s)
  | exI t _ ih => intro Δ s; exact .exI t (ih s)
  | exE _ _ ih₁ ih₂ =>
    intro Δ s
    exact .exE (ih₁ s) (ih₂ (List.cons_subset_cons _ (List.map_subset _ s)))
  | eqRefl t => intro Δ s; exact .eqRefl t
  | eqSubst φ σ σ' _ _ ih₁ ih₂ =>
    intro Δ s
    exact .eqSubst φ σ σ' (fun i => ih₁ i s) (ih₂ s)

/-- Derivability is closed under substitution of terms for free variables. -/
theorem subst (h : Γ ⊢[Ax] φ) :
    ∀ {m : ℕ} (σ : Fin n → T m), (Γ.map (fun ψ => ψ.subst σ) ⊢[Ax] φ.subst σ) := by
  induction h with
  | hyp h => intro m σ; exact .hyp (List.mem_map_of_mem h)
  | ax h ρ => intro m σ; rw [Fm.subst_subst]; exact .ax h _
  | botE φ _ ih => intro m σ; exact .botE _ (ih σ)
  | andI _ _ ih₁ ih₂ => intro m σ; exact .andI (ih₁ σ) (ih₂ σ)
  | andE₁ _ ih => intro m σ; exact .andE₁ (ih σ)
  | andE₂ _ ih => intro m σ; exact .andE₂ (ih σ)
  | orI₁ _ ih => intro m σ; exact .orI₁ (ih σ)
  | orI₂ _ ih => intro m σ; exact .orI₂ (ih σ)
  | orE _ _ _ ih ih₁ ih₂ => intro m σ; exact .orE (ih σ) (ih₁ σ) (ih₂ σ)
  | impI _ ih => intro m σ; exact .impI (ih σ)
  | impE _ _ ih₁ ih₂ => intro m σ; exact .impE (ih₁ σ) (ih₂ σ)
  | allI _ ih =>
    intro m σ
    have h := ih (up σ)
    rw [Fm.map_shift_subst] at h
    exact .allI h
  | allE t _ ih =>
    intro m σ
    rw [Fm.subst_inst]
    exact .allE _ (ih σ)
  | exI t _ ih =>
    intro m σ
    have h := ih σ
    rw [Fm.subst_inst] at h
    exact .exI _ h
  | exE _ _ ih₁ ih₂ =>
    intro m σ
    have h := ih₂ (up σ)
    rw [List.map_cons, Fm.map_shift_subst, Fm.shift_subst_up] at h
    exact .exE (ih₁ σ) h
  | eqRefl t => intro m σ; exact .eqRefl _
  | eqSubst φ ρ ρ' _ _ ih₁ ih₂ =>
    intro m σ
    have h := ih₂ σ
    rw [Fm.subst_subst] at h ⊢
    exact .eqSubst φ _ _ (fun i => ih₁ i σ) h

/-- Derivability is closed under weakening by a fresh variable. -/
theorem shift (h : Γ ⊢[Ax] φ) : Γ.map Fm.shift ⊢[Ax] φ.shift :=
  h.subst _

theorem liftCons (s : ∀ ψ ∈ Γ, Δ ⊢[Ax] ψ) (χ : Fm T n) :
    ∀ ψ ∈ χ :: Γ, (χ :: Δ ⊢[Ax] ψ) := by
  intro ψ hψ
  rcases List.mem_cons.mp hψ with rfl | hψ
  · exact .hyp List.mem_cons_self
  · exact (s ψ hψ).weaken (List.subset_cons_self _ _)

theorem liftShift (s : ∀ ψ ∈ Γ, Δ ⊢[Ax] ψ) :
    ∀ ψ ∈ Γ.map Fm.shift, (Δ.map Fm.shift ⊢[Ax] ψ) := by
  intro ψ hψ
  obtain ⟨χ, hχ, rfl⟩ := List.mem_map.mp hψ
  exact (s χ hχ).shift

/-- Simultaneous cut: the hypotheses may be replaced by anything deriving them. -/
theorem trans (h : Γ ⊢[Ax] φ) :
    ∀ {Δ : List (Fm T n)}, (∀ ψ ∈ Γ, Δ ⊢[Ax] ψ) → (Δ ⊢[Ax] φ) := by
  induction h with
  | hyp h => intro Δ s; exact s _ h
  | ax h σ => intro Δ s; exact .ax h σ
  | botE φ _ ih => intro Δ s; exact .botE φ (ih s)
  | andI _ _ ih₁ ih₂ => intro Δ s; exact .andI (ih₁ s) (ih₂ s)
  | andE₁ _ ih => intro Δ s; exact .andE₁ (ih s)
  | andE₂ _ ih => intro Δ s; exact .andE₂ (ih s)
  | orI₁ _ ih => intro Δ s; exact .orI₁ (ih s)
  | orI₂ _ ih => intro Δ s; exact .orI₂ (ih s)
  | orE _ _ _ ih ih₁ ih₂ =>
    intro Δ s
    exact .orE (ih s) (ih₁ (liftCons s _)) (ih₂ (liftCons s _))
  | impI _ ih => intro Δ s; exact .impI (ih (liftCons s _))
  | impE _ _ ih₁ ih₂ => intro Δ s; exact .impE (ih₁ s) (ih₂ s)
  | allI _ ih => intro Δ s; exact .allI (ih (liftShift s))
  | allE t _ ih => intro Δ s; exact .allE t (ih s)
  | exI t _ ih => intro Δ s; exact .exI t (ih s)
  | exE _ _ ih₁ ih₂ =>
    intro Δ s
    exact .exE (ih₁ s) (ih₂ (liftCons (liftShift s) _))
  | eqRefl t => intro Δ s; exact .eqRefl t
  | eqSubst φ σ σ' _ _ ih₁ ih₂ =>
    intro Δ s
    exact .eqSubst φ σ σ' (fun i => ih₁ i s) (ih₂ s)

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
  have := Prf.ax (Γ := Γ) h var
  rwa [Fm.subst_id] at this

/-- Universal elimination onto the bound variable itself. -/
theorem allOpen {φ : Fm T (n + 1)} (h : Γ ⊢[Ax] Fm.all φ) : Γ.map Fm.shift ⊢[Ax] φ := by
  have h' : Γ.map Fm.shift ⊢[Ax] Fm.all (φ.subst (up (fun i => var i.succ))) := h.shift
  have := Prf.allE (var 0) h'
  rwa [Fm.subst_up_succ_inst] at this

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
    (hφ : Γ ⊢[Ax] φ.subst (inst s)) : Γ ⊢[Ax] φ.subst (inst t) := by
  refine .eqSubst φ (inst s) (inst t) (fun i => ?_) hφ
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using h
  · simpa using Prf.eqRefl (Ax := Ax) (Γ := Γ) (var j)

theorem eqSymm {s t : T n} (h : Γ ⊢[Ax] s ≐ t) : Γ ⊢[Ax] t ≐ s := by
  have := eqSubst1 (Fm.eq (var 0) (Syn.shift s)) h (by simpa using Prf.eqRefl s)
  simpa using this

theorem eqTrans {s t u : T n} (h₁ : Γ ⊢[Ax] s ≐ t) (h₂ : Γ ⊢[Ax] t ≐ u) : Γ ⊢[Ax] s ≐ u := by
  have := eqSubst1 (Fm.eq (Syn.shift s) (var 0)) h₂ (by simpa using h₁)
  simpa using this

/-- Congruence: provably equal substitutions give provably equal instances of a
term. -/
theorem eqCongr {k : ℕ} (t : T k) {σ σ' : Fin k → T n} (h : ∀ i, Γ ⊢[Ax] σ i ≐ σ' i) :
    Γ ⊢[Ax] Syn.subst σ t ≐ Syn.subst σ' t := by
  have key := Prf.eqSubst (Ax := Ax) (Γ := Γ)
    (Fm.eq (Syn.subst (fun i => var (Fin.castAdd k i)) t)
      (Syn.subst (fun i => var (Fin.natAdd k i)) t))
    (Fin.append σ σ) (Fin.append σ σ')
    (fun i => by
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left, Fin.append_left]; exact .eqRefl _
      · rw [Fin.append_right, Fin.append_right]; exact h j)
    (by
      rw [Fm.subst_eq, Syn.subst_subst, Syn.subst_subst]
      simp only [Syn.subst_var, Fin.append_left, Fin.append_right]
      exact .eqRefl _)
  rw [Fm.subst_eq, Syn.subst_subst, Syn.subst_subst] at key
  simp only [Syn.subst_var, Fin.append_left, Fin.append_right] at key
  exact key

/-- Congruence for one variable. -/
theorem eqCongr1 (u : T (n + 1)) {s t : T n} (h : Γ ⊢[Ax] s ≐ t) :
    Γ ⊢[Ax] Syn.subst (inst s) u ≐ Syn.subst (inst t) u := by
  refine eqCongr u (fun i => ?_)
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using h
  · simpa using Prf.eqRefl (Ax := Ax) (Γ := Γ) (var j)

end Prf

end LeanProofs.ConciseIPRA
