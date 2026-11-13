import ConciseIPRA.Deduction

/-!
# Term interpretations between theories

An interpretation of a theory `Ax` over a syntax `T` in a theory `Ax'` over a
syntax `T'` is here a translation of terms `f : T n → T' n` that

* fixes variables,
* commutes with substitution up to equality provable in `Ax'`, and
* sends every axiom of `Ax` to a theorem of `Ax'`.

Formulas are translated by translating the terms of their equations; the
domain is not relativized and equality is interpreted by equality.  Such a
translation preserves derivability (`Interp.sound`).

Substitution is respected only up to provable equality because the
translations of interest do not commute with it syntactically: translating an
iterator term into a primitive recursive function symbol turns the step term
into part of the symbol.

Two interpretations in opposite directions whose composites are provably the
identity on terms form a `BiInterp`.  Then each theory proves exactly the
formulas whose translations the other proves, and every formula is provably
equivalent to its round trip (`BiInterp.iff`, `BiInterp.roundTrip`): the two
theories are synonymous, which is the strongest form of bi-interpretability.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm

variable {T T' : ℕ → Type} [Syn T] [Syn T']

/-! ### Congruence rules for biimplication -/

namespace Prf

variable {Ax : Theory T} {n : ℕ} {Γ : List (Fm T n)} {φ ψ φ' ψ' : Fm T n}

theorem iffAnd (h₁ : Γ ⊢[Ax] Fm.iff φ φ') (h₂ : Γ ⊢[Ax] Fm.iff ψ ψ') :
    Γ ⊢[Ax] Fm.iff (φ ⋏ ψ) (φ' ⋏ ψ') :=
  iffI (.impI (.andI (iffMp h₁.wk (.andE₁ hyp0)) (iffMp h₂.wk (.andE₂ hyp0))))
    (.impI (.andI (iffMpr h₁.wk (.andE₁ hyp0)) (iffMpr h₂.wk (.andE₂ hyp0))))

theorem iffOr (h₁ : Γ ⊢[Ax] Fm.iff φ φ') (h₂ : Γ ⊢[Ax] Fm.iff ψ ψ') :
    Γ ⊢[Ax] Fm.iff (φ ⋎ ψ) (φ' ⋎ ψ') :=
  iffI
    (.impI (.orE hyp0 (.orI₁ (iffMp h₁.wk.wk hyp0)) (.orI₂ (iffMp h₂.wk.wk hyp0))))
    (.impI (.orE hyp0 (.orI₁ (iffMpr h₁.wk.wk hyp0)) (.orI₂ (iffMpr h₂.wk.wk hyp0))))

theorem iffImp (h₁ : Γ ⊢[Ax] Fm.iff φ φ') (h₂ : Γ ⊢[Ax] Fm.iff ψ ψ') :
    Γ ⊢[Ax] Fm.iff (φ ⟶ ψ) (φ' ⟶ ψ') :=
  iffI
    (.impI (.impI (iffMp h₂.wk.wk (.impE hyp1 (iffMpr h₁.wk.wk hyp0)))))
    (.impI (.impI (iffMpr h₂.wk.wk (.impE hyp1 (iffMp h₁.wk.wk hyp0)))))

theorem iffAll {φ φ' : Fm T (n + 1)} (h : Γ.map Fm.shift ⊢[Ax] Fm.iff φ φ') :
    Γ ⊢[Ax] Fm.iff (Fm.all φ) (Fm.all φ') :=
  iffI (.impI (.allI (iffMp h.wk (allOpen hyp0)))) (.impI (.allI (iffMpr h.wk (allOpen hyp0))))

/-- Existential introduction at the bound variable itself. -/
theorem exOpen {φ : Fm T (n + 1)} {Δ : List (Fm T (n + 1))} (h : Δ ⊢[Ax] φ) :
    Δ ⊢[Ax] (Fm.ex φ).shift :=
  .exI (var 0) (by rwa [Fm.subst_up_succ_inst])

theorem iffEx {φ φ' : Fm T (n + 1)} (h : Γ.map Fm.shift ⊢[Ax] Fm.iff φ φ') :
    Γ ⊢[Ax] Fm.iff (Fm.ex φ) (Fm.ex φ') :=
  iffI (.impI (.exE hyp0 (exOpen (iffMp h.wk.wk hyp0))))
    (.impI (.exE hyp0 (exOpen (iffMpr h.wk.wk hyp0))))

theorem eqIff {s s' t t' : T n} (h₁ : Γ ⊢[Ax] s ≐ s') (h₂ : Γ ⊢[Ax] t ≐ t') :
    Γ ⊢[Ax] Fm.iff (s ≐ t) (s' ≐ t') :=
  iffI (.impI (eqTrans (eqSymm h₁.wk) (eqTrans hyp0 h₂.wk)))
    (.impI (eqTrans h₁.wk (eqTrans hyp0 (eqSymm h₂.wk))))

/-- Provably equal substitutions give equivalent instances of a formula. -/
theorem iffSubst {k : ℕ} (φ : Fm T k) {σ σ' : Fin k → T n} (h : ∀ i, Γ ⊢[Ax] σ i ≐ σ' i) :
    Γ ⊢[Ax] Fm.iff (φ.subst σ) (φ.subst σ') :=
  iffI (.impI (.eqSubst φ σ σ' (fun i => (h i).wk) hyp0))
    (.impI (.eqSubst φ σ' σ (fun i => (eqSymm (h i)).wk) hyp0))

end Prf

/-! ### Translation of formulas -/

namespace Fm

variable {n : ℕ}

section Map

omit [Syn T] [Syn T']

/-- Translate the terms of a formula. -/
def map (f : ∀ n, T n → T' n) : {n : ℕ} → Fm T n → Fm T' n
  | _, eq s t => eq (f _ s) (f _ t)
  | _, bot => bot
  | _, and φ ψ => and (map f φ) (map f ψ)
  | _, or φ ψ => or (map f φ) (map f ψ)
  | _, imp φ ψ => imp (map f φ) (map f ψ)
  | _, all φ => all (map f φ)
  | _, ex φ => ex (map f φ)

variable (f : ∀ n, T n → T' n)

theorem map_QF {φ : Fm T n} (h : φ.QF) : (φ.map f).QF := by
  induction φ <;> simp_all [Fm.QF, Fm.map]

end Map

omit [Syn T'] in
/-- If a round trip is provably the identity on terms, every formula is
provably equivalent to its round trip. -/
theorem iff_map_map {Ax : Theory T} (f : ∀ n, T n → T' n) (g : ∀ n, T' n → T n)
    (h : ∀ {n : ℕ} (t : T n), [] ⊢[Ax] t ≐ g n (f n t)) (φ : Fm T n) :
    ∀ Γ : List (Fm T n), Γ ⊢[Ax] Fm.iff φ ((φ.map f).map g) := by
  induction φ with intro Γ
  | eq s t => exact Prf.eqIff (h s).ofNil (h t).ofNil
  | bot => exact Prf.iffRefl _
  | and φ ψ ih₁ ih₂ => exact Prf.iffAnd (ih₁ Γ) (ih₂ Γ)
  | or φ ψ ih₁ ih₂ => exact Prf.iffOr (ih₁ Γ) (ih₂ Γ)
  | imp φ ψ ih₁ ih₂ => exact Prf.iffImp (ih₁ Γ) (ih₂ Γ)
  | all φ ih => exact Prf.iffAll (ih _)
  | ex φ ih => exact Prf.iffEx (ih _)

end Fm

/-! ### Interpretations -/

/-- A translation of terms that fixes variables and commutes with substitution
up to equality provable in `Ax'`. -/
structure TmMorph (T : ℕ → Type) [Syn T] (Ax' : Theory T') where
  /-- The translation of terms. -/
  f : ∀ n, T n → T' n
  f_var : ∀ {n : ℕ} (i : Fin n), f n (var i) = var i
  f_subst : ∀ {n m : ℕ} (ρ : Fin n → T m) (t : T n),
    [] ⊢[Ax'] f m (Syn.subst ρ t) ≐ Syn.subst (fun i => f m (ρ i)) (f n t)

namespace TmMorph

variable {Ax' : Theory T'} (F : TmMorph T Ax') {n m : ℕ}

theorem f_inst (t : T n) : (fun i => F.f n (inst t i)) = inst (F.f n t) := by
  refine funext (Fin.cases ?_ fun j => ?_) <;> simp [F.f_var]

theorem f_repl (s : T (n + 1)) :
    (fun i => F.f (n + 1) (repl s i)) = repl (F.f (n + 1) s) := by
  refine funext (Fin.cases ?_ fun j => ?_) <;> simp [F.f_var]

theorem f_up (ρ : Fin n → T m) (Γ : List (Fm T' (m + 1))) (i : Fin (n + 1)) :
    Γ ⊢[Ax'] F.f (m + 1) (up ρ i) ≐ up (fun i => F.f m (ρ i)) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [up_zero, F.f_var, up_zero]; exact .eqRefl _
  · rw [up_succ, up_succ]
    simpa only [F.f_var, Syn.shift] using (F.f_subst (fun i => var i.succ) (ρ j)).ofNil (Γ := Γ)

/-- The translation of formulas commutes with substitution up to provable
equivalence. -/
theorem map_subst (φ : Fm T n) :
    ∀ {m : ℕ} (ρ : Fin n → T m) (Γ : List (Fm T' m)),
      Γ ⊢[Ax'] Fm.iff ((φ.subst ρ).map F.f) ((φ.map F.f).subst (fun i => F.f m (ρ i))) := by
  induction φ with intro m ρ Γ
  | eq s t => exact Prf.eqIff (F.f_subst ρ s).ofNil (F.f_subst ρ t).ofNil
  | bot => exact Prf.iffRefl _
  | and φ ψ ih₁ ih₂ => exact Prf.iffAnd (ih₁ ρ Γ) (ih₂ ρ Γ)
  | or φ ψ ih₁ ih₂ => exact Prf.iffOr (ih₁ ρ Γ) (ih₂ ρ Γ)
  | imp φ ψ ih₁ ih₂ => exact Prf.iffImp (ih₁ ρ Γ) (ih₂ ρ Γ)
  | all φ ih =>
    exact Prf.iffAll (Prf.iffTrans (ih (up ρ) _) (Prf.iffSubst _ (fun i => F.f_up ρ _ i)))
  | ex φ ih =>
    exact Prf.iffEx (Prf.iffTrans (ih (up ρ) _) (Prf.iffSubst _ (fun i => F.f_up ρ _ i)))

theorem map_inst (φ : Fm T (n + 1)) (t : T n) (Γ : List (Fm T' n)) :
    Γ ⊢[Ax'] Fm.iff ((φ.subst (inst t)).map F.f) ((φ.map F.f).subst (inst (F.f n t))) := by
  have h := F.map_subst φ (inst t) Γ
  rwa [F.f_inst] at h

theorem map_shift (φ : Fm T n) (Γ : List (Fm T' (n + 1))) :
    Γ ⊢[Ax'] Fm.iff (φ.shift.map F.f) (φ.map F.f).shift := by
  have h := F.map_subst φ (fun i => var i.succ) Γ
  simp only [F.f_var] at h
  exact h

theorem shiftCtx (Γ : List (Fm T n)) :
    ∀ χ ∈ (Γ.map Fm.shift).map (Fm.map F.f),
      ((Γ.map (Fm.map F.f)).map Fm.shift ⊢[Ax'] χ) :=
  List.forall_mem_map.2 <| List.forall_mem_map.2 fun ψ hψ =>
    Prf.iffMpr (F.map_shift ψ _) (.hyp (List.mem_map_of_mem (List.mem_map_of_mem hψ)))

theorem map_repl (φ : Fm T (n + 1)) (s : T (n + 1)) (Γ : List (Fm T' (n + 1))) :
    Γ ⊢[Ax'] Fm.iff ((φ.subst (repl s)).map F.f)
      ((φ.map F.f).subst (repl (F.f (n + 1) s))) := by
  have h := F.map_subst φ (repl s) Γ
  rwa [F.f_repl] at h

/-- The translation of an instance of the induction scheme is equivalent to
the instance for the translated formula. -/
theorem map_ind (φ : Fm T (n + 1)) (z : T n) (s : T (n + 1)) (Γ : List (Fm T' n)) :
    Γ ⊢[Ax'] Fm.iff
      ((φ.subst (inst z) ⟶ Fm.all (φ ⟶ φ.subst (repl s)) ⟶ Fm.all φ).map F.f)
      ((φ.map F.f).subst (inst (F.f n z)) ⟶
        Fm.all (φ.map F.f ⟶ (φ.map F.f).subst (repl (F.f (n + 1) s))) ⟶
          Fm.all (φ.map F.f)) :=
  Prf.iffImp (F.map_inst φ z Γ)
    (Prf.iffImp (Prf.iffAll (Prf.iffImp (Prf.iffRefl _) (F.map_repl φ s _))) (Prf.iffRefl _))

end TmMorph

/-- A term interpretation of the theory `Ax` in the theory `Ax'`: a term
translation sending every axiom of `Ax` to a theorem of `Ax'`. -/
structure Interp (Ax : Theory T) (Ax' : Theory T') extends TmMorph T Ax' where
  f_ax : ∀ {k : ℕ} {φ : Fm T k}, Ax k φ → ([] ⊢[Ax'] φ.map f)

namespace Interp

variable {Ax : Theory T} {Ax' : Theory T'} (F : Interp Ax Ax') {n m : ℕ}

/-- An interpretation preserves derivability. -/
theorem sound {Γ : List (Fm T n)} {φ : Fm T n} (h : Γ ⊢[Ax] φ) :
    Γ.map (Fm.map F.f) ⊢[Ax'] φ.map F.f := by
  induction h with
  | hyp h => exact .hyp (List.mem_map_of_mem h)
  | ax h σ =>
    exact Prf.iffMpr (F.map_subst _ σ _) (((F.f_ax h).subst (fun i => F.f _ (σ i))).ofNil)
  | botE φ _ ih => exact .botE _ ih
  | andI _ _ ih₁ ih₂ => exact .andI ih₁ ih₂
  | andE₁ _ ih => exact .andE₁ ih
  | andE₂ _ ih => exact .andE₂ ih
  | orI₁ _ ih => exact .orI₁ ih
  | orI₂ _ ih => exact .orI₂ ih
  | orE _ _ _ ih ih₁ ih₂ => exact .orE ih ih₁ ih₂
  | impI _ ih => exact .impI ih
  | impE _ _ ih₁ ih₂ => exact .impE ih₁ ih₂
  | allI _ ih => exact .allI (ih.trans (F.shiftCtx _))
  | allE t _ ih => exact Prf.iffMpr (F.map_inst _ t _) (.allE _ ih)
  | exI t _ ih => exact .exI _ (Prf.iffMp (F.map_inst _ t _) ih)
  | exE _ _ ih₁ ih₂ =>
    rw [List.map_cons] at ih₂
    exact .exE ih₁ (Prf.iffMp (F.map_shift _ _) (ih₂.trans (Prf.liftCons (F.shiftCtx _) _)))
  | eqRefl t => exact .eqRefl _
  | eqSubst φ σ σ' _ _ ih₁ ih₂ =>
    exact Prf.iffMpr (F.map_subst φ σ' _)
      (.eqSubst _ _ _ ih₁ (Prf.iffMp (F.map_subst φ σ _) ih₂))

end Interp

/-- A pair of term interpretations whose composites are provably the identity:
a synonymy of the two theories. -/
structure BiInterp (Ax : Theory T) (Ax' : Theory T') where
  /-- The interpretation of `Ax` in `Ax'`. -/
  F : Interp Ax Ax'
  /-- The interpretation of `Ax'` in `Ax`. -/
  G : Interp Ax' Ax
  gf : ∀ {n : ℕ} (t : T n), [] ⊢[Ax] t ≐ G.f n (F.f n t)
  fg : ∀ {n : ℕ} (t : T' n), [] ⊢[Ax'] t ≐ F.f n (G.f n t)

namespace BiInterp

variable {Ax : Theory T} {Ax' : Theory T'} (B : BiInterp Ax Ax') {n : ℕ}

/-- Every formula is provably equivalent to its round trip. -/
theorem roundTrip (φ : Fm T n) (Γ : List (Fm T n)) :
    Γ ⊢[Ax] Fm.iff φ ((φ.map B.F.f).map B.G.f) :=
  Fm.iff_map_map B.F.f B.G.f B.gf φ Γ

/-- The symmetric bi-interpretation. -/
def symm : BiInterp Ax' Ax where
  F := B.G
  G := B.F
  gf := B.fg
  fg := B.gf

/-- A bi-interpretation is faithful in both directions: a sequent is derivable
exactly when its translation is. -/
theorem iff {Γ : List (Fm T n)} {φ : Fm T n} :
    (Γ ⊢[Ax] φ) ↔ (Γ.map (Fm.map B.F.f) ⊢[Ax'] φ.map B.F.f) :=
  ⟨B.F.sound, fun h => Prf.iffMpr (B.roundTrip φ Γ) ((B.G.sound h).trans <|
    List.forall_mem_map.2 <| List.forall_mem_map.2 fun ψ hψ =>
      Prf.iffMp (B.roundTrip ψ Γ) (.hyp hψ))⟩

end BiInterp

end LeanProofs.ConciseIPRA
