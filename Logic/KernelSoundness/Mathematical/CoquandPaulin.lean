/-!
# Coquand–Paulin, formalised in Lean

Lean has TWO of Coquand's three ingredients outright:
  * impredicative `Prop` — `∀ x : X, p x : Prop` for `X` in *any* universe, and
  * a universe type      — `Prop : Type`.
Only the third, non-strictly-positive inductive types, is denied, by the kernel's
positivity check. This file proves that guard is *load-bearing*: from merely a
retraction of `Phi A` into `A`, `False` follows.
-/

/-- A positive but NOT strictly positive operator. -/
def Phi (α : Type) : Type := (α → Prop) → Prop

/-- For any `X` there is an injection `X → (X → Prop)`: `x ↦ (· = x)`. -/
def inj {X : Type} : X → (X → Prop) := fun x y => x = y

theorem inj_injective {X : Type} {x x' : X} (h : inj x = inj x') : x = x' :=
  (cast (congrFun h x) rfl).symm

/-- Composite injection from the powerset of `A` into `A`. -/
def fOf {A : Type} (introA : Phi A → A) (p : A → Prop) : A := introA (inj p)

/-- Russell's set: `x` codes a set that does not contain `x`. -/
def P0Of {A : Type} (introA : Phi A → A) (x : A) : Prop :=
  ∃ P : A → Prop, fOf introA P = x ∧ ¬ P x

theorem coquand_paulin
    (A : Type) (introA : Phi A → A) (matchA : A → Phi A)
    (beta : ∀ x, matchA (introA x) = x) : False := by
  have introA_inj : ∀ p p' : Phi A, introA p = introA p' → p = p' := by
    intro p p' h
    have h1 := congrArg matchA h
    rw [beta, beta] at h1
    exact h1
  have f_inj : ∀ p p' : A → Prop, fOf introA p = fOf introA p' → p = p' := by
    intro p p' h
    exact inj_injective (introA_inj _ _ h)
  have bad : P0Of introA (fOf introA (P0Of introA))
           ↔ ¬ P0Of introA (fOf introA (P0Of introA)) := by
    constructor
    · intro hx hP0
      obtain ⟨P, hEq, hNot⟩ := hx
      exact hNot (cast (congrFun (f_inj P (P0Of introA) hEq) _).symm hP0)
    · intro h
      exact ⟨P0Of introA, rfl, h⟩
  exact (fun hp => bad.mp hp hp) (bad.mpr (fun hp => bad.mp hp hp))

#print axioms coquand_paulin

/-! ## The guard is exactly what denies the hypothesis

Uncommenting the following makes the kernel — not the elaborator — refuse:

```
inductive Bad where | mk : Phi Bad → Bad
-- (kernel) arg #1 of 'Bad.mk' has a non positive occurrence of the datatypes
--         being declared
```

`Bad` would supply `introA := Bad.mk` and `matchA`/`beta` from its recursor, so
`coquand_paulin` would then give `False` outright. -/

/-- Cantor, the same phenomenon stated without the operator: there is no retraction
of the powerset of `A` onto `A`. -/
theorem no_powerset_retract (A : Type) (g : (A → Prop) → A) (g' : A → (A → Prop))
    (hg : ∀ p, g' (g p) = p) : False := by
  have g_inj : ∀ p p', g p = g p' → p = p' := by
    intro p p' h
    have h1 := congrArg g' h
    rw [hg, hg] at h1
    exact h1
  let D : A → Prop := fun x => ∃ P, g P = x ∧ ¬ P x
  have bad : D (g D) ↔ ¬ D (g D) := by
    constructor
    · intro hx hD
      obtain ⟨P, hEq, hNot⟩ := hx
      exact hNot (cast (congrFun (g_inj P D hEq) _).symm hD)
    · intro h; exact ⟨D, rfl, h⟩
  exact (fun hp => bad.mp hp hp) (bad.mpr (fun hp => bad.mp hp hp))

#print axioms no_powerset_retract
