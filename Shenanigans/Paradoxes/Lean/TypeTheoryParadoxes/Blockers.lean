/-!
# Where each paradox stops, machine-checked

`Girard.lean` and `CoquandPaulin.lean` derive `False` from hypotheses. This file
does the complementary half: it exhibits the exact judgment Lean refuses in each
case, with the refusal captured by `#guard_msgs` so that a future toolchain
change cannot silently invalidate the claim.

Nothing here proves anything. Every declaration either type-checks trivially or
is expected to fail with a recorded message.
-/

namespace TypeTheoryParadoxes.Blockers

universe u

/-! ## 1. Impredicativity is present, and is as strong as System U in one direction

`(A → B) : Sort (imax u v)`, and `imax u 0 = 0`, so a quantifier landing in
`Prop` *stays* in `Prop` no matter how large the domain. This is exactly the
ingredient Hurkens relies on, and Lean has it outright. -/

/-- Powerset. `X → Prop : Sort (imax u 1) = Sort (max u 1)`. -/
def Pw (X : Sort u) : Sort (max 1 u) := X → Prop

example (X : Type) (p : Pw X) : Prop := ∀ x : X, p x
example (X : Type 5) (p : Pw X) : Prop := ∀ x : X, p x

/-! ## 2. But `Prop` is not closed under powerset

`imax u 1 = max u 1`, which is never `0`. The *type of predicates* on a `Prop`
is a `Type`. This is the arithmetic that denies Hurkens his universe. -/

example : Pw True = (True → Prop) := rfl
example : Type := Pw True

/-! ## 3. So Hurkens' `U` is not a `Prop`, and the self-application does not type

Hurkens' universe is `U := ∀ X : Prop, ((℘℘X → X) → ℘℘X)`. Lean places it in
`Type`, one level too high, because the bound `X` ranges over `Prop : Type`. -/

def U : Type := ∀ X : Prop, ((Pw (Pw X) → X) → Pw (Pw X))

/-! The paradox needs `σ s := s U (…)`, which instantiates the bound `X : Prop`
at `X := U`. Since `U : Type`, `s` is not applicable to it — and this is the
whole story of why Hurkens does not run in Lean. -/

/--
error: Application type mismatch: The argument
  U
has type
  Type
of sort `Type 1` but is expected to have type
  Prop
of sort `Type` in the application
  s U
-/
#guard_msgs in
example (s : U) : Pw (Pw U) := s U (fun t => t)

/-! ## 4. The same collapse in Girard's original form: the product bumps a level

`Girard.girard` hypothesises that `Type u` contains a code for every product of
a `Type u`-indexed family. Lean computes that product's level as
`imax (u+2) (u+1) = u+2`, i.e. `Type (u+1)` — never `Type u`. -/

def F (X : Type u) : Type u := (((X → Prop) → Prop) → X) → ((X → Prop) → Prop)

/-- info: (X : Type u) → F X : Type (u + 1) -/
#guard_msgs in #check ((X : Type u) → F X)

/--
error: Type mismatch
  (X : Type u) → F X
has type
  Type (u + 1)
of sort `Type (u + 2)` but is expected to have type
  Type u
of sort `Type (u + 1)`
-/
#guard_msgs in
example : Type u := (X : Type u) → F X

/-! ## 5. The positivity guard is a *kernel* check, not an elaborator check

`CoquandPaulin.coquand_paulin` needs a retraction of `Phi α = (α → Prop) → Prop`
into `α`. A non-strictly-positive inductive would supply one. The refusal comes
from the kernel — note the `(kernel)` prefix — so no elaborator setting reaches
it, and there is no Lean counterpart of Rocq's `Unset Positivity Checking`. -/

/--
error: (kernel) arg #1 of 'TypeTheoryParadoxes.Blockers.Bad.mk' has a non positive occurrence of the datatypes being declared
-/
#guard_msgs in
inductive Bad where | mk : ((Bad → Prop) → Prop) → Bad

/-! The bare negative occurrence — Curry's paradox, the shape that Rocq accepts
under `Unset Positivity Checking` (see
`Shenanigans/EscapeHatches/Coq/TypingFlags.v` section 2) — is refused by the same
check. -/

/--
error: (kernel) arg #1 of 'TypeTheoryParadoxes.Blockers.Curry.mk' has a non positive occurrence of the datatypes being declared
-/
#guard_msgs in
inductive Curry where | mk : (Curry → False) → Curry

end TypeTheoryParadoxes.Blockers
