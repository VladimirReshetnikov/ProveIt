/-! Hurkens' paradox, transcribed into Lean, to locate the exact blocker. -/
universe u v

/-- "Powerset".  `X → Prop : Sort (imax u 1) = Sort (max u 1)`. -/
def Pw (X : Sort u) : Sort (max 1 u) := X → Prop

-- (1) Impredicativity IS present: a quantifier landing in Prop stays in Prop,
--     because `imax u 0 = 0`.  This is exactly what Hurkens relies on.
#check fun (X : Type) (p : Pw X) => (∀ x : X, p x : Prop)
#check fun (X : Type 5) (p : Pw X) => (∀ x : X, p x : Prop)

-- (2) But the powerset of a Prop is a Type, never a Prop.  `imax u 1 = max u 1`.
#check (Pw True : Type)
example : Pw True = (True → Prop) := rfl

-- (3) So Hurkens' `U` cannot be a Prop.  Lean assigns it Type 1.
def U : Type 1 := ∀ X : Prop, ((Pw (Pw X) → X) → Pw (Pw X))
#check @U

-- (4) The paradox requires self-application: `σ s := s U (...)`, instantiating
--     the bound `X : Prop` at `X := U`.  `U : Type 1`, so this is the wall.
def sigma_attempt (s : U) : Pw (Pw U) := s U (fun t => t)
