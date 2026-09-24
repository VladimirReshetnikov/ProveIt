import Surreal.Algebra.RingFormulaCode
import Surreal.Algebra.RingTermScopeComputability

/-!
# Exact context validation for native ring-formula codes

The formula-scope validation in `odg:def:thm:saturation`. A numerical stack
of context sizes simulates the native parser, including term validity,
matching contexts for implication and positive contexts for quantification.
-/

namespace Surreal.RingFormulaCode
open FirstOrder FirstOrder.Language

local instance (n : ℕ) (l : List RingTermCode.Token) : Decidable (RingTermScope.Valid n l) :=
  inferInstanceAs (Decidable (RingTermCode.height l (some 0) = some 1 ∧
    RingTermScope.checkScope n l = true))

/-- Implication consumes two matching contexts. -/
def impScope (s : List ℕ) : Option (List ℕ) := do
  let n ← s[0]?
  let m ← s[1]?
  if m = n then some (n :: s.drop 2) else none

/-- A universal quantifier consumes one bound variable. -/
def allScope (s : List ℕ) : Option (List ℕ) := do
  let n ← s.head?
  if n = 0 then none else some ((n - 1) :: s.tail)

/-- Numerical simulation of one token's action on scoped formulas. -/
def scopeStep : Token → List ℕ → Option (List ℕ)
  | .inl (n, a, b), s =>
      if RingTermScope.Valid (1 + n) a ∧ RingTermScope.Valid (1 + n) b then some (n :: s) else none
  | .inr (.inl n), s => some (n :: s)
  | .inr (.inr i), s => if i.val = 0 then impScope s else allScope s

/-- Scan context sizes while rejecting syntactically invalid subexpressions. -/
def scopes (l : List Token) (s : Option (List ℕ)) : Option (List ℕ) :=
  l.foldr (fun t r => r.bind (scopeStep t)) s

/-- One successful numerical step is exactly the projection of native parsing. -/
theorem step_scopes (t : Token) (s : List ScopedFormula) :
    (step t s).map (List.map Sigma.fst) = scopeStep t (s.map Sigma.fst) := by
  rcases t with ⟨n, a, b⟩ | (n | i)
  · cases ha : RingTermScope.decode (1 + n) a <;>
      cases hb : RingTermScope.decode (1 + n) b <;>
      simp [step, scopeStep, RingTermScope.valid_iff_decode, ha, hb]
  · rfl
  · fin_cases i
    · cases s with
      | nil => simp [step, scopeStep, impScope]
      | cons φ s =>
        cases s with
        | nil => cases φ; simp [step, scopeStep, impScope]
        | cons ψ s =>
          obtain ⟨n, φ⟩ := φ
          obtain ⟨m, ψ⟩ := ψ
          by_cases h : m = n
          · subst m; simp [step, scopeStep, impScope]
          · simp [step, scopeStep, impScope, h]
    · cases s with
      | nil => simp [step, scopeStep, allScope]
      | cons φ s =>
        obtain ⟨n, φ⟩ := φ
        cases n <;> simp [step, scopeStep, allScope]

/-- Numerical scanning agrees with native parsing for any initial stack. -/
theorem parse_scopes (l : List Token) (s : Option (List ScopedFormula)) :
    (parse l s).map (List.map Sigma.fst) = scopes l (s.map (List.map Sigma.fst)) := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    change ((parse l s).bind (step t)).map (List.map Sigma.fst) =
      (scopes l (s.map (List.map Sigma.fst))).bind (scopeStep t)
    rw [← ih]
    cases parse l s <;> simp [step_scopes]

/-- Extract a context only when the entire stream is precisely one well-scoped formula. -/
def scope (l : List Token) : Option ℕ :=
  match scopes l (some []) with
  | some [n] => some n
  | _ => none

/-- The numerical scope extractor precisely describes the native parser's result. -/
theorem decode_scope (l : List Token) : (decode l).map Sigma.fst = scope l := by
  have h := parse_scopes l (some [])
  simp only [Option.map_some, List.map_nil] at h
  unfold scope
  rw [← h]
  cases hp : parse l (some []) with
  | none => simp [decode, hp]
  | some s => cases s with
    | nil => simp [decode, hp]
    | cons φ s => cases s <;> simp [decode, hp]

/-- Encoding a native formula records exactly its actual bound-variable context. -/
@[simp] theorem scope_encode (φ : ScopedFormula) : scope (encodeScoped φ) = some φ.1 := by
  rw [← decode_scope, decode_encode, Option.map_some]

/-- Valid formula codes are exactly streams with a successfully extracted context. -/
def Valid (l : List Token) : Prop := (scope l).isSome = true

/-- Numerical validity is equivalent to the existence of a native parsed formula. -/
theorem valid_iff_decode (l : List Token) : Valid l ↔ ∃ φ, decode l = some φ := by
  rw [Valid, ← decode_scope]
  cases h : decode l <;> simp

/-- Context validation recognizes exactly the serializer's range. -/
theorem valid_iff_mem_range (l : List Token) : Valid l ↔ l ∈ Set.range encodeScoped := by
  rw [valid_iff_decode]
  constructor
  · rintro ⟨φ, hφ⟩
    exact ⟨φ, encode_of_decode hφ⟩
  · rintro ⟨φ, rfl⟩
    exact ⟨φ, decode_encode φ⟩

/-- Scoped native formulas correspond exactly to numerically validated token streams. -/
def codeEquiv : ScopedFormula ≃ {l : List Token // Valid l} where
  toFun φ := ⟨encodeScoped φ, by simp [Valid]⟩
  invFun l := (decode l.val).getD ⟨0, .falsum⟩
  left_inv φ := by simp
  right_inv l := by
    obtain ⟨φ, hφ⟩ := (valid_iff_decode l.val).mp l.property
    apply Subtype.ext
    change encodeScoped ((decode l.val).getD ⟨0, .falsum⟩) = l.val
    rw [hφ, Option.getD_some]
    exact encode_of_decode hφ

end Surreal.RingFormulaCode
