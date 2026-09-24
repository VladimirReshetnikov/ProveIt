import Mathlib.ModelTheory.Algebra.Ring.Basic
import Mathlib.Computability.Primrec.List
import Mathlib.Tactic.FinCases

/-!
# Prefix codes for native ring terms

A coding prerequisite for `odg:def:thm:saturation`. Tokens distinguish
natural-number variables and the five ring function symbols. Prefix parsing
uses a stack and rejects underflow; validity has a primitive-recursive
numerical stack implementation.
-/

namespace Surreal.RingTermCode
open FirstOrder FirstOrder.Language

/-- A variable index or one of zero, one, negation, addition and multiplication. -/
abbrev Token := ℕ ⊕ Fin 5

/-- The number of arguments consumed by a token. -/
def arity : Token → ℕ
  | .inl _ => 0
  | .inr i => if i.val < 2 then 0 else if i.val = 2 then 1 else 2

/-- Prefix serialization of a native ring term with natural-number variable indices. -/
def encode : Language.ring.Term ℕ → List Token
  | .var n => [.inl n]
  | .func .zero _ => [.inr 0]
  | .func .one _ => [.inr 1]
  | .func .neg ts => .inr 2 :: encode (ts 0)
  | .func .add ts => .inr 3 :: (encode (ts 0) ++ encode (ts 1))
  | .func .mul ts => .inr 4 :: (encode (ts 0) ++ encode (ts 1))

@[simp] theorem encode_zero : encode (0 : Language.ring.Term ℕ) = [.inr 0] := rfl
@[simp] theorem encode_one : encode (1 : Language.ring.Term ℕ) = [.inr 1] := rfl
@[simp] theorem encode_neg (t : Language.ring.Term ℕ) : encode (-t) = .inr 2 :: encode t := rfl
@[simp] theorem encode_add (s t : Language.ring.Term ℕ) :
    encode (s + t) = .inr 3 :: (encode s ++ encode t) := rfl
@[simp] theorem encode_mul (s t : Language.ring.Term ℕ) :
    encode (s * t) = .inr 4 :: (encode s ++ encode t) := rfl

/-- Apply a token to a term stack, rejecting missing arguments. -/
def step : Token → List (Language.ring.Term ℕ) → Option (List (Language.ring.Term ℕ))
  | .inl n, s => some (.var n :: s)
  | .inr 0, s => some (0 :: s)
  | .inr 1, s => some (1 :: s)
  | .inr 2, a :: s => some (-a :: s)
  | .inr 3, a :: b :: s => some ((a + b) :: s)
  | .inr 4, a :: b :: s => some ((a * b) :: s)
  | _, _ => none

/-- Parse all terms in a prefix stream onto an existing stack. -/
def parse (l : List Token) (s : Option (List (Language.ring.Term ℕ))) :
    Option (List (Language.ring.Term ℕ)) :=
  l.foldr (fun t r => r.bind (step t)) s

@[simp] theorem parse_nil (s : Option (List (Language.ring.Term ℕ))) : parse [] s = s := rfl

@[simp] theorem parse_cons (t : Token) (l : List Token)
    (s : Option (List (Language.ring.Term ℕ))) :
    parse (t :: l) s = (parse l s).bind (step t) := rfl

@[simp] theorem parse_append (l m : List Token)
    (s : Option (List (Language.ring.Term ℕ))) : parse (l ++ m) s = parse l (parse m s) := by
  simp [parse, List.foldr_append]

@[simp] theorem parse_none (l : List Token) : parse l none = none := by
  induction l with
  | nil => rfl
  | cons t l ih => simp [ih]

/-- Prefix serialization pushes exactly the original term, for any initial stack. -/
theorem parse_encode (t : Language.ring.Term ℕ) (s : List (Language.ring.Term ℕ)) :
    parse (encode t) (some s) = some (t :: s) := by
  induction t generalizing s with
  | var n => rfl
  | func f ts ih =>
    cases f <;> simp [encode, step, ih]
    all_goals
      change Term.func _ _ = Term.func _ _
      congr 1
      funext i
      fin_cases i <;> rfl

/-- Decode a stream only when it contains exactly one complete term. -/
def decode (l : List Token) : Option (Language.ring.Term ℕ) :=
  match parse l (some []) with
  | some [t] => some t
  | _ => none

/-- Native terms are recovered exactly by the parser. -/
@[simp] theorem decode_encode (t : Language.ring.Term ℕ) : decode (encode t) = some t := by
  simp [decode, parse_encode]

/-- Distinct native terms have distinct prefix codes. -/
theorem encode_injective : Function.Injective encode := by
  intro a b h
  have hd := congrArg decode h
  simpa using hd

/-- A successful stack step consumes exactly the prefix represented by its token. -/
theorem step_encode (t : Token) (s r : List (Language.ring.Term ℕ))
    (h : step t s = some r) : r.flatMap encode = t :: s.flatMap encode := by
  rcases t with n | i
  · simp only [step, Option.some.injEq] at h
    subst r
    rfl
  · fin_cases i <;> cases s with
    | nil => simp [step] at h <;> subst r <;> simp
    | cons a s =>
      cases s <;> simp [step] at h <;> subst r <;>
        simp [List.flatMap_cons, List.append_assoc]

/-- Successful parsing preserves the entire input; no malformed suffix is discarded. -/
theorem parse_encode_flatMap (l : List Token) (s r : List (Language.ring.Term ℕ))
    (h : parse l (some s) = some r) : r.flatMap encode = l ++ s.flatMap encode := by
  induction l generalizing r with
  | nil => simpa using congrArg (List.flatMap encode) (Option.some.inj h.symm)
  | cons t l ih =>
    obtain ⟨m, hm, hs⟩ := Option.bind_eq_some_iff.mp h
    rw [step_encode t m r hs, ih m hm, List.cons_append]

/-- Any successful single-term parse re-encodes to exactly the original stream. -/
theorem encode_of_decode {l : List Token} {t : Language.ring.Term ℕ}
    (h : decode l = some t) : encode t = l := by
  unfold decode at h
  split at h
  · rename_i t' ht'
    cases h
    simpa using parse_encode_flatMap l [] [t] ht'
  · contradiction

/-- Apply one arity to a numerical stack height. -/
def heightStep (t : Token) (n : ℕ) : Option ℕ :=
  if arity t ≤ n then some (n - arity t + 1) else none

/-- Numerical stack evaluation of a prefix stream. -/
def height (l : List Token) (n : Option ℕ) : Option ℕ :=
  l.foldr (fun t r => r.bind (heightStep t)) n

/-- The stack-height evaluator agrees with the actual syntax parser. -/
theorem step_length (t : Token) (s : List (Language.ring.Term ℕ)) :
    (step t s).map List.length = heightStep t s.length := by
  rcases t with n | i
  · simp [step, heightStep, arity]
  · fin_cases i <;> cases s with
    | nil => simp [step, heightStep, arity]
    | cons a s => cases s <;> simp [step, heightStep, arity]

/-- Numerical validity accounts for every possible stack underflow. -/
theorem parse_length (l : List Token) (s : Option (List (Language.ring.Term ℕ))) :
    (parse l s).map List.length = height l (s.map List.length) := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    change ((parse l s).bind (step t)).map List.length =
      (height l (s.map List.length)).bind (heightStep t)
    rw [← ih]
    cases parse l s <;> simp [step_length]

/-- Prefix streams representing one complete term. -/
def Valid (l : List Token) : Prop := height l (some 0) = some 1

/-- Every serialized native term passes the numerical validity check. -/
theorem valid_encode (t : Language.ring.Term ℕ) : Valid (encode t) := by
  have h := parse_length (encode t) (some [])
  simpa [Valid, parse_encode] using h.symm

/-- Numerical validity is equivalent to success of the exact single-term decoder. -/
theorem valid_iff_decode (l : List Token) : Valid l ↔ ∃ t, decode l = some t := by
  have h := parse_length l (some [])
  cases hp : parse l (some []) with
  | none => simp [hp, Valid, decode] at h ⊢; exact h.symm ▸ (by simp)
  | some s =>
    simp only [hp, Option.map_some, List.length_nil] at h
    rw [Valid, ← h, Option.some.injEq]
    cases s with
    | nil => simp [decode, hp]
    | cons a s => cases s <;> simp [decode, hp]

/-- The primitive-recursive validity condition characterizes exactly the image of serialization. -/
theorem valid_iff_mem_range (l : List Token) : Valid l ↔ l ∈ Set.range encode := by
  rw [valid_iff_decode]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, encode_of_decode ht⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, decode_encode t⟩

/-- Native terms are equivalent to the subtype of valid finite prefix streams. -/
def codeEquiv : Language.ring.Term ℕ ≃ {l : List Token // Valid l} where
  toFun t := ⟨encode t, valid_encode t⟩
  invFun l := (decode l.val).getD (.var 0)
  left_inv t := by simp
  right_inv l := by
    obtain ⟨t, ht⟩ := (valid_iff_decode l.val).mp l.property
    apply Subtype.ext
    change encode ((decode l.val).getD (.var 0)) = l.val
    rw [ht, Option.getD_some]
    exact encode_of_decode ht

end Surreal.RingTermCode
