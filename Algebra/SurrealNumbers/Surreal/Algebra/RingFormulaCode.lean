import Surreal.Algebra.RingTermScope
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Prefix codes for native bounded ring formulas

The formula-coding prerequisite for `odg:def:thm:saturation`. There is one
free variable and an arbitrary finite bound-variable context. Equation tokens
contain scope-checked term codes; implication requires matching contexts,
and universal quantification reduces a positive context by one.
-/

namespace Surreal.RingFormulaCode
open FirstOrder FirstOrder.Language

/-- All bound-variable contexts of unary native ring formulas. -/
abbrev ScopedFormula := Σ n, Language.ring.BoundedFormula (Fin 1) n

/-- An equation with its context and two term codes, a falsum with its context,
or an implication/universal-quantifier token. -/
abbrev Token := (ℕ × List RingTermCode.Token × List RingTermCode.Token) ⊕ (ℕ ⊕ Fin 2)

/-- Pack the free variable and bound-variable indices into a single finite context. -/
def termEquiv (n : ℕ) :
    Language.ring.Term (Fin 1 ⊕ Fin n) ≃ Language.ring.Term (Fin (1 + n)) :=
  Term.relabelEquiv finSumFinEquiv

/-- Prefix serialization retains every atom's bound-variable context. -/
def encode : {n : ℕ} → Language.ring.BoundedFormula (Fin 1) n → List Token
  | n, .falsum => [.inr (.inl n)]
  | n, .equal a b => [.inl (n, RingTermScope.encode (termEquiv n a),
      RingTermScope.encode (termEquiv n b))]
  | _, .rel r _ => r.elim
  | _, .imp φ ψ => .inr (.inr 0) :: (encode φ ++ encode ψ)
  | _, .all φ => .inr (.inr 1) :: encode φ

/-- Serialize a formula together with its context. -/
def encodeScoped (φ : ScopedFormula) : List Token := encode φ.2

/-- One exact formula-stack parsing step. -/
def step : Token → List ScopedFormula → Option (List ScopedFormula)
  | .inl (n, a, b), s => do
      let a' ← RingTermScope.decode (1 + n) a
      let b' ← RingTermScope.decode (1 + n) b
      pure (⟨n, .equal ((termEquiv n).symm a') ((termEquiv n).symm b')⟩ :: s)
  | .inr (.inl n), s => some (⟨n, .falsum⟩ :: s)
  | .inr (.inr 0), ⟨n, φ⟩ :: ⟨m, ψ⟩ :: s =>
      if h : m = n then some (⟨n, φ.imp (h ▸ ψ)⟩ :: s) else none
  | .inr (.inr 1), ⟨n + 1, φ⟩ :: s => some (⟨n, .all φ⟩ :: s)
  | _, _ => none

/-- Parse a prefix stream onto an existing scoped formula stack. -/
def parse (l : List Token) (s : Option (List ScopedFormula)) : Option (List ScopedFormula) :=
  l.foldr (fun t r => r.bind (step t)) s

@[simp] theorem parse_nil (s : Option (List ScopedFormula)) : parse [] s = s := rfl
@[simp] theorem parse_cons (t : Token) (l : List Token) (s : Option (List ScopedFormula)) :
    parse (t :: l) s = (parse l s).bind (step t) := rfl
@[simp] theorem parse_append (l r : List Token) (s : Option (List ScopedFormula)) :
    parse (l ++ r) s = parse l (parse r s) := by simp [parse, List.foldr_append]
@[simp] theorem parse_none (l : List Token) : parse l none = none := by
  induction l with
  | nil => rfl
  | cons t l ih => simp [ih]

/-- Parsing a serialized formula pushes exactly that formula and its original context. -/
theorem parse_encode {n : ℕ} (φ : Language.ring.BoundedFormula (Fin 1) n) (s : List ScopedFormula) :
    parse (encode φ) (some s) = some (⟨n, φ⟩ :: s) := by
  induction φ generalizing s with
  | falsum => rfl
  | equal a b => simp [encode, step]
  | rel r _ => exact r.elim
  | imp φ ψ hφ hψ => simp [encode, step, hφ, hψ]
  | all φ hφ => simp [encode, step, hφ]

/-- Decode only a complete stream containing precisely one formula. -/
def decode (l : List Token) : Option ScopedFormula :=
  match parse l (some []) with
  | some [φ] => some φ
  | _ => none

/-- The formula codec recovers both native syntax and bound-variable context. -/
@[simp] theorem decode_encode (φ : ScopedFormula) : decode (encodeScoped φ) = some φ := by
  obtain ⟨n, φ⟩ := φ
  simp [decode, encodeScoped, parse_encode]

/-- Serialization is injective even across different bound-variable contexts. -/
theorem encode_injective : Function.Injective encodeScoped := by
  intro φ ψ h
  have hd := congrArg decode h
  simpa using hd

/-- A successful parsing step reproduces precisely its original token and argument codes. -/
theorem step_encode (t : Token) (s r : List ScopedFormula) (h : step t s = some r) :
    r.flatMap encodeScoped = t :: s.flatMap encodeScoped := by
  rcases t with ⟨n, a, b⟩ | (n | i)
  · obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b', hb, hr⟩ := Option.bind_eq_some_iff.mp h
    cases hr
    simp [List.flatMap_cons, encodeScoped, encode,
      RingTermScope.encode_of_decode ha, RingTermScope.encode_of_decode hb]
  · simp only [step, Option.some.injEq] at h
    subst r
    rfl
  · fin_cases i
    · cases s with
      | nil => simp [step] at h
      | cons φ s =>
        cases s with
        | nil => simp [step] at h
        | cons ψ s =>
          obtain ⟨n, φ⟩ := φ
          obtain ⟨m, ψ⟩ := ψ
          change (if he : m = n then some (⟨n, φ.imp (he ▸ ψ)⟩ :: s) else none) = some r at h
          split at h
          · rename_i he
            subst m
            cases h
            simp [List.flatMap_cons, encodeScoped, encode, List.append_assoc]
          · contradiction
    · cases s with
      | nil => simp [step] at h
      | cons φ s =>
        obtain ⟨n, φ⟩ := φ
        cases n with
        | zero => simp [step] at h
        | succ n =>
          change some (⟨n, φ.all⟩ :: s) = some r at h
          cases h
          simp [List.flatMap_cons, encodeScoped, encode]

/-- Successful parsing preserves the whole stream, including scope information. -/
theorem parse_encode_flatMap (l : List Token) (s r : List ScopedFormula)
    (h : parse l (some s) = some r) : r.flatMap encodeScoped = l ++ s.flatMap encodeScoped := by
  induction l generalizing r with
  | nil => simpa using congrArg (List.flatMap encodeScoped) (Option.some.inj h.symm)
  | cons t l ih =>
    obtain ⟨m, hm, hs⟩ := Option.bind_eq_some_iff.mp h
    rw [step_encode t m r hs, ih m hm, List.cons_append]

/-- Every accepted code is precisely the serialization of the formula returned. -/
theorem encode_of_decode {l : List Token} {φ : ScopedFormula} (h : decode l = some φ) :
    encodeScoped φ = l := by
  unfold decode at h
  split at h
  · rename_i φ' hφ'
    cases h
    simpa using parse_encode_flatMap l [] [φ] hφ'
  · contradiction

end Surreal.RingFormulaCode
