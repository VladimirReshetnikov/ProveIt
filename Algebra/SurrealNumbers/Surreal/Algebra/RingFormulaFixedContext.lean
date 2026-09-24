import Surreal.Algebra.RingFormulaCodeComputability

/-!
# Primitive-recursive coding at a fixed bound-variable context

The unary formulas in `odg:def:thm:saturation` have one free variable and
zero bound variables at the outermost level. This module specializes the
scoped formula encoding to every fixed context, including that case.
-/

namespace Surreal.RingFormulaCode
open FirstOrder FirstOrder.Language

/-- Formulas with a fixed context are exactly the matching fiber of scoped formulas. -/
def fixedContextEquiv (n : ℕ) : Language.ring.BoundedFormula (Fin 1) n ≃
    {φ : ScopedFormula // φ.1 = n} where
  toFun φ := ⟨⟨n, φ⟩, rfl⟩
  invFun φ := φ.property ▸ φ.val.2
  left_inv _ := rfl
  right_inv φ := by
    obtain ⟨⟨m, φ⟩, h⟩ := φ
    dsimp only at h
    subst m
    rfl

local instance : Primcodable ScopedFormula := formulaPrimcodable

/-- Native bounded formulas have explicit primitive-recursive codes at every fixed context. -/
@[implicit_reducible]
def fixedFormulaPrimcodable (n : ℕ) : Primcodable (Language.ring.BoundedFormula (Fin 1) n) :=
  letI : Primcodable {φ : ScopedFormula // φ.1 = n} :=
    Primcodable.subtype (Primrec.eq.comp context_primrec (Primrec.const n))
  Primcodable.ofEquiv {φ : ScopedFormula // φ.1 = n} (fixedContextEquiv n)

/-- Decode at an explicitly requested context, rejecting any other context. -/
def decodeFixed (n : ℕ) (l : List Token) : Option (Language.ring.BoundedFormula (Fin 1) n) := do
  let φ ← decode l
  if h : φ.1 = n then some (h ▸ φ.2) else none

/-- Fixed-context decoding recovers the native formula. -/
@[simp] theorem decodeFixed_encode {n : ℕ} (φ : Language.ring.BoundedFormula (Fin 1) n) :
    decodeFixed n (encode φ) = some φ := by
  change decodeFixed n (encodeScoped ⟨n, φ⟩) = some φ
  simp [decodeFixed]

section FixedContext
variable (n : ℕ)
local instance : Primcodable {φ : ScopedFormula // φ.1 = n} :=
  Primcodable.subtype (Primrec.eq.comp context_primrec (Primrec.const n))
local instance : Primcodable (Language.ring.BoundedFormula (Fin 1) n) := fixedFormulaPrimcodable n

/-- Adding the fixed context tag is primitive recursive. -/
theorem tag_primrec : Primrec (fun φ : Language.ring.BoundedFormula (Fin 1) n =>
    (⟨n, φ⟩ : ScopedFormula)) :=
  Primrec.subtype_val.comp (Primrec.of_equiv (e := fixedContextEquiv n))

/-- Serialization is primitive recursive for native formulas at a fixed context. -/
theorem fixed_encode_primrec : Primrec (encode (n := n)) :=
  encode_primrec.comp (tag_primrec n)

/-- Fixed-context formulas retain exactly the same natural-number code as their prefix streams. -/
theorem fixed_encode_nat_eq (φ : Language.ring.BoundedFormula (Fin 1) n) :
    Encodable.encode φ = Encodable.encode (encode φ) := rfl

/-- Fixed-context parsing is the exact primitive-recursive filter by the numerical context. -/
theorem encode_decodeFixed_eq (l : List Token) :
    Encodable.encode (decodeFixed n l) =
      if scope l = some n then Encodable.encode l + 1 else 0 := by
  have hs := decode_scope l
  cases hd : decode l with
  | none => simp [hd] at hs; simp [decodeFixed, hd, ← hs]
  | some φ =>
    obtain ⟨m, φ⟩ := φ
    simp only [hd, Option.map_some] at hs
    by_cases hm : m = n
    · subst m
      have he : encode φ = l := encode_of_decode hd
      simp [decodeFixed, hd, ← hs, fixed_encode_nat_eq, he]
    · simp [decodeFixed, hd, ← hs, hm]

/-- The native parser for each fixed context is primitive recursive. -/
theorem decodeFixed_primrec : Primrec (decodeFixed n) := by
  apply Primrec.encode_iff.mp
  exact (Primrec.ite (Primrec.eq.comp scope_primrec (Primrec.const (some n)))
    (Primrec.succ.comp Primrec.encode) (Primrec.const 0)).of_eq
    (fun l => (encode_decodeFixed_eq n l).symm)

end FixedContext
end Surreal.RingFormulaCode
