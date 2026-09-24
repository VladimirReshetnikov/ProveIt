import Surreal.Algebra.RingTermScope

/-!
# Primitive-recursive scope checks and finite-context term encodings

The bounded-variable coding step for `odg:def:thm:saturation`. Scope checking
is uniform in the number of available variables, including zero. Every finite
context receives an explicit native-term coding with primitive-recursive
serialization and parsing.
-/

namespace Surreal.RingTermScope
open FirstOrder FirstOrder.Language RingTermCode

/-- Checking one variable token against a context bound is primitive recursive. -/
theorem tokenScope_primrec : Primrec₂ tokenScope := by
  have h : Primrec (fun p : ℕ × Token => (Sum.casesOn p.2
      (fun k => decide (k < p.1)) (fun _ => true) : Bool)) := Primrec.sumCasesOn Primrec.snd
    (Primrec.nat_lt.decide.comp Primrec.snd (Primrec.fst.comp Primrec.fst)).to₂
    (Primrec.const true).to₂
  exact h.to₂.of_eq (fun n t => by cases t <;> rfl)

/-- The complete scope check is primitive recursive in context size and prefix stream. -/
theorem checkScope_primrec : Primrec₂ checkScope :=
  (Primrec.list_foldr Primrec.snd (Primrec.const true)
    (Primrec.and.comp
      (tokenScope_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂).to₂

/-- Joint syntax and scope validity is primitive recursive, uniformly in the context size. -/
theorem valid_primrec : PrimrecRel Valid :=
  (RingTermCode.valid_primrec.comp Primrec.snd).and
    (Primrec.eq.comp checkScope_primrec (Primrec.const true))

local instance (n : ℕ) : DecidablePred (Valid n) := fun l =>
  inferInstanceAs (Decidable (RingTermCode.height l (some 0) = some 1 ∧ checkScope n l = true))

/-- Explicit primitive-recursive coding of native terms with finitely many variables. -/
@[implicit_reducible]
def termPrimcodable (n : ℕ) : Primcodable (Language.ring.Term (Fin n)) :=
  letI : Primcodable {l : List Token // Valid n l} :=
    Primcodable.subtype (valid_primrec.comp (Primrec.const n) Primrec.id)
  Primcodable.ofEquiv {l : List Token // Valid n l} (codeEquiv n)

section FixedContext
variable (n : ℕ)
local instance : Primcodable {l : List Token // Valid n l} :=
  Primcodable.subtype (valid_primrec.comp (Primrec.const n) Primrec.id)
local instance : Primcodable (Language.ring.Term (Fin n)) := termPrimcodable n

/-- Scoped term serialization is primitive recursive for each finite context. -/
theorem encode_primrec : Primrec (encode (n := n)) :=
  Primrec.subtype_val.comp (Primrec.of_equiv (e := codeEquiv n))

/-- The scoped native term's natural-number code is its prefix stream's code. -/
theorem encode_nat_eq (t : Language.ring.Term (Fin n)) :
    Encodable.encode t = Encodable.encode (encode t) := rfl

/-- The encoded parser is exactly the filter by syntactic and scope validity. -/
theorem encode_decode_eq (l : List Token) :
    Encodable.encode (decode n l) = if Valid n l then Encodable.encode l + 1 else 0 := by
  by_cases hl : Valid n l
  · obtain ⟨t, ht⟩ := (valid_iff_decode n l).mp hl
    rw [ht, Encodable.encode_some, encode_nat_eq, encode_of_decode ht, if_pos hl]
  · have hn : decode n l = none := by
      cases h : decode n l with
      | none => rfl
      | some t => exact False.elim (hl ((valid_iff_decode n l).mpr ⟨t, h⟩))
    simp [hn, hl]

/-- Parsing into native bounded terms is primitive recursive. -/
theorem decode_primrec : Primrec (decode n) := by
  apply Primrec.encode_iff.mp
  exact (Primrec.ite (valid_primrec.comp (Primrec.const n) Primrec.id)
    (Primrec.succ.comp Primrec.encode) (Primrec.const 0)).of_eq
    (fun l => (encode_decode_eq n l).symm)

end FixedContext
end Surreal.RingTermScope
