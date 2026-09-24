import Surreal.Algebra.RingTermCode

/-!
# Primitive-recursive validity of native ring-term prefix codes

The syntax-coding prerequisite in `odg:def:thm:saturation`. The token
alphabet and finite token lists use Mathlib's existing encodings. Validity
is established by a primitive-recursive stack-height scan, and the parser
proof identifies this predicate with the exact image of native term encoding.
-/

namespace Surreal.RingTermCode

/-- Reading token arities is primitive recursive. -/
theorem arity_primrec : Primrec arity := by
  have hf : Primrec (fun i : Fin 5 => if i.val < 2 then 0 else if i.val = 2 then 1 else 2) :=
    Primrec.ite (Primrec.nat_lt.comp Primrec.fin_val (Primrec.const 2)) (Primrec.const 0)
      (Primrec.ite (Primrec.eq.comp Primrec.fin_val (Primrec.const 2))
        (Primrec.const 1) (Primrec.const 2))
  exact (Primrec.sumCasesOn Primrec.id (Primrec.const 0).to₂ (hf.comp Primrec.snd).to₂).of_eq
    (fun t => by cases t <;> rfl)

/-- A numerical stack step, including rejection of underflow, is primitive recursive. -/
theorem heightStep_primrec : Primrec₂ heightStep :=
  (Primrec.ite (Primrec.nat_le.comp (arity_primrec.comp Primrec.fst) Primrec.snd)
    (Primrec.option_some.comp (Primrec.succ.comp
      (Primrec.nat_sub.comp Primrec.snd (arity_primrec.comp Primrec.fst))))
    (Primrec.const none)).to₂

/-- Propagating a failed scan through subsequent tokens is primitive recursive. -/
theorem heightBind_primrec : Primrec₂ (fun (t : Token) (r : Option ℕ) => r.bind (heightStep t)) :=
  (Primrec.option_bind Primrec.snd
    (heightStep_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).to₂

/-- The complete stack-height scan is primitive recursive in stream and initial height. -/
theorem height_primrec : Primrec₂ height :=
  (Primrec.list_foldr Primrec.fst Primrec.snd
    (heightBind_primrec.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂).to₂

/-- Prefix validity is a primitive-recursive predicate on the full code space. -/
theorem valid_primrec : PrimrecPred Valid :=
  Primrec.eq.comp (height_primrec.comp Primrec.id (Primrec.const (some 0)))
    (Primrec.const (some 1))

/-- The exact range of the native term encoder, not just a necessary condition, is primitive recursive. -/
theorem range_encode_primrec : PrimrecPred (fun l => l ∈ Set.range encode) :=
  valid_primrec.of_eq valid_iff_mem_range

local instance : DecidablePred Valid := fun l =>
  inferInstanceAs (Decidable (height l (some 0) = some 1))

/-- Primitive-recursive coding of native terms by exactly the valid prefix streams. -/
@[implicit_reducible]
def termPrimcodable : Primcodable (FirstOrder.Language.ring.Term ℕ) :=
  letI : Primcodable {l : List Token // Valid l} := Primcodable.subtype valid_primrec
  Primcodable.ofEquiv {l : List Token // Valid l} codeEquiv

section Constructors
open FirstOrder FirstOrder.Language
local instance : Primcodable {l : List Token // Valid l} := Primcodable.subtype valid_primrec
local instance : Primcodable (Language.ring.Term ℕ) := termPrimcodable

/-- Prefix serialization is primitive recursive under the explicit term coding. -/
theorem encode_primrec : Primrec encode :=
  Primrec.subtype_val.comp (Primrec.of_equiv (e := codeEquiv))

/-- To verify a function returning terms it suffices to verify its prefix serialization. -/
theorem primrec_iff_encode {α : Type*} [Primcodable α] (f : α → Language.ring.Term ℕ) :
    Primrec f ↔ Primrec (fun a => encode (f a)) := by
  constructor
  · exact fun h => encode_primrec.comp h
  · intro h
    have hc : Primrec (fun a => codeEquiv (f a)) := Primrec.subtype_val_iff.mp h
    exact ((Primrec.of_equiv_symm (e := codeEquiv)).comp hc).of_eq (fun a => codeEquiv.symm_apply_apply (f a))

/-- The term's natural-number code is exactly the code of its prefix token list. -/
theorem encode_nat_eq (t : Language.ring.Term ℕ) :
    Encodable.encode t = Encodable.encode (encode t) := rfl

/-- The parser's encoded output is a primitive-recursive validity filter. -/
theorem encode_decode_eq (l : List Token) :
    Encodable.encode (decode l) = if Valid l then Encodable.encode l + 1 else 0 := by
  by_cases hl : Valid l
  · obtain ⟨t, ht⟩ := (valid_iff_decode l).mp hl
    rw [ht, Encodable.encode_some, encode_nat_eq, encode_of_decode ht, if_pos hl]
  · have hn : decode l = none := by
      cases h : decode l with
      | none => rfl
      | some t => exact False.elim (hl ((valid_iff_decode l).mpr ⟨t, h⟩))
    simp [hn, hl]

/-- The exact native term decoder is primitive recursive as well as executable. -/
theorem decode_primrec : Primrec decode := by
  apply Primrec.encode_iff.mp
  exact (Primrec.ite valid_primrec (Primrec.succ.comp Primrec.encode)
    (Primrec.const 0)).of_eq (fun l => (encode_decode_eq l).symm)

/-- Variable construction is primitive recursive in its index. -/
theorem var_primrec : Primrec (Term.var : ℕ → Language.ring.Term ℕ) := by
  apply (primrec_iff_encode _).mpr
  exact Primrec.list_cons.comp Primrec.sumInl (Primrec.const [])

/-- Native negation is primitive recursive. -/
theorem neg_primrec : Primrec (fun t : Language.ring.Term ℕ => -t) := by
  apply (primrec_iff_encode _).mpr
  simpa using Primrec.list_cons.comp (Primrec.const (Sum.inr (2 : Fin 5))) encode_primrec

/-- Native addition is primitive recursive. -/
theorem add_primrec : Primrec₂ (fun s t : Language.ring.Term ℕ => s + t) := by
  apply (primrec_iff_encode _).mpr
  simpa using Primrec.list_cons.comp (Primrec.const (Sum.inr (3 : Fin 5)))
    (Primrec.list_append.comp (encode_primrec.comp Primrec.fst) (encode_primrec.comp Primrec.snd))

/-- Native multiplication is primitive recursive. -/
theorem mul_primrec : Primrec₂ (fun s t : Language.ring.Term ℕ => s * t) := by
  apply (primrec_iff_encode _).mpr
  simpa using Primrec.list_cons.comp (Primrec.const (Sum.inr (4 : Fin 5)))
    (Primrec.list_append.comp (encode_primrec.comp Primrec.fst) (encode_primrec.comp Primrec.snd))

end Constructors

end Surreal.RingTermCode
