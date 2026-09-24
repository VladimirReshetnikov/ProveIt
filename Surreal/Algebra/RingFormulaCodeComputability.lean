import Surreal.Algebra.RingFormulaValidity

/-!
# Primitive-recursive coding and parsing of native ring formulas

The effective bounded-formula syntax prerequisite for `odg:def:thm:saturation`.
Numeric context validation is primitive recursive and its accepted streams
are exactly native formulas. This supplies a genuine Primcodable structure,
with primitive-recursive serialization and parsing.
-/

namespace Surreal.RingFormulaCode
open FirstOrder FirstOrder.Language

/-- Matching the contexts of an implication is primitive recursive. -/
theorem impScope_primrec : Primrec impScope :=
  Primrec.option_bind (Primrec.list_getElem?.comp Primrec.id (Primrec.const 0))
    (Primrec.option_bind (Primrec.list_getElem?.comp Primrec.fst (Primrec.const 1))
      (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.snd.comp Primrec.fst))
        (Primrec.option_some.comp (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst)
          (Primrec.list_drop.comp (Primrec.const 2) (Primrec.fst.comp Primrec.fst))))
        (Primrec.const none)).to₂).to₂

/-- Removing one available bound variable is primitive recursive. -/
theorem allScope_primrec : Primrec allScope :=
  Primrec.option_bind Primrec.list_head?
    (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const none)
      (Primrec.option_some.comp (Primrec.list_cons.comp
        (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1))
        (Primrec.list_tail.comp Primrec.fst)))).to₂

local instance (n : ℕ) (l : List RingTermCode.Token) : Decidable (RingTermScope.Valid n l) :=
  inferInstanceAs (Decidable (RingTermCode.height l (some 0) = some 1 ∧
    RingTermScope.checkScope n l = true))

/-- Every context-stack transition is primitive recursive, including checking both equation terms. -/
theorem scopeStep_primrec : Primrec₂ scopeStep := by
  have ha : Primrec₂ (fun (a : ℕ × List RingTermCode.Token × List RingTermCode.Token) (s : List ℕ) =>
      if RingTermScope.Valid (1 + a.1) a.2.1 ∧ RingTermScope.Valid (1 + a.1) a.2.2 then
        some (a.1 :: s) else none) :=
    (Primrec.ite
      ((RingTermScope.valid_primrec.comp
        (Primrec.nat_add.comp (Primrec.const 1) (Primrec.fst.comp Primrec.fst))
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))).and
       (RingTermScope.valid_primrec.comp
        (Primrec.nat_add.comp (Primrec.const 1) (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
      (Primrec.option_some.comp (Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst) Primrec.snd))
      (Primrec.const none)).to₂
  have ho : Primrec₂ (fun (i : Fin 2) (s : List ℕ) =>
      if i.val = 0 then impScope s else allScope s) :=
    (Primrec.ite (Primrec.eq.comp (Primrec.fin_val.comp Primrec.fst) (Primrec.const 0))
      (impScope_primrec.comp Primrec.snd) (allScope_primrec.comp Primrec.snd)).to₂
  have hr : Primrec (fun p : (ℕ ⊕ Fin 2) × List ℕ =>
      (Sum.casesOn p.1 (fun n => some (n :: p.2))
        (fun i => if i.val = 0 then impScope p.2 else allScope p.2) : Option (List ℕ))) :=
    Primrec.sumCasesOn Primrec.fst
      (Primrec.option_some.comp (Primrec.list_cons.comp Primrec.snd (Primrec.snd.comp Primrec.fst))).to₂
      (ho.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂
  have h : Primrec (fun p : Token × List ℕ =>
      (Sum.casesOn p.1
        (fun a => if RingTermScope.Valid (1 + a.1) a.2.1 ∧ RingTermScope.Valid (1 + a.1) a.2.2 then
          some (a.1 :: p.2) else none)
        (fun r => Sum.casesOn r (fun n => some (n :: p.2))
          (fun i => if i.val = 0 then impScope p.2 else allScope p.2)) : Option (List ℕ))) :=
    Primrec.sumCasesOn Primrec.fst
      (ha.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂
      (hr.comp (Primrec.snd.pair (Primrec.snd.comp Primrec.fst))).to₂
  exact h.to₂.of_eq (fun t s => by rcases t with a | (n | i) <;> rfl)

/-- Context-stack scanning is primitive recursive in stream and initial stack. -/
theorem scopes_primrec : Primrec₂ scopes := by
  have hs : Primrec₂ (fun (t : Token) (s : Option (List ℕ)) => s.bind (scopeStep t)) :=
    (Primrec.option_bind Primrec.snd
      (scopeStep_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).to₂
  exact (Primrec.list_foldr Primrec.fst Primrec.snd
    (hs.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).to₂

/-- Extracting the context of a single complete formula is primitive recursive. -/
theorem scope_primrec : Primrec scope := by
  have hs : Primrec (fun s : List ℕ => if s.length = 1 then s.head? else none) :=
    Primrec.ite (Primrec.eq.comp Primrec.list_length (Primrec.const 1)) Primrec.list_head? (Primrec.const none)
  have h := Primrec.option_bind (scopes_primrec.comp Primrec.id (Primrec.const (some [])))
    (hs.comp Primrec.snd).to₂
  exact h.of_eq (fun l => by
    dsimp only [id_eq]
    unfold scope
    cases scopes l (some []) with
    | none => rfl
    | some s => cases s with
      | nil => rfl
      | cons n s => cases s <;> simp)

/-- The exact native formula-code language is primitive recursive. -/
theorem valid_primrec : PrimrecPred Valid :=
  Primrec.eq.comp (Primrec.option_isSome.comp scope_primrec) (Primrec.const true)

local instance : DecidablePred Valid := fun l => inferInstanceAs (Decidable ((scope l).isSome = true))

/-- Explicit primitive-recursive coding of all unary native bounded ring formulas. -/
@[implicit_reducible]
def formulaPrimcodable : Primcodable ScopedFormula :=
  letI : Primcodable {l : List Token // Valid l} := Primcodable.subtype valid_primrec
  Primcodable.ofEquiv {l : List Token // Valid l} codeEquiv

section Native
local instance : Primcodable {l : List Token // Valid l} := Primcodable.subtype valid_primrec
local instance : Primcodable ScopedFormula := formulaPrimcodable

/-- Serialization of scoped native formulas is primitive recursive. -/
theorem encode_primrec : Primrec encodeScoped :=
  Primrec.subtype_val.comp (Primrec.of_equiv (e := codeEquiv))

/-- Natural-number codes are exactly the codes of the prefix token lists. -/
theorem encode_nat_eq (φ : ScopedFormula) :
    Encodable.encode φ = Encodable.encode (encodeScoped φ) := rfl

/-- The encoded native parser is the primitive-recursive filter by exact syntax validity. -/
theorem encode_decode_eq (l : List Token) :
    Encodable.encode (decode l) = if Valid l then Encodable.encode l + 1 else 0 := by
  by_cases hl : Valid l
  · obtain ⟨φ, hφ⟩ := (valid_iff_decode l).mp hl
    rw [hφ, Encodable.encode_some, encode_nat_eq, encode_of_decode hφ, if_pos hl]
  · have hn : decode l = none := by
      cases h : decode l with
      | none => rfl
      | some φ => exact False.elim (hl ((valid_iff_decode l).mpr ⟨φ, h⟩))
    simp [hn, hl]

/-- Parsing arbitrary finite streams into native scoped formulas is primitive recursive. -/
theorem decode_primrec : Primrec decode := by
  apply Primrec.encode_iff.mp
  exact (Primrec.ite valid_primrec (Primrec.succ.comp Primrec.encode)
    (Primrec.const 0)).of_eq (fun l => (encode_decode_eq l).symm)

/-- Reading a native formula's number of available bound variables is primitive recursive. -/
theorem context_primrec : Primrec (Sigma.fst : ScopedFormula → ℕ) := by
  have h := Primrec.option_getD.comp (scope_primrec.comp encode_primrec) (Primrec.const 0)
  exact h.of_eq (fun φ => by simp)

end Native
end Surreal.RingFormulaCode
