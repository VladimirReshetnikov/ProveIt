module
public import M6PA.Theory
public import M6PA.Calibration.RelationalSourceSyntax
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Coding
@[expose] public section

/-! Numeric coding for the existing relational source language. The convention
is Foundation's set-language convention: equality 0, membership 1, both binary,
with no function symbols. This does not change native target formula codes. -/
namespace M6.PA.RelationalSource
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

instance relationEncodable (k : Nat) : Encodable (Relation k) where
  encode := fun r => match r with
    | .eq => 0
    | .mem => 1
  decode := fun e => match k,e with
    | 2,0 => some .eq
    | 2,1 => some .mem
    | _,_ => none
  encodek := fun r => by cases r <;> rfl

instance languageEncodable : language.Encodable where
  func _ := inferInstanceAs (Encodable Empty)
  rel k := relationEncodable k

@[simp] theorem encode_eq : Encodable.encode (Relation.eq : language.Rel 2) = 0 := rfl
@[simp] theorem encode_mem : Encodable.encode (Relation.mem : language.Rel 2) = 1 := rfl

theorem relation_range {k r : Nat} :
    r ∈ Set.range (Encodable.encode : language.Rel k → Nat) ↔
      k=2 ∧ (r=0 ∨ r=1) := by
  constructor
  · rintro ⟨r,rfl⟩
    cases r
    · exact ⟨rfl,Or.inl rfl⟩
    · exact ⟨rfl,Or.inr rfl⟩
  · rintro ⟨rfl,rfl|rfl⟩
    · exact ⟨Relation.eq,rfl⟩
    · exact ⟨Relation.mem,rfl⟩

instance languageDefinable : language.LORDefinable where
  func := .mkSigma “k f. ⊥”
  rel := .mkSigma “k r. k=2 ∧ (r=0 ∨ r=1)”
  func_iff {k c} := by
    simp only [Set.mem_range]
    constructor
    · rintro ⟨f,_⟩
      exact nomatch f
    · simp
  rel_iff {k c} := by simpa using! (relation_range (k := k) (r := c))

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem source_no_functions (k f : V) : ¬language.IsFunc k f := by
  change ¬(V ⊧/![k,f] (⊥ : ArithmeticSemisentence 2))
  simp

@[simp] theorem source_relations (k r : V) :
    language.IsRel k r ↔ k=2 ∧ (r=0 ∨ r=1) := by
  change (V ⊧/![k,r] “k r. k=2 ∧ (r=0 ∨ r=1)”) ↔ _
  simp

local instance sourceRelQuote : GödelQuote (Relation 2) V := gödelQuoteRel (L := language) 2

/-- Calibrate the chosen relation tags to Foundation's actual quotations. -/
theorem quote_source_eq : (⌜(Relation.eq : language.Rel 2)⌝ : V) = 0 := by
  change ((Encodable.encode (Relation.eq : language.Rel 2) : Nat) : V) = 0
  simp

theorem quote_source_mem : (⌜(Relation.mem : language.Rel 2)⌝ : V) = 1 := by
  change ((Encodable.encode (Relation.mem : language.Rel 2) : Nat) : V) = 1
  simp

/-- Even nonstandard well-formed source terms have only variable constructors. -/
theorem source_term_cases (n t : V) :
    IsSemiterm language n t ↔
      (∃ i < n, t = qqBvar i) ∨ ∃ i, t = qqFvar i := by
  rw [IsSemiterm.case_iff]
  simp

#print axioms relation_range
#print axioms quote_source_eq
#print axioms quote_source_mem
#print axioms source_relations
#print axioms source_term_cases
end M6.PA.RelationalSource

