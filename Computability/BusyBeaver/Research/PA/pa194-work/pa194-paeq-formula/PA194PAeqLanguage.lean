import PA194PAeqSyntax
import PA194PAeqTermCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Term.Coding
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unnecessarySeqFocus false
namespace PA194PAeq
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder

instance functionEncodable (k : Nat) : Encodable (Func k) where
  encode := fun f => match f with
    | .zero => 0 | .succ => 1 | .add => 2 | .mul => 3
  decode := fun e => match k,e with
    | 0,0 => some .zero | 1,1 => some .succ
    | 2,2 => some .add | 2,3 => some .mul | _,_ => none
  encodek := fun f => by cases f <;> rfl

instance relationEncodable (k : Nat) : Encodable (Rel k) where
  encode := fun r => match r with | .eq => 0
  decode := fun e => match k,e with | 2,0 => some .eq | _,_ => none
  encodek := fun r => by cases r <;> rfl

instance languageEncodable : language.Encodable where
  func k := functionEncodable k
  rel k := relationEncodable k

theorem function_range {k f : Nat} :
    f ∈ Set.range (Encodable.encode : language.Func k → Nat) ↔
      (k=0 ∧ f=0) ∨ (k=1 ∧ f=1) ∨ (k=2 ∧ (f=2 ∨ f=3)) := by
  constructor
  · rintro ⟨f,rfl⟩
    cases f <;> simp [Encodable.encode]
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl|rfl⟩)
    · exact ⟨.zero,rfl⟩
    · exact ⟨.succ,rfl⟩
    · exact ⟨.add,rfl⟩
    · exact ⟨.mul,rfl⟩

theorem relation_range {k r : Nat} :
    r ∈ Set.range (Encodable.encode : language.Rel k → Nat) ↔ k=2 ∧ r=0 := by
  constructor
  · rintro ⟨r,rfl⟩; cases r; exact ⟨rfl,rfl⟩
  · rintro ⟨rfl,rfl⟩; exact ⟨.eq,rfl⟩

instance languageDefinable : language.LORDefinable where
  func := .mkSigma “k f. (k=0 ∧ f=0) ∨ (k=1 ∧ f=1) ∨ (k=2 ∧ (f=2 ∨ f=3))”
  rel := .mkSigma “k r. k=2 ∧ r=0”
  func_iff {k c} := by simpa using! (function_range (k := k) (f := c))
  rel_iff {k c} := by simpa using! (relation_range (k := k) (r := c))

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem source_functions (k f : V) :
    language.IsFunc k f ↔
      (k=0 ∧ f=0) ∨ (k=1 ∧ f=1) ∨ (k=2 ∧ (f=2 ∨ f=3)) := by
  change (V ⊧/![k,f] “k f. (k=0 ∧ f=0) ∨ (k=1 ∧ f=1) ∨ (k=2 ∧ (f=2 ∨ f=3))”) ↔ _
  simp

@[simp] theorem source_relations (k r : V) : language.IsRel k r ↔ k=2 ∧ r=0 := by
  change (V ⊧/![k,r] “k r. k=2 ∧ r=0”) ↔ _
  simp

theorem quote_zero {n : Nat} : (⌜(zero : SyntacticSemiterm language n)⌝ : V) =
    qqFunc 0 0 0 := by simp [zero, SemitermVec.val]; rfl

theorem quote_successor {n : Nat} (t : SyntacticSemiterm language n) :
    (⌜succ t⌝ : V) = qqFunc 1 1 (⌜t⌝ ∷ 0) := by
  simp [succ, SemitermVec.val]
  constructor
  · change ((1 : Nat) : V) = 1
    simp
  · rfl

#print axioms function_range
#print axioms relation_range
#print axioms source_functions
#print axioms source_relations
#print axioms quote_zero
#print axioms quote_successor
end PA194PAeq

