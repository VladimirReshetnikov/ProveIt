import DiophantineConsistency.AnnotatedRuleSchedules
import DiophantineConsistency.AnnotatedContextLookup

/-! # Supplied checking of the exact original rule-side conditions -/
namespace DiophantineConsistency.AnnotatedRuleSide
open SetTheory SetTheory.Form AnnotatedProofChecker AnnotatedProofCode
open ScalarPRCode DirectScalar
open AnnotatedRuleCoordinates (Coordinates quote)
open AnnotatedRuleSchedules (rule ofRule)
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000
attribute [local irreducible] Nat.unpair

def value (tag : Nat) (r : Coordinates) (membershipIndex : Nat) : Nat :=
  if tag=0 then AnnotatedContextLookup.referenceValue
    (Nat.pair r.context (Nat.pair membershipIndex r.a)) else 1

private theorem exists_reference (G : List Form) (a : Form) :
    (∃ index,AnnotatedContextLookup.referenceValue
      (Nat.pair (AnnotatedContext.contextCode G) (Nat.pair index (formCode a)))=1) ↔ a∈G := by
  constructor
  · rintro ⟨index,h⟩
    exact List.mem_of_getElem? ((AnnotatedContextLookup.reference_context G index a).mp h)
  · intro h
    obtain ⟨index,hi⟩ := List.getElem?_of_mem h
    exact ⟨index,(AnnotatedContextLookup.reference_context G index a).mpr hi⟩

theorem exists_quote_iff (tag : Fin 17) (G : List Form) (a b c : Form) (i j : Nat) :
    (∃ index,value tag.val (quote G a b c i j) index=1) ↔ (rule tag G a b c i j).side=true := by
  fin_cases tag <;> simp [value,quote,rule,Rule.side,exists_reference]

theorem quote_sound (tag : Fin 17) (G : List Form) (a b c : Form) (i j index : Nat)
    (h : value tag.val (quote G a b c i j) index=1) : (rule tag G a b c i j).side=true :=
  (exists_quote_iff tag G a b c i j).mp ⟨index,h⟩

theorem exists_ofRule_iff (original : Rule) :
    (∃ index,value (ofRule original).1.val (ofRule original).2 index=1) ↔ original.side=true := by
  cases original <;> simp [ofRule,value,quote,Rule.side,exists_reference]

namespace P
open AnnotatedRenameLocal.Program (left right)

def inputValue (n : Nat) : Nat :=
  value n.unpair.1 (AnnotatedRuleCoordinates.decode n.unpair.2.unpair.1) n.unpair.2.unpair.2

def program : R inputValue := by
  let tag := Realizes.left
  let coordinates := left Realizes.right
  let index := right Realizes.right
  let context := AnnotatedRuleSchedules.P.context.comp coordinates
  let a := AnnotatedRuleSchedules.P.a.comp coordinates
  let member := AnnotatedContextLookup.referenceProgram.comp (context.pair (index.pair a))
  refine (ifEq tag Realizes.zero member (constant 1)).ofEq ?_
  intro n
  simp only [inputValue,value]

end P

theorem program_input (tag : Nat) (r : Coordinates) (index : Nat) :
    P.program.val.eval (Nat.pair tag (Nat.pair (AnnotatedRuleCoordinates.encode r) index))=
      value tag r index := by
  rw [P.program.property]
  simp only [P.inputValue,Nat.unpair_pair,AnnotatedRuleCoordinates.decode_encode]

theorem program_primrec : Nat.Primrec P.program.val.eval := P.program.val.primrec

end DiophantineConsistency.AnnotatedRuleSide
