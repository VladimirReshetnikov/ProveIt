module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAAxiomCodeInduction
public import M6PA.Calibration.PAPresentationAxiomWitness
@[expose] public section

/-! A finite, executable tag decoder. No decision procedure for the infinite
induction scheme is assumed here. Soundness targets the same pinned axiom graph. -/
namespace M6.PA.FoundationAxiomCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic
open Presentation

abbrev FiniteTag := Sum BaseTag EqualityTag

def FiniteTag.sentence : FiniteTag → ArithmeticSentence
  | .inl t => t.sentence
  | .inr t => t.sentence

def FiniteTag.code (t : FiniteTag) : Nat := Encodable.encode t.sentence

def finiteTags : List FiniteTag :=
  [.inl .addZero, .inl .addAssoc, .inl .addComm, .inl .addEqOfLt,
   .inl .zeroLe, .inl .zeroLtOne, .inl .oneLeOfZeroLt, .inl .addLtAdd,
   .inl .mulZero, .inl .mulOne, .inl .mulAssoc, .inl .mulComm,
   .inl .mulLtMul, .inl .distr, .inl .ltIrrefl, .inl .ltTrans, .inl .ltTri,
   .inr .refl, .inr .symm, .inr .trans, .inr .zero, .inr .one,
   .inr .add, .inr .mul, .inr .eq, .inr .lt]

theorem mem_finiteTags (t : FiniteTag) : t ∈ finiteTags := by
  rcases t with t | t <;> cases t <;> simp [finiteTags]

/-- Search uses only executable equality on natural numbers. -/
def decodeFinite (p : Nat) : Option FiniteTag :=
  finiteTags.find? (fun t => t.code == p)

theorem decodeFinite_sound {p : Nat} {t : FiniteTag}
    (h : decodeFinite p = some t) : t.code = p := by
  have := List.find?_some h
  simpa using this

theorem decodeFinite_complete (t : FiniteTag) :
    ∃ u, decodeFinite t.code = some u := by
  have h : (decodeFinite t.code).isSome := by
    simp only [decodeFinite, List.isSome_find?, List.any_eq_true]
    exact ⟨t, mem_finiteTags t, by simp⟩
  exact Option.isSome_iff_exists.mp h

theorem FiniteTag.mem (t : FiniteTag) : t.sentence ∈ theory := by
  rcases t with t | t
  · exact Or.inl t.mem
  · exact Or.inl (.equal _ t.mem)

/-- All-model soundness at the returned finite sentence's numerical code. -/
theorem decodeFinite_mem {p : Nat} {t : FiniteTag}
    (h : decodeFinite p = some t)
    (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    (p : V) ∈ theory.Δ₁Class := by
  rw [← decodeFinite_sound h]
  change (↑(Encodable.encode t.sentence) : V) ∈ theory.Δ₁Class
  rw [← Sentence.quote_eq_encode]
  exact Δ₁Class.mem_iff.mpr t.mem

#print axioms decodeFinite
#print axioms decodeFinite_sound
#print axioms decodeFinite_complete
#print axioms decodeFinite_mem
end M6.PA.FoundationAxiomCode

