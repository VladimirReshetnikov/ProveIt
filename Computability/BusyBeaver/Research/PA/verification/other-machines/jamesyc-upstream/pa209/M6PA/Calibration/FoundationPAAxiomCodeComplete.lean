module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAAxiomCodeFinite
public import M6PA.Calibration.FoundationPAAxiomCodeGraph
@[expose] public section

/-! Completeness for arbitrary model-valued inputs to the pinned finite axiom
branch. No alternate Δ₁ instance is installed for PeanoMinus or Peano. -/
namespace M6.PA.FoundationAxiomCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open Presentation

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Evaluate Foundation's exact finite-list presentation in any IΣ₁ model. -/
theorem ofList_iff (l : List ArithmeticSentence) (p : V) :
    (V ⊧/![p] (Theory.Δ₁.ofList l).ch.val) ↔
      ∃ σ ∈ l, p = (Encodable.encode σ : V) := by
  induction l with
  | nil =>
    change (V ⊧/![p] (⊥ : ArithmeticSemisentence 1)) ↔ _
    simp
  | cons σ l ih =>
    change (V ⊧/![p] ((Theory.Δ₁.singleton σ).ch ⋎ (Theory.Δ₁.ofList l).ch).val) ↔ _
    simp only [Bounding.HierarchySymbol.Semiformula.val_or,
      LogicalConnective.HomClass.map_or]
    rw [ih]
    change ((V ⊧/![p] “x. x = ↑(Encodable.encode σ)”) ∨ _) ↔ _
    simp [numeral_eq_natCast]

/-- The actual noncomputably chosen finite presentation has no extra
nonstandard codes: every accepted code equals one of its standard numerals. -/
theorem peanoMinus_iff_sentence (p : V) :
    p ∈ PeanoMinus.Δ₁Class ↔
      ∃ σ ∈ PeanoMinus, p = (Encodable.encode σ : V) := by
  change (V ⊧/![p] (Theory.Δ₁.ofList PeanoMinus.finite.toFinset.toList).ch.val) ↔ _
  rw [ofList_iff]
  simp

theorem FiniteTag.mem_base (t : FiniteTag) : t.sentence ∈ PeanoMinus := by
  rcases t with t | t
  · exact t.mem
  · exact .equal _ t.mem

theorem finiteTag_exists {σ : ArithmeticSentence} (h : σ ∈ PeanoMinus) :
    ∃ t : FiniteTag, t.sentence = σ := by
  cases h with
  | equal σ h =>
    cases h with
    | refl => exact ⟨.inr .refl,rfl⟩
    | symm => exact ⟨.inr .symm,rfl⟩
    | trans => exact ⟨.inr .trans,rfl⟩
    | funcExt f => cases f with
      | zero => exact ⟨.inr .zero,rfl⟩
      | one => exact ⟨.inr .one,rfl⟩
      | add => exact ⟨.inr .add,rfl⟩
      | mul => exact ⟨.inr .mul,rfl⟩
    | relExt r => cases r with
      | eq => exact ⟨.inr .eq,rfl⟩
      | lt => exact ⟨.inr .lt,rfl⟩
  | addZero => exact ⟨.inl .addZero,rfl⟩
  | addAssoc => exact ⟨.inl .addAssoc,rfl⟩
  | addComm => exact ⟨.inl .addComm,rfl⟩
  | addEqOfLt => exact ⟨.inl .addEqOfLt,rfl⟩
  | zeroLe => exact ⟨.inl .zeroLe,rfl⟩
  | zeroLtOne => exact ⟨.inl .zeroLtOne,rfl⟩
  | oneLeOfZeroLt => exact ⟨.inl .oneLeOfZeroLt,rfl⟩
  | addLtAdd => exact ⟨.inl .addLtAdd,rfl⟩
  | mulZero => exact ⟨.inl .mulZero,rfl⟩
  | mulOne => exact ⟨.inl .mulOne,rfl⟩
  | mulAssoc => exact ⟨.inl .mulAssoc,rfl⟩
  | mulComm => exact ⟨.inl .mulComm,rfl⟩
  | mulLtMul => exact ⟨.inl .mulLtMul,rfl⟩
  | distr => exact ⟨.inl .distr,rfl⟩
  | ltIrrefl => exact ⟨.inl .ltIrrefl,rfl⟩
  | ltTrans => exact ⟨.inl .ltTrans,rfl⟩
  | ltTri => exact ⟨.inl .ltTri,rfl⟩

theorem peanoMinus_iff_tag (p : V) :
    p ∈ PeanoMinus.Δ₁Class ↔ ∃ t : FiniteTag, p = (t.code : V) := by
  rw [peanoMinus_iff_sentence]
  constructor
  · rintro ⟨σ,hσ,hp⟩
    obtain ⟨t,rfl⟩ := finiteTag_exists hσ
    exact ⟨t,hp⟩
  · rintro ⟨t,hp⟩
    exact ⟨t.sentence,t.mem_base,hp⟩

theorem decodeFinite_iff (p : Nat) :
    (∃ t, decodeFinite p = some t) ↔ p ∈ PeanoMinus.Δ₁Class := by
  rw [peanoMinus_iff_tag]
  constructor
  · rintro ⟨t,ht⟩
    exact ⟨t, by simpa using (decodeFinite_sound ht).symm⟩
  · rintro ⟨t,rfl⟩
    simpa using decodeFinite_complete t

/-- Exhaustive exact axiom alternatives, with arbitrary model-valued input. -/
theorem axiom_iff_tag_or_witness (p : V) :
    p ∈ theory.Δ₁Class ↔
      (∃ t : FiniteTag, p = (t.code : V)) ∨
      ∃ m b k : V, V ⊧/![p,m,b,k] inductionWitnessGraph.val := by
  rw [Peano.mem_Δ₁Class_iff, peanoMinus_iff_tag,
    inductionWitnessGraph_exists_iff]

#print axioms ofList_iff
#print axioms peanoMinus_iff_sentence
#print axioms peanoMinus_iff_tag
#print axioms decodeFinite_iff
#print axioms axiom_iff_tag_or_witness
end M6.PA.FoundationAxiomCode

