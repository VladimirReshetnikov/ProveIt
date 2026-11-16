import ConPAISigma1Directions
import PA194GenericHalt
set_option autoImplicit false
noncomputable section
namespace PA194OneWayEndpoint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory IPRAStandardTheory IPRAPA196Consistency
open IPRANativeFormula ConPA.ISigma1Models ConPA.MachineEndpoint
open LO.FirstOrder.Arithmetic.Bootstrapping
open PRAAddOne PRAHistoryPairCode PA194GenericBridge

theorem nonhalt_implies_consistency
    (h : ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
      [M↓[language] ⊧* PRA], ReductISigma1 M →
        (M↓[language] ⊧ mappedPARefutation) → (M↓[language] ⊧ PA194ExplicitEndpoint.haltClassical)) :
    standardTheory ⊢ ∼PA194ExplicitEndpoint.haltSentence 🡒 nativePAConsistency := by
  apply ConPA.Directions.ipra_nonhalt_implies_consistency PA194ExplicitEndpoint.haltMatrix
  · simp [PA194ExplicitEndpoint.haltMatrix, Semiformula.Open]
  · exact PA194ExplicitEndpoint.haltMatrix_bounded
  · exact h

theorem consistency_implies_nonhalt
    (h : ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
      [M↓[language] ⊧* PRA], ReductISigma1 M →
        (M↓[language] ⊧ PA194ExplicitEndpoint.haltClassical) → (M↓[language] ⊧ mappedPARefutation)) :
    standardTheory ⊢ nativePAConsistency 🡒 ∼PA194ExplicitEndpoint.haltSentence := by
  apply ConPA.Directions.ipra_consistency_implies_nonhalt PA194ExplicitEndpoint.haltMatrix
  · simp [PA194ExplicitEndpoint.haltMatrix, Semiformula.Open]
  · exact h
/-- Every IΣ₁ model converts an internal PA refutation to a halting time. -/
def RefutationToHalt : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    Provable (𝗣𝗔 : ArithmeticTheory) (⌜(⊥ : ArithmeticSentence)⌝ : V) →
      ∃ t : V, π₁ (ConPA.Machine.run denseTable t) = (194 : V)

/-- Every IΣ₁ model converts a halting time to an internal PA refutation. -/
def HaltToRefutation : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    (∃ t : V, π₁ (ConPA.Machine.run denseTable t) = (194 : V)) →
      Provable (𝗣𝗔 : ArithmeticTheory) (⌜(⊥ : ArithmeticSentence)⌝ : V)

theorem generic_nonhalt_implies_consistency (h : RefutationToHalt) :
    standardTheory ⊢ ∼PA194ExplicitEndpoint.haltSentence 🡒 nativePAConsistency := by
  apply nonhalt_implies_consistency
  intro M _ _ _ _ hM
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := standard_isigma1 hM
  have hh := PA194GenericHalt.sentenceBridge (M := M)
  rw [ConPA.Machine.haltDef_iff] at hh
  have hp : (M↓[language] ⊧ mappedPARefutation) ↔
      Provable (𝗣𝗔 : ArithmeticTheory) (⌜(⊥ : ArithmeticSentence)⌝ : M) := by
    rw [models_iff, PA195RefutationBridge.mapped_refutation_iff]
    rfl
  exact fun hr => hh.mpr (h M (hp.mp hr))

theorem generic_consistency_implies_nonhalt (h : HaltToRefutation) :
    standardTheory ⊢ nativePAConsistency 🡒 ∼PA194ExplicitEndpoint.haltSentence := by
  apply consistency_implies_nonhalt
  intro M _ _ _ _ hM
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := standard_isigma1 hM
  have hh := PA194GenericHalt.sentenceBridge (M := M)
  rw [ConPA.Machine.haltDef_iff] at hh
  have hp : (M↓[language] ⊧ mappedPARefutation) ↔
      Provable (𝗣𝗔 : ArithmeticTheory) (⌜(⊥ : ArithmeticSentence)⌝ : M) := by
    rw [models_iff, PA195RefutationBridge.mapped_refutation_iff]
    rfl
  exact fun hr => hp.mpr (h M (hh.mp hr))

#print axioms generic_nonhalt_implies_consistency
#print axioms generic_consistency_implies_nonhalt
#print axioms nonhalt_implies_consistency
#print axioms consistency_implies_nonhalt
end PA194OneWayEndpoint
