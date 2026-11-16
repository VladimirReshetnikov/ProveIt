import ConPAMachineEndpoint
import ConPAISigma1Relative
import PA194GenericHalt
import PA194NativeLiteralFinal

/-! A comparison with the primary literal PA194 run supplies an iPRA
consistency equivalence for a companion transition table. -/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace PA194VariantNative
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open IPRAStandardTheory IPRAPA196Consistency
open ConPA.Machine ConPA.MachineEndpoint ConPA.ISigma1Models ConPA.ISigma1Transfer
open StrictSigmaOneInduction

/-- A comparison of the blank runs at clocks in arbitrary models of `IΣ₁`. -/
def SameHalt (T : Table) (h : Nat) : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    (∃ t : V, π₁ (run PA194GenericBridge.denseTable t) = (194 : V)) ↔
      ∃ t : V, π₁ (run T t) = (h : V)

theorem nonhalt_iff (T : Table) (h : Nat) (hcompare : SameHalt T h) :
    standardTheory ⊢ ∼PA194ExplicitEndpoint.haltSentence 🡘 ∼machineHaltSentence T h := by
  let H := (haltDef T h).val
  have hH : Hierarchy 𝚺 1 H := haltDef_sigma_one T h
  apply ConPA.Relative.nonhalt_iff PA194ExplicitEndpoint.haltMatrix
    (by simp [PA194ExplicitEndpoint.haltMatrix, Semiformula.Open])
    PA194ExplicitEndpoint.haltMatrix_bounded (bnd H)
      (hierarchy_bnd hH (by decide) (by intro _; rfl))
  intro M _ _ _ _ hr
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := standard_isigma1 hr
  have hprimary := (PA194GenericHalt.sentenceBridge (M := M)).trans
    (haltDef_iff (V := M) PA194GenericBridge.denseTable 194)
  have hvariant : (M↓[language] ⊧ Semiformula.lMap embedding (∃⁰ bnd H)) ↔
      ∃ t : M, π₁ (run T t) = (h : M) :=
    models_iff.trans ((PRAWitnessTransfer.eval_lMap_std (∃⁰ bnd H) ![]).trans
      ((evalb_ex (bnd H)).trans ((StrictPiTwoBridge.eval_bnd_iff (M := M) hH).symm.trans
        (haltDef_iff (V := M) T h))))
  exact hprimary.trans ((hcompare M).trans hvariant.symm)

theorem consistency_iff_nonhalt (T : Table) (h : Nat) (hcompare : SameHalt T h) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence T h := by
  have hp := Classical.choice PA194NativeLiteralFinal.consistency_iff_literal_nonhalt
  have hv := Classical.choice (nonhalt_iff T h hcompare)
  exact ⟨K_intro (C_trans (K_left hp) (K_left hv)) (C_trans (K_right hv) (K_right hp))⟩

#print axioms nonhalt_iff
#print axioms consistency_iff_nonhalt
end PA194VariantNative
