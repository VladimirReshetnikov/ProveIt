import ConPAISigma1Relative
import ConPAMachineEndpoint

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace ConPA.MachineRelative
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open IPRAStandardTheory IPRAPA196Consistency
open ConPA.Machine ConPA.MachineEndpoint ConPA.ISigma1Models ConPA.ISigma1Transfer
open StrictSigmaOneInduction

/-- Compare the blank runs at model-valued clocks in arithmetic models of IΣ₁. -/
def SameHalt (T U : Table) (a b : Nat) : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    (∃ t : V, π₁ (run T t) = (a : V)) ↔ ∃ t : V, π₁ (run U t) = (b : V)

theorem nonhalt_iff (T U : Table) (a b : Nat) (compare : SameHalt T U a b) :
    standardTheory ⊢ ∼machineHaltSentence T a 🡘 ∼machineHaltSentence U b := by
  apply ConPA.Relative.bounded_nonhalt_iff (bnd (haltDef T a).val) (bnd (haltDef U b).val)
    (hierarchy_bnd (haltDef_sigma_one T a) (by decide) (by intro _; rfl))
    (hierarchy_bnd (haltDef_sigma_one U b) (by decide) (by intro _; rfl))
  intro M _ _ _ _ reduct
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := standard_isigma1 reduct
  have modelsHalt (table : Table) (halt : Nat) :
      (M↓[language] ⊧ Semiformula.lMap embedding (∃⁰ bnd (haltDef table halt).val)) ↔
        ∃ t : M, π₁ (run table t) = (halt : M) := by
    let H := (haltDef table halt).val
    have hH : Hierarchy 𝚺 1 H := haltDef_sigma_one table halt
    exact models_iff.trans ((PRAWitnessTransfer.eval_lMap_std (∃⁰ bnd H) ![]).trans
      ((evalb_ex (bnd H)).trans ((StrictPiTwoBridge.eval_bnd_iff (M := M) hH).symm.trans
        (haltDef_iff (V := M) table halt))))
  exact (modelsHalt T a).trans ((compare M).trans (modelsHalt U b).symm)

/-- Reuse an existing iPRA equivalence for a table with the same model halting behavior. -/
theorem consistency_iff (T U : Table) (a b : Nat)
    (prior : standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence T a)
    (compare : SameHalt T U a b) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence U b := by
  have source := Classical.choice prior
  have equivalence := Classical.choice (nonhalt_iff T U a b compare)
  exact ⟨K_intro (C_trans (K_left source) (K_left equivalence))
    (C_trans (K_right equivalence) (K_right source))⟩

#print axioms nonhalt_iff
#print axioms consistency_iff
end ConPA.MachineRelative
