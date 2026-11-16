import ConPAMachineEndpoint
import ConPAISigma1Relative
import PA194NativeControllerCorrectness
import PA194NativeLiteralFinal

/-! Transfer a halting comparison with the primary source controller
at arbitrary model-valued clocks to standard iPRA. -/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace PA194ControllerNative
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open IPRAStandardTheory IPRAPA196Consistency
open ConPA.Machine ConPA.MachineEndpoint ConPA.ISigma1Models ConPA.ISigma1Transfer
open StrictSigmaOneInduction TableDispatch

/-- The halting comparison in the models used for the relative transfer. -/
def SameSourceHalt (T : Table) (halt : Nat) : Prop :=
  ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
    [M↓[language] ⊧* PRA],
    letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
    letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
    letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
    letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
    letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
    ∀ [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
      let F := Structure.func (L := language) (M := M)
      (∃ t : M, π₁ (ConPA.Machine.run T t) = (halt : M)) ↔
        ∃ n : M, F PA194SourceControllerCode.pc
          ![F PA194SourceControllerCode.run ![n, PA194CompressedStartup.initialSource]] =
            modelNumeral M 3674

theorem nonhalt_iff (T : Table) (halt : Nat) (compare : SameSourceHalt T halt) :
    standardTheory ⊢ ∼PA194ExplicitEndpoint.haltSentence 🡘 ∼machineHaltSentence T halt := by
  let H := (haltDef T halt).val
  have hH : Hierarchy 𝚺 1 H := haltDef_sigma_one _ _
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
  have hvariant : (M↓[language] ⊧ Semiformula.lMap embedding (∃⁰ bnd H)) ↔
      ∃ t : M, π₁ (ConPA.Machine.run T t) = (halt : M) :=
    models_iff.trans ((PRAWitnessTransfer.eval_lMap_std (∃⁰ bnd H) ![]).trans
      ((evalb_ex (bnd H)).trans ((StrictPiTwoBridge.eval_bnd_iff (M := M) hH).symm.trans
        (haltDef_iff (V := M) T halt))))
  exact (PA194NativeControllerCorrectness.endpoint (M := M)).trans
    ((compare M).symm.trans hvariant.symm)

theorem consistency_iff (T : Table) (halt : Nat) (compare : SameSourceHalt T halt) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence T halt := by
  have primary := Classical.choice PA194NativeLiteralFinal.consistency_iff_literal_nonhalt
  have variant := Classical.choice (nonhalt_iff T halt compare)
  exact ⟨K_intro (C_trans (K_left primary) (K_left variant)) (C_trans (K_right variant) (K_right primary))⟩

#print axioms nonhalt_iff
#print axioms consistency_iff
end PA194ControllerNative
