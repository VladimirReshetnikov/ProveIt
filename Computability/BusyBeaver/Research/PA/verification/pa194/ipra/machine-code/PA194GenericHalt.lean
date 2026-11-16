import PA194GenericBridge
import PA194Reachable
import PA194UnaryRecursionGraph
import PA194ExplicitEndpoint
import ConPAUnconditional
import PA195RefutationBridge
set_option autoImplicit false
set_option maxRecDepth 10000
/-! All-model bridge from the PA194 packed clock and halt sentence to the
generic arithmetic machine, with a conditional iPRA endpoint. The sole
machine hypothesis of the endpoint is the still-open all-model calibration. -/
namespace PA194GenericHalt
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194GenericBridge PA194Reachable PackedClock
section model
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem clockRun [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (t : M) :
    F clock (fun _ => t) = ConPA.Machine.run denseTable t := by
  have hz : (ConPA.Machine.blueprint denseTable).zero.val.Evalb (M := M) ![F (Code.zero 0) Fin.elim0] := by
    simp [ConPA.Machine.blueprint]
    rfl
  have hs (i z : M) : (ConPA.Machine.blueprint denseTable).succ.val.Evalb (M := M) ![F clockStep ![i,z],z,i] := by
    have hv : F clockStep ![i,z] = F encodedStep (fun _ => z) := by
      simp [clockStep, PackedRootModel.modelUnary, modelProjection]
    rw [hv, pointwise]
    simp [ConPA.Machine.blueprint, ConPA.Machine.stepDef_iff]
  have hh := PA194UnaryRecursionGraph.modelResult_eq (M := M) (ConPA.Machine.blueprint denseTable)
    (ConPA.Machine.construction denseTable) (Code.zero 0) clockStep hz hs t
  have he : (Fin.elim0 : Fin 0 → M) = ![] := Subsingleton.elim _ _
  simpa only [PRAHistoryIterator.valueCode, clock, ConPA.Machine.run, he] using hh
#print axioms clockRun

theorem haltBridge [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (hrun : ∀ t : M, F clock (fun _ => t) = ConPA.Machine.run denseTable t) :
    (∃ t : M, F haltIndicator (fun _ => t) = (1 : M)) ↔
      (ConPA.Machine.haltDef denseTable 194).val.Evalb (M := M) ![] := by
  rw [ConPA.Machine.haltDef_iff]
  constructor
  · rintro ⟨t,ht⟩
    refine ⟨t, ?_⟩
    have ht' := (haltIndicatorIffState t).mp ht
    rwa [hrun] at ht'
  · rintro ⟨t,ht⟩
    refine ⟨t, (haltIndicatorIffState t).mpr ?_⟩
    rwa [hrun]
/-- The packed indicator and the generic arithmetic halt sentence agree in
all candidate PRA models with an IΣ₁ reduct, including at nonstandard clocks. -/
theorem haltEquiv [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    (∃ t : M, F haltIndicator (fun _ => t) = (1 : M)) ↔
      (ConPA.Machine.haltDef denseTable 194).val.Evalb (M := M) ![] :=
  haltBridge (fun t => clockRun t)
theorem sentenceBridge [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    (M↓[language] ⊧ PA194ExplicitEndpoint.haltClassical) ↔
      (ConPA.Machine.haltDef denseTable 194).val.Evalb (M := M) ![] := by
  rw [models_iff]
  simpa only [PA194ExplicitEndpoint.haltClassical, Semiformula.eval_ex,
    PA194ExplicitEndpoint.haltMatrix_eval] using (haltEquiv (M := M))
#print axioms sentenceBridge
#print axioms haltEquiv
#print axioms haltBridge
end model
open LO.Entailment LO.FirstOrder.Arithmetic.Bootstrapping
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.ISigma1Models ConPA.MachineEndpoint
/-- Assuming all-model calibration of the pinned table, standard iPRA proves
Con(PA) iff the existing PA194 halt sentence is false. -/
theorem endpoint (hc : Calibrated denseTable 194) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼PA194ExplicitEndpoint.haltSentence := by
  apply ConPA.Unconditional.ipra_of_models PA194ExplicitEndpoint.haltMatrix
  · simp [PA194ExplicitEndpoint.haltMatrix, Semiformula.Open]
  · exact PA194ExplicitEndpoint.haltMatrix_bounded
  · intro M _ _ _ _ hM
    letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
    letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
    letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
    letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
    letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := standard_isigma1 hM
    have hh := sentenceBridge (M := M)
    rw [ConPA.Machine.haltDef_iff] at hh
    have hp : (M↓[language] ⊧ mappedPARefutation) ↔
        Provable (𝗣𝗔 : ArithmeticTheory) (⌜(⊥ : ArithmeticSentence)⌝ : M) := by
      rw [models_iff, PA195RefutationBridge.mapped_refutation_iff]
      rfl
    exact hh.trans ((hc M).symm.trans hp.symm)
#print axioms endpoint
end PA194GenericHalt
