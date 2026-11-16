import PA194BModelSteps
import PAVariantFixedRow
import PA194HalfDiv
import Mathlib.Tactic.Ring

/-! The packed PRA step code and the arithmetic model step agree for every
dense 194-state transition table. -/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace PA194VariantPackedStep
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch PA194FiniteControls PA194HalfDiv
open PackedClock PackedIterationModel PackedRootModel PackedDecoderModel TableModelSemantics
open PA194BModelSteps
open PAVariantRowDispatch (Action)

def stepCode (values : List Action) : Code 1 :=
  bin pairCode (inject3 (PAVariantModelStep.nextQ 194 194 values))
    (bin pairCode (inject3 (PAVariantModelStep.nextL 194 values))
      (inject3 (PAVariantModelStep.nextR 194 values)))

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem rowStep_eq (action : Action) (l r : M) :
    let result := PAVariantFixedRow.rowStep action l r
    (⟪result.1,result.2.1,result.2.2⟫ : M) = PA194BModelSteps.next action l r := by
  have addEval (x y : M) : F addCode ![x,y] = x+y := rfl
  have zeroEval : F (Code.zero 0) Fin.elim0 = (0 : M) := rfl
  change _ = _
  simp only [PAVariantFixedRow.rowStep, PA194BModelSteps.next, PA194BModelSteps.config,
    modelNumeralCast, modelHalfDiv, modelParityMod, addEval, zeroEval]
  by_cases hd : action.2.1 = 0
  · simp only [hd, Nat.cast_zero, if_true]
    have he : l % 2 + ((action.1 : M) + (action.1 : M) +
        (r / 2 + r / 2 + (r / 2 + r / 2))) = 4 * (r / 2) + 2 * (action.1 : M) + l % 2 := by ring
    rw [he]
  · have hd' : (action.2.1 : M) ≠ 0 := by exact_mod_cast hd
    simp only [hd, hd', if_false, two_mul]

private theorem inactive (values : List Action) (hlen : values.length = 388) (c : M)
    (hq : (194 : M) ≤ π₁ c) : ConPA.Machine.step (table values) c = c := by
  classical
  rw [PA194GenericBridge.stepFind]
  have hn : (table values).find? (fun row => decide
      (π₁ c = (row.q : M) ∧ π₂ (π₂ c) % 2 = (row.b : M))) = none := by
    apply List.find?_eq_none.mpr
    intro row hr
    simp only [table, List.mem_map, List.mem_range] at hr
    obtain ⟨i, hi, rfl⟩ := hr
    have hlt : i / 2 < 194 := by omega
    have hlt' : ((i / 2 : Nat) : M) < 194 := by exact_mod_cast hlt
    have hne : π₁ c ≠ ((i / 2 : Nat) : M) := fun he => (not_le_of_gt hlt') (he ▸ hq)
    simp [indexedRow, hne]
  rw [hn]

/-- Agreement at arbitrary model configurations, including controls or tape
halves that are not standard natural numerals. -/
theorem modelStep (values : List Action) (hlen : values.length = 388) (c : M) :
    F (stepCode values) (fun _ => c) = ConPA.Machine.step (table values) c := by
  let q := π₁ c
  let l := π₁ (π₂ c)
  let r := π₂ (π₂ c)
  have hc : c = (⟪q,l,r⟫ : M) := by simp [q,l,r,pair_unpair]
  simp only [stepCode, modelBin, modelInject, packedQ, packedL, packedR,
    modelUnary, modelDecodeLeft, modelDecodeRight, modelPairCode]
  change (⟪F (PAVariantModelStep.nextQ 194 194 values) ![q,l,r],
      F (PAVariantModelStep.nextL 194 values) ![q,l,r],
      F (PAVariantModelStep.nextR 194 values) ![q,l,r]⟫ : M) = _
  by_cases hq : q < modelNumeral M 194
  · obtain ⟨i, hi⟩ := modelBelowNumeral 194 q hq
    obtain ⟨b, hb⟩ := modelParityNumeral r
    have hi' : q = (i.val : M) := by simpa only [modelNumeralCast] using hi
    have hb' : r % 2 = (b.val : M) := by simpa only [modelParityMod, modelNumeralCast] using hb
    let action := values.getD (2*i.val+b.val) (0,0,194)
    have hrow := PAVariantFixedRow.modelFixedRow 194 194 values i.val b.val l r (hi ▸ hq) hb
    have hpacked := congrArg (fun z : M × M × M => (⟪z.1,z.2.1,z.2.2⟫ : M)) hrow
    change _ = (⟪(PAVariantFixedRow.rowStep action l r).1,
        (PAVariantFixedRow.rowStep action l r).2.1,(PAVariantFixedRow.rowStep action l r).2.2⟫ : M) at hpacked
    have hs := PA194BModelSteps.stepRow values i.val b.val l r b.isLt
      (by have hx := i.isLt; have hy := b.isLt; omega) hb'
    rw [hi, hpacked, rowStep_eq]
    exact (show ConPA.Machine.step (table values) c = PA194BModelSteps.next action l r by
      rw [hc, hi']
      exact hs).symm
  · have hq' : (194 : M) ≤ π₁ c := by simpa [q, modelNumeralCast] using le_of_not_gt hq
    have hz : F ltBitCode ![q,modelNumeral M 194] = F (Code.zero 0) Fin.elim0 :=
      (modelLtZero q (modelNumeral M 194)).mpr hq
    have hstep := PAVariantModelStep.modelNext 194 194 values (![q,l,r] : Fin 3 → M)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      PAVariantModelStep.stepSem, hz, if_true] at hstep
    have hpacked := congrArg (fun z : M × M × M => (⟪z.1,z.2.1,z.2.2⟫ : M)) hstep
    rw [hpacked, inactive values hlen c hq']
    exact hc.symm

#print axioms modelStep
end models
end PA194VariantPackedStep
