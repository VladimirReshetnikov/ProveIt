import PA194AX11HSecondPushAdvance
import PA194SourceControllerBinding
import PA194SchedulerCode
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194AX11HSecondPushPaused
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194SourceControllerBinding PA194SourcePCBound PA194FiniteControls
open PA194SchedulerCode PA194AX11HSecondPushAdvance PA194StateOne
open Classical

/-- Freeze the primary and revised source codes at their respective push exits. -/
def oldPaused : Code 1 := choose0 (isOrdinal 3587) PA194SourceControllerCode.step (.proj 0)
def newPaused : Code 1 := choose0 (isOrdinal 3605) PA194AX11HSource.step (.proj 0)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem paused_model (exit : Nat) (step : Code 1) (s : M) :
    F (choose0 (isOrdinal exit) step (.proj 0)) ![s] =
      if F pc ![s] = modelNumeral M exit then s else F step ![s] := by
  rw [choose0_model]
  by_cases he : F pc ![s] = modelNumeral M exit
  · have hn := (ordinalTest exit s).mpr he
    simp only [hn,he,if_false,if_true,modelProjection,Matrix.cons_val_zero]
  · have hz : F (isOrdinal exit) ![s] = 0 := by
      by_contra hn
      exact he ((ordinalTest exit s).mp hn)
    simp only [hz,he,if_false,if_true]

theorem oldPaused_model (s : M) :
    F oldPaused ![s] = if F pc ![s] = modelNumeral M 3587 then s else F PA194SourceControllerCode.step ![s] :=
  paused_model 3587 PA194SourceControllerCode.step s

theorem newPaused_model (s : M) :
    F newPaused ![s] = if F pc ![s] = modelNumeral M 3605 then s else F PA194AX11HSource.step ![s] :=
  paused_model 3605 PA194AX11HSource.step s

/-- The common index ranges over the 19 live sites plus their single exit. -/
def aligned (old revised : M) : Prop :=
  ∃ k : M, k < modelNumeral M 20 ∧
    F pc ![old] = modelNumeral M 3568 + k ∧
    F pc ![revised] = modelNumeral M 3586 + k ∧ pi₂ old = pi₂ revised

theorem aligned_step (old revised : M) (ha : aligned old revised) :
    aligned (F oldPaused ![old]) (F newPaused ![revised]) := by
  obtain ⟨k,hk,ho,hn,hf⟩ := ha
  obtain ⟨i,hi⟩ := modelBelowNumeral 20 k hk
  subst k
  rw [←modelNumeralAdd] at ho hn
  by_cases he : i.val = 19
  · have hOld : F pc ![old] = modelNumeral M 3587 := by simpa [he] using ho
    have hNew : F pc ![revised] = modelNumeral M 3605 := by simpa [he] using hn
    rw [oldPaused_model,newPaused_model,if_pos hOld,if_pos hNew]
    refine ⟨modelNumeral M i.val,modelNumeralStrict i.val 20 i.isLt,?_,?_,hf⟩
    · rw [←modelNumeralAdd]; exact ho
    · rw [←modelNumeralAdd]; exact hn
  · have hi19 : i.val < 19 := by have := i.isLt; omega
    let j : Fin 19 := ⟨i.val,hi19⟩
    have hOld : F pc ![old] ≠ modelNumeral M 3587 := by
      rw [ho]
      exact ne_of_lt (modelNumeralStrict (3568+i.val) 3587 (by omega))
    have hNew : F pc ![revised] ≠ modelNumeral M 3605 := by
      rw [hn]
      exact ne_of_lt (modelNumeralStrict (3586+i.val) 3605 (by omega))
    rw [oldPaused_model,newPaused_model,if_neg hOld,if_neg hNew]
    obtain ⟨q,hqo,hqn,hqf⟩ := advance j old revised ho hn hf
    refine ⟨modelNumeral M q.val,modelNumeralStrict q.val 20 q.isLt,?_,?_,hqf⟩
    · simpa [modelNumeralAdd] using hqo
    · simpa [modelNumeralAdd] using hqn

#print axioms oldPaused_model
#print axioms newPaused_model
#print axioms aligned_step
end models
end PA194AX11HSecondPushPaused
