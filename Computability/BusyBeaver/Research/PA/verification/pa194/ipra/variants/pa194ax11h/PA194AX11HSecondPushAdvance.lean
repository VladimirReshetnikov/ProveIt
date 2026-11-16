import PA194AX11HSecondPushRows
import PA194AX11HPushNext
import PA194SourcePCBound
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194AX11HSecondPushAdvance
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194SourcePCBound PA194FiniteControls
open PA194SourceInstructionModel PA194AX11HPushRows PA194AX11HPrimaryPush
open PA194AX11HSecondPushRows PA194AX11HPushNext PA194AX11HRelocation
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

/-- Repositioning this instruction block preserves the entire register file
and adds 33 to the resulting control index. -/
theorem shifted_sem (i : Fin 19) (s : M) :
    pi₂ (instructionSem (some (shift 33 (newPush.getD i.val .halt))) s) =
      pi₂ (instructionSem (some (newPush.getD i.val .halt)) s) ∧
    pi₁ (instructionSem (some (shift 33 (newPush.getD i.val .halt))) s) =
      pi₁ (instructionSem (some (newPush.getD i.val .halt)) s) + modelNumeral M 33 := by
  fin_cases i <;> simp [newPush,shift,instructionSem,destination]
  all_goals try split
  all_goals try simp only [pi₁_pair,pi₂_pair,true_and]
  all_goals rw [←modelNumeralAdd (M := M)]

/-- The primary push and the candidate's second push make matching file
updates and remain within their respective 19-site blocks or reach exits. -/
theorem advance (i : Fin 19) (old revised : M)
    (ho : F pc ![old] = modelNumeral M (3568+i.val))
    (hn : F pc ![revised] = modelNumeral M (3586+i.val))
    (hf : pi₂ old = pi₂ revised) :
    ∃ j : Fin 20,
      F pc ![F PA194SourceControllerCode.step ![old]] = modelNumeral M (3568+j.val) ∧
      F pc ![F PA194AX11HSource.step ![revised]] = modelNumeral M (3586+j.val) ∧
      pi₂ (F PA194SourceControllerCode.step ![old]) = pi₂ (F PA194AX11HSource.step ![revised]) := by
  have hi : 3586+i.val < 3671 := by have := i.isLt; omega
  obtain ⟨j,hj⟩ := next_index i revised
  have hs := shifted_sem i revised
  have hr := primaryStep_matches i old revised ho hf
  have hc : F PA194AX11HSource.step ![revised] =
      instructionSem (some (shift 33 (newPush.getD i.val .halt))) revised := by
    rw [PA194AX11HSource.selected _ hi revised hn,second_push_record]
  refine ⟨j,?_,?_,?_⟩
  · rw [pcModel]
    have h := hr.2
    rw [hj,←modelNumeralAdd] at h
    have eq : (3553+j.val)+15 = 3568+j.val := by omega
    simpa [eq] using h.symm
  · rw [pcModel,hc,hs.2,hj,←modelNumeralAdd]
    have eq : (3553+j.val)+33 = 3586+j.val := by omega
    rw [eq]
  · rw [hc,hs.1]
    exact hr.1

#print axioms shifted_sem
#print axioms advance
end models
end PA194AX11HSecondPushAdvance
