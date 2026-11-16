import PA194AX11HFieldNext
import PA194SourcePCBound
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194AX11HFieldAdvance
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194SourcePCBound PA194FiniteControls
open PA194AX11HSource PA194AX11HFieldSource PA194AX11HFieldNext PA194AX11HFieldSemantics
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

/-- One field step reaches another corresponding field site or both exits. -/
theorem advance (i : Fin 14) (old revised : M)
    (ho : F pc ![old] = modelNumeral M (3554+i.val))
    (hn : F pc ![revised] = modelNumeral M (3572+i.val))
    (hf : pi₂ old = pi₂ revised) :
    ∃ j : Fin 15,
      F pc ![F PA194SourceControllerCode.step ![old]] = modelNumeral M (3554+j.val) ∧
      F pc ![F PA194AX11HSource.step ![revised]] = modelNumeral M (3572+j.val) ∧
      pi₂ (F PA194SourceControllerCode.step ![old]) = pi₂ (F PA194AX11HSource.step ![revised]) := by
  have hi : 3572+i.val < 3671 := by have := i.isLt; omega
  obtain ⟨j,hj⟩ := next_index i revised
  have hnxt : pi₁ (F PA194AX11HSource.step ![revised]) = modelNumeral M (3572+j.val) := by
    rw [PA194AX11HSource.selected _ hi revised hn,candidateRows]
    exact hj
  have hr := field_step_matches i old revised ho hn hf
  refine ⟨j,?_,?_,hr.1⟩
  · rw [pcModel]
    apply add_right_cancel (b := modelNumeral M 18)
    calc
      pi₁ (F PA194SourceControllerCode.step ![old]) + modelNumeral M 18 =
          pi₁ (F PA194AX11HSource.step ![revised]) := hr.2
      _ = modelNumeral M (3572+j.val) := hnxt
      _ = modelNumeral M (3554+j.val) + modelNumeral M 18 := by
        rw [←modelNumeralAdd]
        congr 1
        omega
  · rw [pcModel,hnxt]

#print axioms advance
end models
end PA194AX11HFieldAdvance
