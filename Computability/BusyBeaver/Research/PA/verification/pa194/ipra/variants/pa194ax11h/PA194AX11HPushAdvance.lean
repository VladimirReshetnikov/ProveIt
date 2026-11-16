import PA194AX11HPushNext
import PA194SourcePCBound
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194AX11HPushAdvance
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194SourcePCBound PA194FiniteControls
open PA194AX11HSource PA194AX11HSourcePush PA194AX11HPushNext PA194AX11HRelocation
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

/-- Both source steps remain in their respective inserted-push intervals
    or reach the corresponding exits, with their register files still equal. -/
theorem advance (i : Fin 19) (old revised : M)
    (ho : F pc ![old] = modelNumeral M (3568+i.val))
    (hn : F pc ![revised] = modelNumeral M (3553+i.val))
    (hf : pi₂ old = pi₂ revised) :
    ∃ j : Fin 20,
      F pc ![F PA194SourceControllerCode.step ![old]] = modelNumeral M (3568+j.val) ∧
      F pc ![F PA194AX11HSource.step ![revised]] = modelNumeral M (3553+j.val) ∧
      pi₂ (F PA194SourceControllerCode.step ![old]) = pi₂ (F PA194AX11HSource.step ![revised]) := by
  have hi : 3553+i.val < 3671 := by have := i.isLt; omega
  obtain ⟨j,hj⟩ := next_index i revised
  have hnxt : pi₁ (F PA194AX11HSource.step ![revised]) = modelNumeral M (3553+j.val) := by
    rw [PA194AX11HSource.selected _ hi revised hn,block_record]
    exact hj
  have hr := full_step_matches i old revised ho hn hf
  refine ⟨j,?_,?_,hr.1⟩
  · rw [pcModel]
    have he := hr.2
    rw [hnxt, ←modelNumeralAdd] at he
    have eq : (3553+j.val)+15 = 3568+j.val := by omega
    simpa [eq] using he.symm
  · rw [pcModel,hnxt]

#print axioms advance
end models
end PA194AX11HPushAdvance
