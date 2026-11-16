import PA194HXAllocation
import PA194SourceSite31Physical
set_option autoImplicit false
namespace PA194HXFrame
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194UnaryRuns PA194ZeroRuns BinaryTapeCodes PRAModelIOpenPairing
open TableDispatch PA194Path27Header

theorem swapLogical_eq_self {α : Type} (e : Fin 11 → α) (h : e 5 = e 6) :
    PA194HXAllocation.swapLogical e = e := by
  funext i
  fin_cases i <;> simp [PA194HXAllocation.swapLogical, h]

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

noncomputable def frame (q : Nat) (gap : M) (args : Fin 11 → M) : M :=
  let f := F PA194HXAllocation.sourceFileCode args
  F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),
    modelWord (PA194SourceProgram.path q) (F zeros ![gap,(1 : M)+(f+f)])]]

theorem frame_eq (q : Nat) (gap : M) (args : Fin 11 → M) :
    frame q gap args = PA194SourceSite31Physical.physicalFrame q gap (PA194HXAllocation.swapLogical args) := by
  simp only [frame, PA194SourceSite31Physical.physicalFrame, PA194HXAllocation.modelSourceFile_swap]

theorem sameFrame_of_equal_HX (q : Nat) (gap : M) (args : Fin 11 → M)
    (h : args 5 = args 6) :
    frame q gap args = PA194SourceSite31Physical.physicalFrame q gap args := by
  rw [frame_eq, swapLogical_eq_self args h]

#print axioms frame_eq
#print axioms sameFrame_of_equal_HX
end models
end PA194HXFrame
