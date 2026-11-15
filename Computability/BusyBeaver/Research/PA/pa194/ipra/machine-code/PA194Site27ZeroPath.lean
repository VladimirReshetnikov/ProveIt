import PA194Site27ZeroTo24
import PA194Path31Header
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site27ZeroPath
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns
open BinaryTapeCodes PRAModelIOpenPairing PA194BinaryDouble PA194SourceSite25Physical PA194Site27ZeroRollback PA194Path27Header
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem zeroBranchWithFile (k : M) (e : Fin 11 → M) (hz : e 0 = (0 : M))
    (hf : returned e = F sourceFileCode e) :
    ∃ clock : M, F PA194Stepper.stepper ![clock,physicalFrame 27 ((k+1)+1) e] =
      physicalFrame 31 ((k+1)+1) e := by
  obtain ⟨r,c,hr,h⟩ := PA194Site27ZeroTo24.zeroTo24 k e hz
  refine ⟨c,?_⟩
  let z := F zeros ![k+1,(1 : M)+(r+r)+(r+r)]
  have hp := PA194Path31Header.path31Word z
  dsimp only at hp
  have hgap : F zeros ![(k+1)+1,(1 : M)+(F sourceFileCode e+F sourceFileCode e)] = z+z := by
    rw [←hf,hr]
    have harg : (1 : M)+((r+r)+(r+r)) = (1 : M)+(r+r)+(r+r) := by simp only [add_assoc]
    rw [harg]
    change F zeros ![F addCode ![k+1,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelZerosSucc]
  change F PA194Stepper.stepper ![c,physicalFrame 27 ((k+1)+1) e] =
    F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),modelWord (PA194SourceProgram.path 31)
      (F zeros ![(k+1)+1,(1 : M)+(F sourceFileCode e+F sourceFileCode e)])]]
  rw [hgap,hp]
  exact h
#print axioms zeroBranchWithFile
end models
end PA194Site27ZeroPath
