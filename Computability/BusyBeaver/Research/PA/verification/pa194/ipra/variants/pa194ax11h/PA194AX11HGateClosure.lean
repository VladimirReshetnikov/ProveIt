import PA194AX11HGateNext
import PA194AX11HGateBinding
import PA194SourcePCBound
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194AX11HGateClosure
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194SourcePCBound PA194FiniteControls
open PA194AX11HGateRows PA194AX11HGateData PA194AX11HGateNext PA194AX11HGateBinding

theorem candidate_row (i : Fin 34) :
    PA194AX11HSource.program[3519+i.val]'(by rw [PA194AX11HSource.program_length]; have := i.isLt; omega) =
      some (gateData.getD i.val .halt) := by
  have h := congrArg (fun xs => xs[i.val]?) data_correct
  have hi : i.val < gateData.length := by simpa [gateData] using i.isLt
  have hnew : newGate[i.val]? = some (PA194AX11HSource.program[3519+i.val]'(by rw [PA194AX11HSource.program_length]; have := i.isLt; omega)) := by
    simp [newGate,i.isLt,PA194AX11HSource.program_length]
  have hdata : getElem? (gateData.map some) i.val = some (some (gateData.getD i.val .halt)) := by
    simp [hi,List.getD_eq_getElem _ _ hi]
  rw [hnew,hdata] at h
  exact Option.some.inj h

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem gate_advance (i : Fin 34) (s : M) (hs : F pc ![s] = modelNumeral M (3519+i.val)) :
    ∃ j : Fin 35, F pc ![F PA194AX11HSource.step ![s]] = modelNumeral M (3519+j.val) := by
  obtain ⟨j,hj⟩ := next_index i s
  refine ⟨j,?_⟩
  rw [pcModel,PA194AX11HSource.selected _ (by have := i.isLt; omega) s hs,candidate_row]
  exact hj

#print axioms candidate_row
#print axioms gate_advance
end models
end PA194AX11HGateClosure
