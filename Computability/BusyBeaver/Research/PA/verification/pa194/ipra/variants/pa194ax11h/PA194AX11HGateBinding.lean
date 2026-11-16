import PA194AX11HGateRows
import PA194AX11HSharedRows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194AX11HGateBinding
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194FiniteControls PA194AX11HGateRows PA194AX11HSharedRows

theorem gate_row (i : Fin 34) :
    PA194AX11HSource.program[3519+i.val]'(by rw [PA194AX11HSource.program_length]; have := i.isLt; omega) =
      ((M6.Source.PathTrie.nthSite PA194.SourceTree.trie (3519+i.val)).bind
        (M6.FastResolve.resolveTree PA194.SourceTree.trie)) := by
  have h := congrArg (fun xs => xs[i.val]?) same_gate_rows
  simpa [newGate,oldGate,i.isLt,PA194AX11HSource.program_length] using h

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem gate_step (i : Fin 34) (s : M) (hs : F pc ![s] = modelNumeral M (3519+i.val)) :
    F PA194AX11HSource.step ![s] = F PA194SourceControllerCode.step ![s] := by
  apply same_step_of_row (3519+i.val) (by have := i.isLt; omega) s hs
  exact gate_row i

#print axioms gate_row
#print axioms gate_step
end models
end PA194AX11HGateBinding
