import PA194SourceActualStepCalibration
import PA194FiniteControls
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SourceBoundedStep
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch PA194FiniteControls
open PA194SourceControllerCode PA194SourceRegisterRelation PA194SourceInstructionCalibration
open PA194SourceActualStepCalibration
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

/-- A model-valued PC bounded by 3673 is one of the standard table ordinals,
    so the resolved instruction semantics applies uniformly in every model. -/
theorem boundedStepCalibration (s : M) (regs : Fin 9 → M)
    (hpc : F pc ![s] < modelNumeral M 3673)
    (hregs : Encodes (pi₂ s) regs) :
    ∃ i : Fin 3673, F pc ![s] = modelNumeral M i.val ∧
      let inst := (M6.Source.PathTrie.nthSite PA194.SourceTree.trie i.val).bind
        (M6.FastResolve.resolveTree PA194.SourceTree.trie)
      pi₁ (F step ![s]) = modelNumeral M (execute inst regs).1 ∧
        Encodes (pi₂ (F step ![s])) (execute inst regs).2 := by
  obtain ⟨i,hi⟩ := modelBelowNumeral 3673 (F pc ![s]) hpc
  exact ⟨i,hi,actualStepCalibration i.val i.isLt s regs hi hregs⟩
#print axioms boundedStepCalibration
end models
end PA194SourceBoundedStep
