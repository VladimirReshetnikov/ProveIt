import PA194SourceSite32ZeroPhysical
import PA194SourceSite32PositivePhysical
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SourceSite32BothPhysical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194SourceControllerCode PA194SourceSite31Controller PA194SourceSite31Physical PRAModelIOpenPairing PRAExhaustion
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem bothBranches (k tail : M) (args : Fin 11 → M) :
    (args 6 = (0 : M) ∧ F step ![sourceState 32 args tail] = sourceState 34 args tail ∧
      ∃ clock : M, F PA194Stepper.stepper ![clock,physicalFrame 32 ((k+1)+1) args] =
        physicalFrame 34 (((k+1)+1)+1) args) ∨
    (∃ m : M, args 6 = m+1 ∧ F step ![sourceState 32 args tail] = sourceState 33 (Function.update args 6 m) tail ∧
      ∃ clock : M, F PA194Stepper.stepper ![clock,physicalFrame 32 ((k+1)+1) args] =
        physicalFrame 33 (((k+1)+1)+1) (Function.update args 6 m)) := by
  classical
  by_cases hz : args 6 = (0 : M)
  · exact Or.inl ⟨hz,PA194SourceSite32ZeroPhysical.zeroBranch k tail args hz⟩
  · let m := F predCode (fun _ => args 6)
    have hs : F Code.succ (fun _ => m) = args 6 := (modelZeroOrSuccPred (args 6)).resolve_left hz
    have hm : args 6 = m+1 := hs.symm.trans (modelAddOne m).symm
    exact Or.inr ⟨m,hm,PA194SourceSite32PositivePhysical.positiveBranch k tail m args hm⟩
#print axioms bothBranches
end models
end PA194SourceSite32BothPhysical
