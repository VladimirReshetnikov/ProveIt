import PA194FoldedChecks
import PA194FoldedCacheCorrect
import PA194SourceControllerCode

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

namespace PA194FoldedSourceContracts
open M6.Runtime M6.Source PA194SourceProgram PA194FoldedRuntimeRows
open PA194FoldedChecks PA194FoldedCacheCorrect PA194CompressedRootContracts

abbrev dest := PA194SourceControllerCode.destination

def Contracts (i : Nat) : Instruction → Prop
  | .inc r next => dest next < 3673 ∧
    contract none i (dest next) 0 512 (.inc (physicalRegister r)) = true
  | .dec r z p => dest z < 3673 ∧ dest p < 3673 ∧
    contract (some (physicalRegister r,true)) i (dest z) 0 512 .none = true ∧
    contract (some (physicalRegister r,false)) i (dest p) 1 512 (.dec (physicalRegister r)) = true
  | .jump next => dest next < 3673 ∧
    contract none i (dest next) 0 512 .none = true
  | .halt => haltContract i 512 = true

theorem destination_eq (pc : Option Nat) : dest pc = pc.getD 0 := by cases pc <;> rfl

theorem cachedContractCorrect (br : Branch) (i j extra fuel : Nat) (e : Eff) :
    cachedContract br i j extra fuel e = contract br i j extra fuel e := by
  unfold cachedContract contract
  rw [cachedMachine_correct]

theorem cachedHaltCorrect (i fuel : Nat) : cachedHalt i fuel = haltContract i fuel := by
  unfold cachedHalt haltContract
  rw [cachedMachine_correct]

theorem instruction (i : Nat) (code : Instruction) (h : checkInstruction i code = true) :
    Contracts i code := by
  cases code <;> simpa only [checkInstruction,Contracts,destination_eq,cachedContractCorrect,
    cachedHaltCorrect,Bool.and_eq_true_iff,decide_eq_true_eq,and_assoc] using h

theorem atSite (i : Nat) (h : checkAt i = true) :
    ∃ code, resolveAt sites i = some code ∧ Contracts i code := by
  obtain ⟨code,hresolve,hcheck⟩ := checked_at i h
  exact ⟨code,hresolve,instruction i code hcheck⟩

#print axioms atSite
end PA194FoldedSourceContracts
