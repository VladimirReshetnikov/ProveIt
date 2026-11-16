import PA194FoldedChecks
import PA194FoldedCacheCorrect
import PA194HXAllocation
import PA194HXDispatch
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194HXContracts
open M6.Runtime M6.Source PA194SourceProgram PA194FoldedRuntimeRows
open PA194FoldedChecks PA194FoldedCache PA194FoldedCacheCorrect
open PA194CompressedRootContracts

/-- Symbolic native-control machine with precisely the two HX row changes. -/
def machine (q : Nat) (b : Bool) : Option (Bool × Bool × Nat) :=
  if q = 21 ∧ b = true then some (false,true,55)
  else if q = 45 ∧ b = true then some (false,true,60)
  else PA194FoldedRuntimeRows.machine q b

def cachedMachine (q : Nat) (b : Bool) : Option (Bool × Bool × Nat) :=
  if q = 21 ∧ b = true then some (false,true,55)
  else if q = 45 ∧ b = true then some (false,true,60)
  else PA194FoldedCache.cachedMachine q b

theorem cached_correct : cachedMachine = machine := by
  funext q b
  simp only [cachedMachine,machine,cachedMachine_correct]

/-- Logical register to HX's physical field, passed to the M6 runtime oracle. -/
def physicalRegister (r : Fin 9) : Nat := (PA194HXAllocation.hx r).val

theorem physicalRegister_values : (List.finRange 9).map physicalRegister = [6,2,0,4,3,8,7,5,1] := by decide +kernel

def cachedContract (br : Branch) (i j extra fuel : Nat) (e : Eff) : Bool :=
  (exec cachedMachine br (fun s => sMatches s
      (PA194RuntimeContracts.rootFrame (path j) extra e))
      fuel (PA194RuntimeContracts.rootFrame (path i)) false).isSome

def cachedHalt (i fuel : Nat) : Bool :=
  (exec cachedMachine none (fun s => s.1 == 254) fuel
    (PA194RuntimeContracts.rootFrame (path i)) false).isSome

def checkInstruction (i : Nat) : Instruction → Bool
  | .inc r next => decide (next.getD 0 < 3673) &&
    cachedContract none i (next.getD 0) 0 512 (.inc (physicalRegister r))
  | .dec r z p => decide (z.getD 0 < 3673 ∧ p.getD 0 < 3673) &&
    (cachedContract (some (physicalRegister r,true)) i (z.getD 0) 0 512 .none &&
    cachedContract (some (physicalRegister r,false)) i (p.getD 0) 1 512 (.dec (physicalRegister r)))
  | .jump next => decide (next.getD 0 < 3673) &&
    cachedContract none i (next.getD 0) 0 512 .none
  | .halt => cachedHalt i 512

def checkAt (i : Nat) : Bool := (PA194CheckCoverage.codeAt i).any (checkInstruction i)

#print axioms cached_correct
#print axioms physicalRegister_values
end PA194HXContracts
