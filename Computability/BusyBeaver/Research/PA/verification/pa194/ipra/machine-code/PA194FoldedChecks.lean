import PA194CompressedRootContracts
import PA194CheckCoverage
import PA194FoldedCache

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace PA194FoldedChecks
open M6.Runtime M6.Source PA194SourceProgram PA194FoldedRuntimeRows
open PA194CompressedRootContracts PA194FoldedCache

def haltContract (i fuel : Nat) : Bool :=
  (exec machine none (fun s => s.1 == 254) fuel
    (PA194RuntimeContracts.rootFrame (path i)) false).isSome

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

def blockCheck (base count : Nat) : Bool := (List.range count).all (fun j => checkAt (base+j))

theorem block_sound {base count i : Nat} (h : blockCheck base count = true)
    (lo : base ≤ i) (hi : i < base+count) : checkAt i = true := by
  have hh := List.all_eq_true.mp h (i-base) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le lo] using hh

theorem checked_at (i : Nat) (h : checkAt i = true) :
    ∃ code, M6.Source.resolveAt sites i = some code ∧ checkInstruction i code = true := by
  unfold checkAt at h
  cases hc : PA194CheckCoverage.codeAt i with
  | none => simp [hc] at h
  | some code =>
    refine ⟨code,?_,by simpa [hc] using h⟩
    rw [PA194SourceProgram.resolve_tree]
    exact hc

#print axioms checked_at

end PA194FoldedChecks
