import PA194ORData
import PA194FoldedChecks
import ConPAMachineCompressedNormalization

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace PA194ORChecks
open M6.Runtime M6.Source PA194SourceProgram PA194CompressedRootContracts

def contract (br : Branch) (i j extra fuel : Nat) (e : Eff) : Bool :=
  (exec PA194ORData.machine br (fun s => sMatches s
      (PA194RuntimeContracts.rootFrame (PA194ORData.path j) extra e))
      fuel (PA194RuntimeContracts.rootFrame (PA194ORData.path i)) false).isSome

def haltContract (i fuel : Nat) : Bool :=
  (exec PA194ORData.machine none (fun s => s.1 == 254) fuel
    (PA194RuntimeContracts.rootFrame (PA194ORData.path i)) false).isSome

def checkInstruction (i : Nat) : Instruction → Bool
  | .inc r next => decide (next.getD 0 < 3673) &&
    contract none i (next.getD 0) 0 512 (.inc (physicalRegister r))
  | .dec r z p => decide (z.getD 0 < 3673 ∧ p.getD 0 < 3673) &&
    (contract (some (physicalRegister r,true)) i (z.getD 0) 0 512 .none &&
    contract (some (physicalRegister r,false)) i (p.getD 0) 1 512 (.dec (physicalRegister r)))
  | .jump next => decide (next.getD 0 < 3673) &&
    contract none i (next.getD 0) 0 512 .none
  | .halt => haltContract i 512

def checkAt (i : Nat) : Bool :=
  decide (PA194ORData.codeAt i = PA194CheckCoverage.codeAt i) &&
    (PA194ORData.codeAt i).any (checkInstruction i)

def blockCheck (base count : Nat) : Bool := (List.range count).all (fun j => checkAt (base + j))

theorem block_sound {base count i : Nat} (h : blockCheck base count = true)
    (lo : base ≤ i) (hi : i < base + count) : checkAt i = true := by
  have hh := List.all_eq_true.mp h (i - base) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le lo] using hh

theorem checked_at (i : Nat) (h : checkAt i = true) :
    ∃ code, M6.Source.resolveAt sites i = some code ∧ checkInstruction i code = true := by
  unfold checkAt at h
  have hAnd := h
  simp only [Bool.and_eq_true] at hAnd
  obtain ⟨agreement, checked⟩ := hAnd
  have same := of_decide_eq_true agreement
  rw [same] at checked
  cases hc : PA194CheckCoverage.codeAt i with
  | none => simp [hc] at checked
  | some code =>
    refine ⟨code, ?_, by simpa [hc] using checked⟩
    rw [PA194SourceProgram.resolve_tree]
    exact hc

#print axioms checked_at

end PA194ORChecks
