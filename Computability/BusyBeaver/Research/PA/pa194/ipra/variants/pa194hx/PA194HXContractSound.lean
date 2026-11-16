import PA194HXContracts
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194HXContractSound
open M6.Runtime M6.Source PA194SourceProgram PA194HXContracts

def contract (br : Branch) (i j extra fuel : Nat) (e : Eff) : Bool :=
  (exec machine br (fun s => sMatches s
      (PA194RuntimeContracts.rootFrame (path j) extra e))
      fuel (PA194RuntimeContracts.rootFrame (path i)) false).isSome

def haltContract (i fuel : Nat) : Bool :=
  (exec machine none (fun s => s.1 == 254) fuel
    (PA194RuntimeContracts.rootFrame (path i)) false).isSome

def Contracts (i : Nat) : Instruction → Prop
  | .inc r next => next.getD 0 < 3673 ∧
    contract none i (next.getD 0) 0 512 (.inc (PA194HXContracts.physicalRegister r)) = true
  | .dec r z p => z.getD 0 < 3673 ∧ p.getD 0 < 3673 ∧
    contract (some (PA194HXContracts.physicalRegister r,true)) i (z.getD 0) 0 512 .none = true ∧
    contract (some (PA194HXContracts.physicalRegister r,false)) i (p.getD 0) 1 512 (.dec (PA194HXContracts.physicalRegister r)) = true
  | .jump next => next.getD 0 < 3673 ∧
    contract none i (next.getD 0) 0 512 .none = true
  | .halt => haltContract i 512 = true

theorem cachedContractCorrect (br : Branch) (i j extra fuel : Nat) (e : Eff) :
    cachedContract br i j extra fuel e = contract br i j extra fuel e := by
  unfold cachedContract contract
  rw [cached_correct]

theorem cachedHaltCorrect (i fuel : Nat) : cachedHalt i fuel = haltContract i fuel := by
  unfold cachedHalt haltContract
  rw [cached_correct]

theorem instruction (i : Nat) (code : Instruction) (h : checkInstruction i code = true) :
    Contracts i code := by
  cases code <;> simpa only [checkInstruction,Contracts,cachedContractCorrect,
    cachedHaltCorrect,Bool.and_eq_true_iff,decide_eq_true_eq,and_assoc] using h

theorem atSite (i : Nat) (h : checkAt i = true) :
    ∃ code, resolveAt sites i = some code ∧ Contracts i code := by
  unfold checkAt at h
  cases hc : PA194CheckCoverage.codeAt i with
  | none => simp [hc] at h
  | some code =>
    refine ⟨code,?_,instruction i code (by simpa [hc] using h)⟩
    rw [PA194SourceProgram.resolve_tree]
    exact hc

#print axioms atSite
end PA194HXContractSound
