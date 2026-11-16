import PA194SourceContracts
import PA194RegisterLayout

set_option autoImplicit false
set_option maxRecDepth 65536

namespace PA194RegisterContracts
open M6.Runtime M6.Source PA194SourceProgram
open PA194SourceContracts PA194RegisterLayout

abbrev pathAt := PA194SourceProgram.path

def physicalRegister (A : Allocation) (r : Fin 9) : Nat := (A.position r).val

def checkInstruction (A : Allocation) (machine : M6.Zip.TMN) (i : Nat) : Instruction → Bool
  | .inc r next => decide (next.getD 0 < 3673) &&
    contract machine pathAt none i (next.getD 0) 0 512 (.inc (physicalRegister A r))
  | .dec r z p => decide (z.getD 0 < 3673 ∧ p.getD 0 < 3673) &&
    (contract machine pathAt (some (physicalRegister A r,true)) i (z.getD 0) 0 512 .none &&
    contract machine pathAt (some (physicalRegister A r,false)) i (p.getD 0) 1 512 (.dec (physicalRegister A r)))
  | .jump next => decide (next.getD 0 < 3673) &&
    contract machine pathAt none i (next.getD 0) 0 512 .none
  | .halt => haltContract machine pathAt i 512

def checkAt (A : Allocation) (machine : M6.Zip.TMN) (i : Nat) : Bool :=
  (PA194CheckCoverage.codeAt i).any (checkInstruction A machine i)

def Contracts (A : Allocation) (machine : M6.Zip.TMN) (i : Nat) : Instruction → Prop
  | .inc r next => next.getD 0 < 3673 ∧
    contract machine pathAt none i (next.getD 0) 0 512 (.inc (physicalRegister A r)) = true
  | .dec r z p => z.getD 0 < 3673 ∧ p.getD 0 < 3673 ∧
    contract machine pathAt (some (physicalRegister A r,true)) i (z.getD 0) 0 512 .none = true ∧
    contract machine pathAt (some (physicalRegister A r,false)) i (p.getD 0) 1 512 (.dec (physicalRegister A r)) = true
  | .jump next => next.getD 0 < 3673 ∧
    contract machine pathAt none i (next.getD 0) 0 512 .none = true
  | .halt => haltContract machine pathAt i 512 = true

theorem atSite (A : Allocation) (machine : M6.Zip.TMN) (i : Nat) (h : checkAt A machine i = true) :
    ∃ code, resolveAt sites i = some code ∧ Contracts A machine i code := by
  unfold checkAt at h
  cases hc : PA194CheckCoverage.codeAt i with
  | none => simp [hc] at h
  | some code =>
    refine ⟨code, ?_, ?_⟩
    · rw [PA194SourceProgram.resolve_tree]
      exact hc
    · have h' : checkInstruction A machine i code = true := by simpa [hc] using h
      cases code <;> simpa only [checkInstruction,Contracts,Bool.and_eq_true_iff,
        decide_eq_true_eq,and_assoc] using h'

#print axioms atSite
end PA194RegisterContracts
