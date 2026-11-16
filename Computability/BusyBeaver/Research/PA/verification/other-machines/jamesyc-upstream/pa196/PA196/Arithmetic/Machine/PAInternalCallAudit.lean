module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import PA196.Arithmetic.Machine.PANativeTable
public import PA196.RuntimeContracts
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace PA196.Arithmetic.Machine.InternalCallAudit
open M6.Runtime
/-- Audit only the box oracle calls visited before the original exec target test.
A true audit is not an execution theorem. Arithmetic model soundness is separate. -/
def localAllowed (allowed : Nat → BoxSt → Bool) (br : Branch) : SConf → Bool
  | (q,false,_,[.box x]) =>
      match oracle q br x with
      | none => true
      | some _ => allowed q x
  | _ => true

def check (allowed : Nat → BoxSt → Bool) (br : Branch) (tgt : SConf → Bool) :
    Nat → SConf → Bool → Bool
  | 0,_,_ => true
  | f+1,s,moved =>
      if moved && tgt s then true
      else match sstep PA196.Arithmetic.Machine.NativeTable.machine br s with
        | none => true
        | some (s',m) => localAllowed allowed br s && check allowed br tgt f s' (moved || m)

end PA196.Arithmetic.Machine.InternalCallAudit
