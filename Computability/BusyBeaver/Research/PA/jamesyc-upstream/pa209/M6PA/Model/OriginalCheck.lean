module
public import M6.CheckCoverage
public import M6.Legacy213.FastCodes
@[expose] public section
namespace M6.Arithmetic.OriginalCheck
open M6.Source M6.Runtime M6.RuntimeContracts
/-- Retained A,B,C,D,E,F,G source ordinal mapped into physical F,G,A,B,C,D,E,return.
E's physical contract includes its increment and the extra final Continue. -/
def lift (i : Nat) : Nat := if i < 3922 then i+25 else i-3922
def path (i : Nat) : Path := M6.Program.path (lift i)
/-- Uniform width38 contract; the actual width48 startup has gap10. -/
def frame (p : Path) (extra : Nat := 0) (e : Eff := .none) : SConf :=
  M6.RuntimeContracts.rootFrame p extra e
def codeAt := M6.Legacy213.FastCodes.code

def checkInstruction (i : Nat) : Instruction → Bool
  | .inc r next => decide (next.getD 0 < 3947) &&
    check 1024 ⟨none,frame (path i),frame (path (next.getD 0)) 0 (.inc (physicalRegister r))⟩
  | .dec r z p => decide (z.getD 0 < 3947 ∧ p.getD 0 < 3947) &&
    (check 1024 ⟨some (physicalRegister r,true),frame (path i),frame (path (z.getD 0)) 0 .none⟩ &&
     check 1024 ⟨some (physicalRegister r,false),frame (path i),frame (path (p.getD 0)) 1 (.dec (physicalRegister r))⟩)
  | .jump next => decide (next.getD 0 < 3947) &&
    check 1024 ⟨none,frame (path i),frame (path (next.getD 0)) 0 .none⟩
  | .halt => haltCheck 1024 none (frame (path i))

def checkAt (i : Nat) : Bool := (codeAt i).any (checkInstruction i)
def blockCheck (base count : Nat) : Bool :=
  (List.range count).all (fun j => checkAt (base+j))

theorem block_sound {base count i : Nat} (h : blockCheck base count = true)
    (lo : base ≤ i) (hi : i < base+count) : checkAt i = true := by
  have hh := List.all_eq_true.mp h (i-base) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le lo] using hh
end M6.Arithmetic.OriginalCheck
