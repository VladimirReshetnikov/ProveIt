module
public import PA196.Program
public import PA196.Source.Readers
@[expose] public section
namespace PA196.Arithmetic.Scheduler.AXTyped
open M6.Source
/-- Finite literal binding evidence, separate from external Nat semantics. -/
inductive Bound : AXMacro.Op → Nat → Nat → Prop
  | push (offset : Nat) (range : offset+44<3812)
      (rows : AXPushParam.Bound Program.sites offset) : Bound .push (offset+25) (offset+44)
  | cons (offset : Nat) (range : offset+47<3812)
      (pop : UnpairPartial.Bound Program.sites (offset+20))
      (pair : AXPair.Bound Program.sites offset)
      (times : AXTimes4.Bound Program.sites (offset+41)) : Bound .cons (offset+20) (offset+47)
  | copyA (base : Nat) (range : base+7<3812) (rows : CopyToT.Bound Program.sites 3 base) : Bound .copyA base (base+7)
  | copyD (base : Nat) (range : base+7<3812) (rows : CopyToT.Bound Program.sites 4 base) : Bound .copyD base (base+7)
  | copyH (base : Nat) (range : base+7<3812) (rows : CopyToT.Bound Program.sites 5 base) : Bound .copyH base (base+7)
  | incT (base : Nat) (range : base+1<3812)
      (row : resolveAt Program.sites base=some (.inc 1 (some (base+1)))) : Bound .incT base (base+1)
  | readH (base : Nat) (range : base+14<3812) (rows : PA196.Source.Readers.Bound Program.sites (AXMacro.readerH base)) : Bound .readH base (base+14)
  | readD (base : Nat) (range : base+14<3812) (rows : PA196.Source.Readers.Bound Program.sites (AXMacro.readerD base)) : Bound .readD base (base+14)

inductive Plan : Nat → Nat → List AXMacro.Op → Prop
  | nil (pc : Nat) : Plan pc pc []
  | cons {pc next last op ops} : Bound op pc next → Plan next last ops → Plan pc last (op::ops)
end PA196.Arithmetic.Scheduler.AXTyped

