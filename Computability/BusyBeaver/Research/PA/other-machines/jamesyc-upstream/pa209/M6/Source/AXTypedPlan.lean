module
public import M6.Source.AXMacroRead
@[expose] public section
namespace M6.Source.AXTyped
/-- Finite literal binding evidence, separate from external Nat semantics. -/
inductive Bound : AXMacro.Op → Nat → Nat → Prop
  | push (offset : Nat) (range : offset+44<3947)
      (rows : AXPushParam.Bound exactSites offset) : Bound .push (offset+25) (offset+44)
  | cons (offset : Nat) (range : offset+47<3947)
      (pop : UnpairPartial.Bound exactSites (offset+20))
      (pair : AXPair.Bound exactSites offset)
      (times : AXTimes4.Bound exactSites (offset+41)) : Bound .cons (offset+20) (offset+47)
  | copyA (base : Nat) (range : base+7<3947) (rows : CopyToT.Bound exactSites 3 base) : Bound .copyA base (base+7)
  | copyD (base : Nat) (range : base+7<3947) (rows : CopyToT.Bound exactSites 4 base) : Bound .copyD base (base+7)
  | copyH (base : Nat) (range : base+7<3947) (rows : CopyToT.Bound exactSites 5 base) : Bound .copyH base (base+7)
  | incT (base : Nat) (range : base+1<3947)
      (row : resolveAt exactSites base=some (.inc 1 (some (base+1)))) : Bound .incT base (base+1)
  | readH (base : Nat) (range : base+14<3947) (rows : (AXMacro.readerH base).Bound) : Bound .readH base (base+14)
  | readD (base : Nat) (range : base+14<3947) (rows : (AXMacro.readerD base).Bound) : Bound .readD base (base+14)

inductive Plan : Nat → Nat → List AXMacro.Op → Prop
  | nil (pc : Nat) : Plan pc pc []
  | cons {pc next last op ops} : Bound op pc next → Plan next last ops → Plan pc last (op::ops)
end M6.Source.AXTyped

