module
public import M6.Source.AXBindings.B009
import all M6.Source.AXBindings.B009
public import M6.Source.AXTypedPlan
public import M6.Source.ExistingPrivateBound
@[expose] public section
namespace M6.Source.AXModelBounds
theorem bound1485_c : CopyToT.Bound exactSites 4 1485 :=
  existingPrivateBound% "M6.Source.AXBindings.B009" "M6.Source.AXAll.bound1485_c"
theorem bound1492_p : AXPushParam.Bound exactSites 1467 :=
  existingPrivateBound% "M6.Source.AXBindings.B009" "M6.Source.AXAll.bound1492_p"
theorem bound1511_c : CopyToT.Bound exactSites 5 1511 :=
  existingPrivateBound% "M6.Source.AXBindings.B009" "M6.Source.AXAll.bound1511_c"
theorem bound1518_p : AXPushParam.Bound exactSites 1493 :=
  existingPrivateBound% "M6.Source.AXBindings.B009" "M6.Source.AXAll.bound1518_p"
theorem bound1537_c : CopyToT.Bound exactSites 3 1537 :=
  existingPrivateBound% "M6.Source.AXBindings.B009" "M6.Source.AXAll.bound1537_c"
theorem bound1544_u : UnpairPartial.Bound exactSites 1544 :=
  existingPrivateBound% "M6.Source.AXBindings.B009" "M6.Source.AXAll.bound1544_u"
theorem bound1544_q : AXPair.Bound exactSites 1524 :=
  existingPrivateBound% "M6.Source.AXBindings.B009" "M6.Source.AXAll.bound1544_q"
theorem bound1544_m : AXTimes4.Bound exactSites 1565 :=
  existingPrivateBound% "M6.Source.AXBindings.B009" "M6.Source.AXAll.bound1544_m"
theorem row1571_i0 : resolveAt exactSites 1571 = some (Instruction.inc 1 (some 1572)) :=
  existingPrivateBound% "M6.Source.AXBindings.B009" "M6.Source.AXAll.row1571_i0"
theorem row1572_i0 : resolveAt exactSites 1572 = some (Instruction.inc 1 (some 1573)) :=
  existingPrivateBound% "M6.Source.AXBindings.B009" "M6.Source.AXAll.row1572_i0"
theorem bound1573_u : UnpairPartial.Bound exactSites 1573 :=
  existingPrivateBound% "M6.Source.AXBindings.B009" "M6.Source.AXAll.bound1573_u"
theorem bound1573_q : AXPair.Bound exactSites 1553 :=
  existingPrivateBound% "M6.Source.AXBindings.B009" "M6.Source.AXAll.bound1573_q"
theorem bound1573_m : AXTimes4.Bound exactSites 1594 :=
  existingPrivateBound% "M6.Source.AXBindings.B009" "M6.Source.AXAll.bound1573_m"
theorem row1600_i0 : resolveAt exactSites 1600 = some (Instruction.inc 1 (some 1601)) :=
  existingPrivateBound% "M6.Source.AXBindings.B009" "M6.Source.AXAll.row1600_i0"
theorem row1601_i0 : resolveAt exactSites 1601 = some (Instruction.inc 1 (some 1602)) :=
  existingPrivateBound% "M6.Source.AXBindings.B009" "M6.Source.AXAll.row1601_i0"
theorem bound1602_p : AXPushParam.Bound exactSites 1577 :=
  existingPrivateBound% "M6.Source.AXBindings.B009" "M6.Source.AXAll.bound1602_p"
theorem block1485 : AXTyped.Bound .copyD 1485 1492 :=
  AXTyped.Bound.copyD 1485 (by decide) bound1485_c
theorem block1492 : AXTyped.Bound .push 1492 1511 :=
  AXTyped.Bound.push 1467 (by decide) bound1492_p
theorem block1511 : AXTyped.Bound .copyH 1511 1518 :=
  AXTyped.Bound.copyH 1511 (by decide) bound1511_c
theorem block1518 : AXTyped.Bound .push 1518 1537 :=
  AXTyped.Bound.push 1493 (by decide) bound1518_p
theorem block1537 : AXTyped.Bound .copyA 1537 1544 :=
  AXTyped.Bound.copyA 1537 (by decide) bound1537_c
theorem block1544 : AXTyped.Bound .cons 1544 1571 :=
  AXTyped.Bound.cons 1524 (by decide) bound1544_u bound1544_q bound1544_m
theorem block1571 : AXTyped.Bound .incT 1571 1572 :=
  AXTyped.Bound.incT 1571 (by decide) row1571_i0
theorem block1572 : AXTyped.Bound .incT 1572 1573 :=
  AXTyped.Bound.incT 1572 (by decide) row1572_i0
theorem block1573 : AXTyped.Bound .cons 1573 1600 :=
  AXTyped.Bound.cons 1553 (by decide) bound1573_u bound1573_q bound1573_m
theorem block1600 : AXTyped.Bound .incT 1600 1601 :=
  AXTyped.Bound.incT 1600 (by decide) row1600_i0
theorem block1601 : AXTyped.Bound .incT 1601 1602 :=
  AXTyped.Bound.incT 1601 (by decide) row1601_i0
theorem block1602 : AXTyped.Bound .push 1602 1621 :=
  AXTyped.Bound.push 1577 (by decide) bound1602_p
end M6.Source.AXModelBounds

