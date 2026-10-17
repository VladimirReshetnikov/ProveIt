import BusyBeaver.ZFC.ArithmeticMachineScanPerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticTapePrefix254
open ArithmeticMachineGraphPerm252 ArithmeticMachineStepPerm252 ArithmeticMachineRunFromPerm252
open ArithmeticMachineScanPerm252
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineScanPerm252.odd_mod_two
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineScanPerm252.odd_div_two
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineScanPerm252.apply_right_one
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineScanPerm252.seekInc_action
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineScanPerm252.scanFrame_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineScanPerm252.seekInc_step
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineScanPerm252.seekInc_scan
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineScanPerm252.seekInc_scan_graph
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (x : V) : (2*x+1)%2 = 1 := odd_mod_two x
example (x : V) : (2*x+1)/2 = x := odd_div_two x
example (q left right : V) : applyValue (4*q+4) left right = cantor q (cantor (2*left+1) (right/2)) := apply_right_one q left right
example : actionLookup (72 : V) 1 = 292 := seekInc_action
example (n left suffix : V) : stepValue (scanFrame left (onesPrefix (n+1) suffix)) = scanFrame (2*left+1) (onesPrefix n suffix) := seekInc_step n left suffix
example (n left suffix : V) : runFrom n (scanFrame left (onesPrefix n suffix)) = scanFrame (onesPrefix n left) suffix := seekInc_scan n left suffix
example (out n left suffix : V) : runFromDef.val.Evalb ![out,n,scanFrame left (onesPrefix n suffix)] ↔ out = scanFrame (onesPrefix n left) suffix := seekInc_scan_graph out n left suffix
example (left right : V) : runFrom 0 (scanFrame left right) = scanFrame left right := runFrom_zero _
example (n left suffix : V) : runFrom n (scanFrame left (onesPrefix n (2*suffix+1))) = scanFrame (onesPrefix n left) (2*suffix+1) := seekInc_scan n left (2*suffix+1)
example (left suffix : V) : stepValue (scanFrame left (2*suffix+1)) = scanFrame (2*left+1) suffix := by
  simpa only [onesPrefix_succ, onesPrefix_zero] using seekInc_step (0 : V) left suffix

example (out left right : V) : scanFrameDef.val.Evalb ![out,left,right] ↔ out = scanFrame left right := by simp
