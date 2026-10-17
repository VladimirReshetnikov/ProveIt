import BusyBeaver.ZFC.ArithmeticMachineUniformScansPerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticMachineGraphPerm252 ArithmeticMachineStepPerm252 ArithmeticMachineRunFromPerm252
open ArithmeticMachineUniformScansPerm252
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineUniformScansPerm252.zerosPrefix_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineUniformScansPerm252.bitPrefix_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineUniformScansPerm252.bitPrefix_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineUniformScansPerm252.bitPrefix_succ
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineUniformScansPerm252.bitPrefix_push
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineUniformScansPerm252.bitPrefix_bit
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineUniformScansPerm252.bitPrefix_half
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineUniformScansPerm252.frame_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineUniformScansPerm252.apply_right_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineUniformScansPerm252.apply_right
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineUniformScansPerm252.apply_left_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineUniformScansPerm252.apply_left_one
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineUniformScansPerm252.apply_left
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineUniformScansPerm252.step_right
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineUniformScansPerm252.step_left
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineUniformScansPerm252.scan_right
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineUniformScansPerm252.scan_left
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineUniformScansPerm252.right_row_of_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineUniformScansPerm252.left_row_of_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineUniformScansPerm252.scan_right_numeral
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticMachineUniformScansPerm252.scan_left_numeral

example (out n suffix : V) : zerosPrefixDef.val.Evalb ![out,n,suffix] ↔ out = Exp.exp n * suffix := by simp [zerosPrefix]
example (b : Bool) (out n suffix : V) : (bitPrefixDef b).val.Evalb ![out,n,suffix] ↔ out = bitPrefix b n suffix := by simp
example (b : Bool) (suffix : V) : bitPrefix b 0 suffix = suffix := bitPrefix_zero b suffix
example (b : Bool) (n suffix : V) : bitPrefix b (n+1) suffix = 2*bitPrefix b n suffix+digit b := bitPrefix_succ b n suffix
example (b : Bool) (n suffix : V) : bitPrefix b n (2*suffix+digit b) = bitPrefix b (n+1) suffix := bitPrefix_push b n suffix
example (b : Bool) (n suffix : V) : bitPrefix b (n+1) suffix % 2 = digit (V := V) b := bitPrefix_bit b n suffix
example (b : Bool) (n suffix : V) : bitPrefix b (n+1) suffix / 2 = bitPrefix b n suffix := bitPrefix_half b n suffix
example (out q left right : V) : frameDef.val.Evalb ![out,q,left,right] ↔ out = frame q left right := by simp
example (b : Bool) (q left right : V) : applyValue (4*q+3+digit b) left right = frame q (2*left+digit b) (right/2) := apply_right b q left right
example (b : Bool) (q left right : V) : applyValue (4*q+1+digit b) left right = frame q (left/2) (left%2+2*(digit b+2*(right/2))) := apply_left b q left right
example (b : Bool) (q n left suffix : V) (h : actionLookup q (digit b) = 4*q+3+digit b) : runFrom n (frame q left (bitPrefix b n suffix)) = frame q (bitPrefix b n left) suffix := scan_right b q h n left suffix
example (b : Bool) (q n left right : V) (h : actionLookup q (digit b) = 4*q+1+digit b) : runFrom n (leftFrame q (bitPrefix b n left) right) = leftFrame q left (bitPrefix b n right) := scan_left b q h n left right
example (n left suffix : V) : runFrom n (frame 10 left (bitPrefix false n suffix)) = frame 10 (bitPrefix false n left) suffix := scan_right_numeral false 10 (by decide) n left suffix
example (n left suffix : V) : runFrom n (frame 72 left (bitPrefix true n suffix)) = frame 72 (bitPrefix true n left) suffix := scan_right_numeral true 72 (by decide) n left suffix
example (n left right : V) : runFrom n (leftFrame 4 (bitPrefix false n left) right) = leftFrame 4 left (bitPrefix false n right) := scan_left_numeral false 4 (by decide) n left right
example (n left right : V) : runFrom n (leftFrame 3 (bitPrefix true n left) right) = leftFrame 3 left (bitPrefix true n right) := scan_left_numeral true 3 (by decide) n left right
example (q left right : V) : runFrom 0 (leftFrame q left right) = leftFrame q left right := runFrom_zero _
example (n : V) : zerosPrefix n 0 = 0 := by simp [zerosPrefix]
