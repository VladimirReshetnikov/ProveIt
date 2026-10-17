import BusyBeaver.ZFC.ArithmeticZeroRegisterBlocks254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticMachinePerm252 ArithmeticZeroRegisterBlocks254
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticZeroRegisterBlocks254.zeroBlocks_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticZeroRegisterBlocks254.zeroBlocks_defined_delta
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticZeroRegisterBlocks254.zeroBlocks_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticZeroRegisterBlocks254.zeroBlocks_succ
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticZeroRegisterBlocks254.zeroBlocks_one
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticZeroRegisterBlocks254.zeroBlocks_add
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticZeroRegisterBlocks254.zeroBlocks_push
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticZeroRegisterBlocks254.zeroBlocks_bit
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticZeroRegisterBlocks254.zeroBlocks_half
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticZeroRegisterBlocks254.zeroBlocks_second_bit
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticZeroRegisterBlocks254.zeroBlocks_tail_two
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticZeroRegisterBlocks254.zeroBlocks_total
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticZeroRegisterBlocks254.zeroBlocks_bitsCode
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticZeroRegisterBlocks254.zeroBlocksDef_bitsCode
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (out count suffix : V) : zeroBlocksDef.val.Evalb ![out,count,suffix] ↔ out = zeroBlocks count suffix := by simp
example (out count suffix : V) : zeroBlocksDeltaDef.val.Evalb ![out,count,suffix] ↔ out = zeroBlocks count suffix := by simp
example (suffix : V) : zeroBlocks 0 suffix = suffix := zeroBlocks_zero suffix
example (count suffix : V) : zeroBlocks (count+1) suffix = 4*zeroBlocks count suffix+2 := zeroBlocks_succ count suffix
example (m n suffix : V) : zeroBlocks (m+n) suffix = zeroBlocks n (zeroBlocks m suffix) := zeroBlocks_add m n suffix
example (count suffix : V) : zeroBlocks count (4*suffix+2) = zeroBlocks (count+1) suffix := zeroBlocks_push count suffix
example (count suffix : V) : zeroBlocks (count+1) suffix % 2 = 0 := zeroBlocks_bit count suffix
example (count suffix : V) : zeroBlocks (count+1) suffix / 2 = 2*zeroBlocks count suffix+1 := zeroBlocks_half count suffix
example (count suffix : V) : (zeroBlocks (count+1) suffix / 2) % 2 = 1 := zeroBlocks_second_bit count suffix
example (count suffix : V) : zeroBlocks (count+1) suffix / 2 / 2 = zeroBlocks count suffix := zeroBlocks_tail_two count suffix
example (count suffix : V) : ∃! out, zeroBlocksDef.val.Evalb ![out,count,suffix] := zeroBlocks_total count suffix
example (count : Nat) (suffix : List Bool) : zeroBlocks count (bitsCode suffix) = bitsCode ((List.replicate count [false,true]).flatten ++ suffix) := zeroBlocks_bitsCode count suffix
example (out count : Nat) (suffix : List Bool) : zeroBlocksDef.val.Evalb ![out,count,bitsCode suffix] ↔ out = bitsCode ((List.replicate count [false,true]).flatten ++ suffix) := zeroBlocksDef_bitsCode out count suffix
example : zeroBlocks (1 : V) 0 = 2 := by simp [zeroBlocks_one]
example : zeroBlocks (0 : V) 0 = 0 := by simp
