import BusyBeaver.ZFC.ArithmeticZeroSpareScanPerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticZeroRegisterBlocks254 ArithmeticMachineRunFromPerm252
open ArithmeticMachineUniformScansPerm252 ArithmeticZeroSpareScanPerm252
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticZeroSpareScanPerm252.reverseZeroBlocks_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticZeroSpareScanPerm252.zeroBlocks_even
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticZeroSpareScanPerm252.two_reverseZeroBlocks
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticZeroSpareScanPerm252.reverseZeroBlocks_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticZeroSpareScanPerm252.reverseZeroBlocks_succ
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticZeroSpareScanPerm252.reverseZeroBlocks_push
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticZeroSpareScanPerm252.reverseBlock_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticZeroSpareScanPerm252.scan_zero_blocks
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticZeroSpareScanPerm252.scan_zero_blocks_dec
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticZeroSpareScanPerm252.scan_zero_blocks_inc
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticZeroSpareScanPerm252.scan_zero_blocks_suffix
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (out count left : V) : reverseZeroBlocksDef.val.Evalb ![out,count,left] ↔ out = reverseZeroBlocks count left := by simp
example (count left : V) : ∃ half : V, zeroBlocks count (2*left) = 2*half := zeroBlocks_even count left
example (count left : V) : 2*reverseZeroBlocks count left = zeroBlocks count (2*left) := two_reverseZeroBlocks count left
example (left : V) : reverseZeroBlocks 0 left = left := reverseZeroBlocks_zero left
example (count left : V) : reverseZeroBlocks (count+1) left = 4*reverseZeroBlocks count left+1 := reverseZeroBlocks_succ count left
example (count left : V) : reverseZeroBlocks count (4*left+1) = reverseZeroBlocks (count+1) left := reverseZeroBlocks_push count left
example (count left suffix : V) : runFrom (2*count) (frame 43 left (zeroBlocks count suffix)) = frame 43 (reverseZeroBlocks count left) suffix := scan_zero_blocks_dec count left suffix
example (count left suffix : V) : runFrom (2*count) (frame 72 left (zeroBlocks count suffix)) = frame 72 (reverseZeroBlocks count left) suffix := scan_zero_blocks_inc count left suffix
example (count left suffix : V) : runFrom (2*count) (frame 84 left (zeroBlocks count suffix)) = frame 84 (reverseZeroBlocks count left) suffix := scan_zero_blocks_suffix count left suffix
example (left suffix : V) : runFrom 0 (frame 72 left suffix) = frame 72 left suffix := by simp
example (left suffix : V) : runFrom 2 (frame 72 left (4*suffix+2)) = frame 72 (4*left+1) suffix := by
  have hreverse : reverseZeroBlocks (1 : V) left = 4*left+1 := by
    simpa only [zero_add, reverseZeroBlocks_zero] using reverseZeroBlocks_succ (0 : V) left
  simpa [zeroBlocks_one, hreverse] using scan_zero_blocks_inc (1 : V) left suffix
example (count left suffix : V) : runFrom (2*count) (frame 72 left (zeroBlocks count (2*suffix+1))) = frame 72 (reverseZeroBlocks count left) (2*suffix+1) := scan_zero_blocks_inc count left (2*suffix+1)
