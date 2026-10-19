import BusyBeaver.ZFC.ArithmeticOneRegisterBlocksRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticOneRegisterBlocksRotation240 ArithmeticMachinePerm252

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticOneRegisterBlocksRotation240.oneBlocks_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticOneRegisterBlocksRotation240.oneBlocks_succ
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticOneRegisterBlocksRotation240.oneBlocks_one
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticOneRegisterBlocksRotation240.oneBlocks_add
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticOneRegisterBlocksRotation240.oneBlocks_push
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticOneRegisterBlocksRotation240.oneBlocks_total
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticOneRegisterBlocksRotation240.oneBlocks_bitsCode
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticOneRegisterBlocksRotation240.oneBlocksDef_bitsCode
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticOneRegisterBlocksRotation240.oneBlocks_defined_delta

section Internal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example : 𝚺₁-Function₂[V] oneBlocks via oneBlocksDef := oneBlocks_defined
example : 𝚫₁-Function₂[V] oneBlocks via oneBlocksDeltaDef := oneBlocks_defined_delta
example (suffix : V) : oneBlocks 0 suffix = suffix := oneBlocks_zero suffix
example (count suffix : V) : oneBlocks (count+1) suffix = 8*oneBlocks count suffix+6 :=
  oneBlocks_succ count suffix
example (a b suffix : V) : oneBlocks (a+b) suffix = oneBlocks b (oneBlocks a suffix) :=
  oneBlocks_add a b suffix
example (count suffix : V) : oneBlocks count (8*suffix+6) = oneBlocks (count+1) suffix :=
  oneBlocks_push count suffix
example (count suffix : V) : ∃! out, oneBlocksDef.val.Evalb ![out,count,suffix] :=
  oneBlocks_total count suffix
example (additional : V) :
    oneBlocks (167+additional) (8*(0 : V)+6) = oneBlocks ((167+additional)+1) 0 :=
  oneBlocks_push (167+additional) 0
end Internal

example (count : Nat) (suffix : List Bool) :
    oneBlocks count (bitsCode suffix) =
      bitsCode ((List.replicate count [false,true,true]).flatten ++ suffix) :=
  oneBlocks_bitsCode count suffix
example (out count : Nat) (suffix : List Bool) :
    oneBlocksDef.val.Evalb ![out,count,bitsCode suffix] ↔
      out = bitsCode ((List.replicate count [false,true,true]).flatten ++ suffix) :=
  oneBlocksDef_bitsCode out count suffix
example : oneBlocks (167 : Nat) (bitsCode []) =
    bitsCode ((List.replicate 167 [false,true,true]).flatten ++ []) :=
  oneBlocks_bitsCode 167 []
