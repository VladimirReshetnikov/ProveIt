import BusyBeaver.ZFC.ArithmeticFiniteTapeRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticMachinePerm252
open ArithmeticMachineStepPerm252 (encodeConfig)
open ArithmeticMachineUniformScansPerm252
open ArithmeticRegisterForwardPerm252 (registerBlock)
open ArithmeticOneRegisterBlocksRotation240 ArithmeticCarryTraversalRotation240
open ArithmeticFiniteTapeRotation240

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticFiniteTapeRotation240.bitsPrefix_append
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticFiniteTapeRotation240.bitPrefix_replicate
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticFiniteTapeRotation240.bitsCode_cast
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticFiniteTapeRotation240.registerBlock_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticFiniteTapeRotation240.fileTape_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticFiniteTapeRotation240.oneBlocks_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticFiniteTapeRotation240.cantor_cast
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticFiniteTapeRotation240.encodeConfig_cast

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (xs ys : List Bool) (suffix : V) :
    bitsPrefix (xs++ys) suffix = bitsPrefix xs (bitsPrefix ys suffix) :=
  bitsPrefix_append xs ys suffix
example (b : Bool) (n : Nat) (suffix : V) :
    bitPrefix b (n : V) suffix = bitsPrefix (List.replicate n b) suffix :=
  bitPrefix_replicate b n suffix
example (xs : List Bool) : (bitsCode xs : V) = bitsPrefix xs 0 := bitsCode_cast xs
example (v : Nat) (suffix : V) :
    registerBlock (v : V) suffix = bitsPrefix (false::true::List.replicate v true) suffix :=
  registerBlock_nat v suffix
example (values : List Nat) (suffix : V) :
    fileTape (values.map (fun n : Nat => (n : V))) suffix =
      bitsPrefix (RegisterBoxesPerm252.registerBits values) suffix := fileTape_nat values suffix
example (n : Nat) (suffix : V) :
    oneBlocks (n : V) suffix = fileTape (List.replicate n (1 : V)) suffix := oneBlocks_nat n suffix
example (a b : Nat) : cantor (a : V) (b : V) = (Code254.P a b : V) := cantor_cast a b
example (u : NumericConfig) :
    (encodeConfig u : V) = frame (u.state : V) (u.left : V) (u.right : V) := encodeConfig_cast u

-- The exact startup spare count is external; its following tape stays arbitrary.
example (suffix : V) : oneBlocks (167 : V) suffix = fileTape (List.replicate 167 (1 : V)) suffix :=
  oneBlocks_nat 167 suffix
-- A literal halt code is transported without assuming a computation reaches it.
example (left right : Nat) :
    (encodeConfig ⟨0,left,right⟩ : V) = frame 0 (left : V) (right : V) :=
  encodeConfig_cast ⟨0,left,right⟩
