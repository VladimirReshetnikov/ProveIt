import BusyBeaver.ZFC.ArithmeticSiteBootPerm252
set_option autoImplicit false
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticMachinePerm252 ArithmeticMachineStepPerm252
open ArithmeticMachineUniformScansPerm252 ArithmeticRegisterForwardPerm252
open ArithmeticRegisterFilePerm252 ArithmeticZeroRegisterBlocks254
open ArithmeticSymbolicBoxesPerm252 ArithmeticSiteBootPerm252
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteBootPerm252.bitsPrefix_append
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteBootPerm252.bitPrefix_replicate
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteBootPerm252.bitsCode_cast
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteBootPerm252.registerBlock_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteBootPerm252.fileCode_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteBootPerm252.zeroBlocks_replicate
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteBootPerm252.unchanged_boxBits
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteBootPerm252.boxBits_compat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteBootPerm252.cantor_cast
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteBootPerm252.encodeConfig_cast
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteBootPerm252.boot_registerBits
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteBootPerm252.startValue_nil
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteBootPerm252.boot_right_bits
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteBootPerm252.bootCode_start
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteBootPerm252.internal_boot_start
section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (xs ys : List Bool) (suffix : V) :
    bitsPrefix (xs++ys) suffix = bitsPrefix xs (bitsPrefix ys suffix) :=
  bitsPrefix_append xs ys suffix
example (b : Bool) (n : Nat) (suffix : V) :
    bitPrefix b (n : V) suffix = bitsPrefix (List.replicate n b) suffix :=
  bitPrefix_replicate b n suffix
example (xs : List Bool) : (bitsCode xs : V) = bitsPrefix xs 0 := bitsCode_cast xs
example (v : Nat) (suffix : V) : registerBlock (v : V) suffix =
    bitsPrefix (false::true::List.replicate v true) suffix := registerBlock_nat v suffix
example (values : List Nat) (suffix : V) :
    fileCode (values.map (fun v : Nat => (v : V))) suffix =
      bitsPrefix (RegisterBoxesPerm252.registerBits values) suffix := fileCode_nat values suffix
example (n : Nat) (suffix : V) :
    zeroBlocks (n : V) suffix = fileCode (List.replicate n (0 : V)) suffix :=
  zeroBlocks_replicate n suffix
example (values : List Nat) (count : Nat) (suffix : V) :
    boxPrefix (values.map (fun v : Nat => (v : V))) (count : V) (.plain .unchanged) suffix =
      bitsPrefix (SymbolicPerm252.boxBits (.plain .unchanged) (fullValues values count)) suffix :=
  unchanged_boxBits values count suffix
example (x : SymbolicPerm252.Box) (values : List Nat) (hlen : values.length = 9)
    (count : Nat) (suffix : V) :
    boxPrefix (values.map (fun v : Nat => (v : V))) (count : V) x suffix =
      bitsPrefix (SymbolicPerm252.boxBits x (fullValues values count)) suffix :=
  boxBits_compat x values hlen count suffix
example (a b : Nat) : cantor (a : V) (b : V) = (Code254.P a b : V) := cantor_cast a b
example (u : NumericConfig) :
    (encodeConfig u : V) = frame (u.state : V) (u.left : V) (u.right : V) :=
  encodeConfig_cast u
example (values : List Nat) : BootPerm252.registerBitsPerm252 values =
    RegisterBoxesPerm252.registerBits values := boot_registerBits values
example (values : List V) (count gap : V) : ArithmeticSitePerm252.startValue values count gap [] =
    frame 95 1 (bitPrefix false (gap+40)
      (2*boxPrefix values count (.plain .unchanged) 0+1)) := startValue_nil values count gap
example : BootPerm252.bootTargetPerm252.right = List.replicate 40 false ++ true ::
    SymbolicPerm252.boxBits (.plain .unchanged) (fullValues (List.replicate 9 0) 56) := boot_right_bits
example : (ArithmeticBootstrapPerm252.bootCode : V) =
    ArithmeticSitePerm252.startValue (List.replicate 9 (0 : V)) 56 0 [] := bootCode_start
example : ArithmeticMachineRunPerm252.run (82552 : V) =
    ArithmeticSitePerm252.startValue (List.replicate 9 (0 : V)) 56 0 [] := internal_boot_start
example (x : SymbolicPerm252.Box) (suffix : V) :
    boxPrefix (List.replicate 9 (0 : V)) 0 x suffix =
      bitsPrefix (SymbolicPerm252.boxBits x (fullValues (List.replicate 9 0) 0)) suffix := by
  simpa only [List.map_replicate,Nat.cast_zero,Nat.cast_ofNat] using
    boxBits_compat (V := V) x (List.replicate 9 0) (by simp) 0 suffix
example : (ArithmeticBootstrapPerm252.bootCode : V) =
    frame 95 1 (bitPrefix false (40 : V)
      (2*boxPrefix (List.replicate 9 (0 : V)) 56 (.plain .unchanged) 0+1)) := by
  rw [bootCode_start,startValue_nil]
  simp only [zero_add]
end
