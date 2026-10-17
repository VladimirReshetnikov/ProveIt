import BusyBeaver.ZFC.ArithmeticSitePerm252
import BusyBeaver.ZFC.ArithmeticBootstrapPerm252

set_option autoImplicit false

/-!
Finite natural-data compatibility for the actual symbolic tape interpretation,
and the exact arithmetic entry reached by the existing blank bootstrap.
All repetitions and lists in the compatibility statements are externally finite;
the untouched numeric suffix is an arbitrary internal IΣ1-model value.
The closed boot result is transferred through generic tape and pairing laws,
without expanding the large boot numeral or replaying the 82,552 steps.
No internal dispatch invariant or unbounded runtime is asserted.
Mira-Cult, Jeff and Wade retain their machine/framework attribution.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticSiteBootPerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticMachinePerm252 ArithmeticMachineStepPerm252
open ArithmeticMachineUniformScansPerm252 ArithmeticRegisterForwardPerm252
open ArithmeticRegisterFilePerm252 ArithmeticZeroRegisterBlocks254
open ArithmeticSymbolicTapePerm252 ArithmeticSymbolicBoxesPerm252
open ArithmeticSymbolicExecutionPerm252 (value)
open SymbolicPerm252 (Box Reg)
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Interpretation of a fixed finite nearest-first bit prefix. -/
noncomputable def bitsPrefix : List Bool → V → V
  | [], suffix => suffix
  | b :: bs, suffix => 2*bitsPrefix bs suffix+digit b

lemma bitsPrefix_append (xs ys : List Bool) (suffix : V) :
    bitsPrefix (xs++ys) suffix = bitsPrefix xs (bitsPrefix ys suffix) := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp only [List.cons_append,bitsPrefix,ih]

lemma bitPrefix_replicate (b : Bool) (n : Nat) (suffix : V) :
    bitPrefix b (n : V) suffix = bitsPrefix (List.replicate n b) suffix := by
  induction n with
  | zero => simp only [Nat.cast_zero,bitPrefix_zero,List.replicate_zero,bitsPrefix]
  | succ n ih =>
    simp only [Nat.cast_succ,bitPrefix_succ,List.replicate_succ,bitsPrefix,ih]

lemma bitsCode_cast (xs : List Bool) : (bitsCode xs : V) = bitsPrefix xs 0 := by
  induction xs with
  | nil => simp [bitsCode,bitsPrefix]
  | cons b xs ih =>
    cases b <;> simp only [bitsCode,bitsPrefix,Bool.toNat_false,Bool.toNat_true,
      Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,digit,Bool.false_eq_true,if_true,if_false,ih] <;> ring

lemma registerBlock_nat (v : Nat) (suffix : V) :
    registerBlock (v : V) suffix =
      bitsPrefix (false::true::List.replicate v true) suffix := by
  rw [registerBlock,bitPrefix_succ,bitPrefix_replicate]
  simp only [bitsPrefix,digit,Bool.false_eq_true,if_true,if_false]
  ring

lemma fileCode_nat (values : List Nat) (suffix : V) :
    fileCode (values.map (fun v : Nat => (v : V))) suffix =
      bitsPrefix (RegisterBoxesPerm252.registerBits values) suffix := by
  induction values with
  | nil => rfl
  | cons v values ih =>
    change registerBlock (v : V) (fileCode (values.map (fun x : Nat => (x : V))) suffix) =
      bitsPrefix ((false::true::List.replicate v true) ++
        RegisterBoxesPerm252.registerBits values) suffix
    rw [bitsPrefix_append,←registerBlock_nat,ih]

lemma zeroBlocks_replicate (n : Nat) (suffix : V) :
    zeroBlocks (n : V) suffix = fileCode (List.replicate n (0 : V)) suffix := by
  induction n with
  | zero => simp only [Nat.cast_zero,zeroBlocks_zero,List.replicate_zero,fileCode]
  | succ n ih =>
    simp only [Nat.cast_succ,zeroBlocks_succ,List.replicate_succ,fileCode,←ih,
      registerBlock,bitPrefix_succ,bitPrefix_zero,digit,if_true]
    ring

/-- The fixed spare layout used by actual boxBits, with an external zero count. -/
def fullValues (values : List Nat) (count : Nat) : List Nat :=
  values ++ (List.replicate 8 0 ++ [1] ++ List.replicate count 0)

lemma fullValues_cast (values : List Nat) (count : Nat) :
    (fullValues values count).map (fun v : Nat => (v : V)) =
      values.map (fun v : Nat => (v : V)) ++ fixedSpares ++ List.replicate count 0 := by
  simp [fullValues,fixedSpares,List.map_append,List.map_replicate,List.append_assoc]

lemma unchanged_boxBits (values : List Nat) (count : Nat) (suffix : V) :
    boxPrefix (values.map (fun v : Nat => (v : V))) (count : V) (.plain .unchanged) suffix =
      bitsPrefix (SymbolicPerm252.boxBits (.plain .unchanged) (fullValues values count)) suffix := by
  have hf := fileCode_nat (V := V) (fullValues values count) (2*suffix)
  rw [fullValues_cast,fileCode_append,fileCode_append,←zeroBlocks_replicate] at hf
  simpa only [boxPrefix,spareTail,SymbolicPerm252.boxBits,bitsPrefix_append,
    bitsPrefix,digit,Bool.false_eq_true,if_false,add_zero] using hf

lemma getD_cast (values : List Nat) (r : Nat) :
    (values.map (fun v : Nat => (v : V))).getD r 0 = (values.getD r 0 : V) := by
  induction values generalizing r with
  | nil => simp
  | cons v values ih =>
    cases r with
    | zero => rfl
    | succ r => simpa only [List.map_cons,List.getD_cons_succ] using ih r

lemma writeAt_incr (values : List Nat) (r : Nat) :
    writeAt (values.map (fun v : Nat => (v : V))) r ((values.getD r 0 : V)+1) =
      (SymbolicPerm252.incr r values).map (fun v : Nat => (v : V)) := by
  induction values generalizing r with
  | nil => cases r <;> rfl
  | cons v values ih =>
    cases r <;> simp only [writeAt,SymbolicPerm252.incr,List.map_cons,
      List.getD_cons_zero,List.getD_cons_succ,Nat.cast_add,Nat.cast_one,ih]

lemma writeAt_decr (values : List Nat) (r : Nat) :
    writeAt (values.map (fun v : Nat => (v : V))) r ((values.getD r 0 : V)-1) =
      (SymbolicPerm252.decr r values).map (fun v : Nat => (v : V)) := by
  induction values generalizing r with
  | nil => cases r <;> rfl
  | cons v values ih =>
    cases r with
    | zero => cases v <;> simp [writeAt,SymbolicPerm252.decr]
    | succ r => simpa only [writeAt,SymbolicPerm252.decr,List.map_cons,
        List.getD_cons_succ] using congrArg (List.cons (v : V)) (ih r)

lemma incr_append (r : Nat) (values tail : List Nat) (hr : r < values.length) :
    SymbolicPerm252.incr r (values++tail) = SymbolicPerm252.incr r values ++ tail := by
  induction values generalizing r with
  | nil => simp at hr
  | cons v values ih =>
    cases r with
    | zero => rfl
    | succ r => simpa only [List.cons_append,SymbolicPerm252.incr] using
        congrArg (List.cons v) (ih r (by simpa using hr))

lemma decr_append (r : Nat) (values tail : List Nat) (hr : r < values.length) :
    SymbolicPerm252.decr r (values++tail) = SymbolicPerm252.decr r values ++ tail := by
  induction values generalizing r with
  | nil => simp at hr
  | cons v values ih =>
    cases r with
    | zero => rfl
    | succ r => simpa only [List.cons_append,SymbolicPerm252.decr] using
        congrArg (List.cons v) (ih r (by simpa using hr))

lemma markedPrefix_nat (r : Nat) (values : List Nat) (suffix : V) :
    markedPrefix r (values.map (fun v : Nat => (v : V))) suffix =
      bitsPrefix (SymbolicPerm252.markedBits r values) suffix := by
  induction values generalizing r with
  | nil => cases r <;> rfl
  | cons v values ih =>
    cases r with
    | zero =>
      simp only [List.map_cons,markedPrefix,SymbolicPerm252.markedBits,
        bitsPrefix,bitsPrefix_append,←bitPrefix_replicate,←fileCode_nat,digit,Bool.false_eq_true,if_false]
      ring
    | succ r =>
      change registerBlock (v : V)
        (markedPrefix r (values.map (fun x : Nat => (x : V))) suffix) =
          bitsPrefix ((false::true::List.replicate v true) ++
            SymbolicPerm252.markedBits r values) suffix
      rw [bitsPrefix_append,←registerBlock_nat,ih]

lemma markedBits_append (r : Nat) (values tail : List Nat) (hr : r < values.length) :
    SymbolicPerm252.markedBits r (values++tail) =
      SymbolicPerm252.markedBits r values ++ RegisterBoxesPerm252.registerBits tail := by
  induction values generalizing r with
  | nil => simp at hr
  | cons v values ih =>
    cases r with
    | zero => simp [SymbolicPerm252.markedBits,RegisterBoxesPerm252.registerBits_append,
        List.append_assoc]
    | succ r => simp only [List.cons_append,SymbolicPerm252.markedBits,
        ih r (by simpa using hr),List.append_assoc]

lemma fullValues_decr (r : Nat) (values : List Nat) (count : Nat)
    (hr : r < values.length) :
    SymbolicPerm252.decr r (fullValues values count) ++ [0] =
      fullValues (SymbolicPerm252.decr r values) (count+1) := by
  rw [fullValues,decr_append r values _ hr,fullValues]
  simp only [List.append_assoc,List.replicate_add,List.replicate_one]

/-- All four actual Box forms, including decrement's appended zero and the
literal final padding; selected primary registers remain before the spares. -/
theorem boxBits_compat (x : Box) (values : List Nat) (hlen : values.length = 9)
    (count : Nat) (suffix : V) :
    boxPrefix (values.map (fun v : Nat => (v : V))) (count : V) x suffix =
      bitsPrefix (SymbolicPerm252.boxBits x (fullValues values count)) suffix := by
  cases x with
  | plain effect => cases effect with
    | unchanged => exact unchanged_boxBits values count suffix
    | increment r =>
      have hr : r.val < values.length := by simpa only [hlen] using r.isLt
      simp only [boxPrefix,getD_cast,writeAt_incr]
      simpa only [boxPrefix,SymbolicPerm252.boxBits,fullValues,
        incr_append r.val values _ hr] using
        unchanged_boxBits (V := V) (SymbolicPerm252.incr r.val values) count suffix
    | decrement r =>
      have hr : r.val < values.length := by simpa only [hlen] using r.isLt
      simp only [boxPrefix,getD_cast,writeAt_decr]
      rw [show ((count : V)+1) = ((count+1 : Nat) : V) by simp]
      simpa only [boxPrefix,SymbolicPerm252.boxBits,fullValues_decr r.val values count hr] using
        unchanged_boxBits (V := V) (SymbolicPerm252.decr r.val values) (count+1) suffix
  | marked r =>
    have hr : r.val < values.length := by simpa only [hlen] using r.isLt
    simp only [boxPrefix,spareTail,markedPrefix_nat,SymbolicPerm252.boxBits,
      fullValues,markedBits_append r.val values _ hr,bitsPrefix_append,bitsPrefix,
      digit,Bool.false_eq_true,if_false,add_zero]
    have ht := unchanged_boxBits (V := V) ([] : List Nat) count suffix
    simpa only [boxPrefix,fileCode,List.map_nil,spareTail,SymbolicPerm252.boxBits,fullValues,
      List.nil_append,bitsPrefix_append,bitsPrefix,digit,Bool.false_eq_true,if_false,add_zero] using
      congrArg (bitsPrefix (SymbolicPerm252.markedBits r.val values)) ht

/-- Generic pairing cast identity, proved from the exact polynomial graph. -/
lemma cantor_cast (a b : Nat) : cantor (a : V) (b : V) = (Code254.P a b : V) := by
  symm
  apply cantor_graph.mpr
  have h := congrArg (fun n : Nat => (n : V))
    ((codeP_graph (Code254.P a b) a b).mp rfl)
  simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] using h

lemma encodeConfig_cast (u : NumericConfig) :
    (encodeConfig u : V) = frame (u.state : V) (u.left : V) (u.right : V) := by
  simp only [encodeConfig,frame,cantor_cast]

/-- The native compiler's register-bit function is exactly the box function. -/
lemma boot_registerBits (values : List Nat) :
    BootPerm252.registerBitsPerm252 values = RegisterBoxesPerm252.registerBits values :=
  (RegisterBoxesPerm252.registerBits_eq_flatMap values).symm

/-- Kept separate from the large boot code: this is just the Site.start shape. -/
lemma startValue_nil (values : List V) (count gap : V) :
    ArithmeticSitePerm252.startValue values count gap [] =
      frame 95 1 (bitPrefix false (gap+40)
        (2*boxPrefix values count (.plain .unchanged) 0+1)) := by
  simp only [ArithmeticSitePerm252.startValue,value,configValue,SitePerm252.start,
    SitePerm252.dispatch,SitePerm252.minDistance,ArithmeticMachinePerm252.stateCode,
    List.length_nil,Nat.sub_zero,List.map_nil,List.nil_append,tapePrefix,segmentPrefix,
    affine,digit,Bool.false_eq_true,if_false,if_true,mul_zero,zero_add,
    Nat.cast_ofNat,Nat.cast_one,one_mul,show (94+1 : Nat) = 95 by rfl]

/-- A small list identity, retaining exactly one final false padding cell. -/
lemma boot_right_bits : BootPerm252.bootTargetPerm252.right =
    List.replicate 40 false ++ true ::
      SymbolicPerm252.boxBits (.plain .unchanged)
        (fullValues (List.replicate 9 0) 56) := by
  simp only [BootPerm252.bootTargetPerm252,BootPerm252.bootRegistersPerm252,
    BootPerm252.bootSparesPerm252,fullValues,boot_registerBits,
    SymbolicPerm252.boxBits,List.replicate_one,List.append_assoc,List.cons_append,List.nil_append]

/-- The exact closed entry, with nine zero primary registers and 56 variable
zero spares after the fixed eight-zero/one suffix. No huge numeral is unfolded. -/
theorem bootCode_start : (ArithmeticBootstrapPerm252.bootCode : V) =
    ArithmeticSitePerm252.startValue (List.replicate 9 (0 : V)) 56 0 [] := by
  have hb := boxBits_compat (V := V) (.plain .unchanged)
    (List.replicate 9 0) (by simp) 56 (0 : V)
  simp only [List.map_replicate,Nat.cast_zero,Nat.cast_ofNat] at hb
  have hL : (bitsCode BootPerm252.bootTargetPerm252.left : V) = 1 := by
    rw [bitsCode_cast]
    change bitsPrefix (true::List.replicate 10 false) 0 = 1
    rw [bitsPrefix,←bitPrefix_replicate,bitPrefix_false_zero]
    simp [digit]
  have hR : (bitsCode BootPerm252.bootTargetPerm252.right : V) =
      bitPrefix false (40 : V)
        (2*boxPrefix (List.replicate 9 (0 : V)) 56 (.plain .unchanged) 0+1) := by
    rw [bitsCode_cast,boot_right_bits,bitsPrefix_append]
    change bitsPrefix (List.replicate 40 false)
      (2*bitsPrefix (SymbolicPerm252.boxBits (.plain .unchanged)
        (fullValues (List.replicate 9 0) 56)) 0+digit true) = _
    rw [←hb,←bitPrefix_replicate]
    simp only [Nat.cast_ofNat,digit,if_true]
  change (encodeConfig (encodeZip BootPerm252.bootTargetPerm252) : V) = _
  rw [encodeConfig_cast]
  change frame (95 : V) (bitsCode BootPerm252.bootTargetPerm252.left : V)
    (bitsCode BootPerm252.bootTargetPerm252.right : V) = _
  rw [hL,hR,startValue_nil]
  simp only [zero_add]

/-- The already checked blank prefix reaches the exact numeric Site.start[]. -/
theorem internal_boot_start : ArithmeticMachineRunPerm252.run (82552 : V) =
    ArithmeticSitePerm252.startValue (List.replicate 9 (0 : V)) 56 0 [] :=
  (ArithmeticBootstrapPerm252.internal_boot (V := V)).trans bootCode_start

end SetTheory.BusyBeaver.ZFC.ArithmeticSiteBootPerm252
