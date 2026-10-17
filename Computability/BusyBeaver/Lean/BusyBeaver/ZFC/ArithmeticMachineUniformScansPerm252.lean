import BusyBeaver.ZFC.ArithmeticMachineScanPerm252

/-!
Uniform zero/one scans of the actual arithmetic evaluator.
A local self-loop lookup equation remains an explicit premise. Both directions
retain the entire tape halves, for all internal lengths. Left-facing frames
recenter numerically; no absolute head coordinate or external finite tape is
asserted. These endpoints do not assert first exit from a scan state.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticMachineUniformScansPerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticTapePrefix254
open ArithmeticMachineGraphPerm252 ArithmeticMachineStepPerm252 ArithmeticMachineRunFromPerm252
open ArithmeticMachineScanPerm252 (odd_mod_two odd_div_two apply_right_one)
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def zerosPrefix (n suffix : V) : V := Exp.exp n * suffix

def zerosPrefixDef : 𝚺₁.Semisentence 3 := .mkSigma
  “out n suffix. ∃ power, !expDef power n ∧ out = power*suffix”
instance zerosPrefix_defined : 𝚺₁-Function₂[V] zerosPrefix via zerosPrefixDef :=
  .mk fun e => by simp [zerosPrefixDef, zerosPrefix]

noncomputable def digit (b : Bool) : V := if b then 1 else 0
noncomputable def bitPrefix (b : Bool) (n suffix : V) : V :=
  if b then onesPrefix n suffix else zerosPrefix n suffix

def bitPrefixDef (b : Bool) : 𝚺₁.Semisentence 3 :=
  if b then .mkSigma “out n suffix. !onesPrefixDef out n suffix” else zerosPrefixDef
instance bitPrefix_defined (b : Bool) :
    𝚺₁-Function₂[V] (bitPrefix b) via bitPrefixDef b := .mk fun e => by
  cases b <;> simp [bitPrefixDef, bitPrefix, zerosPrefix_defined.iff]
private instance bitPrefix_delta (b : Bool) : 𝚫₁-Function₂[V] (bitPrefix b) :=
  (bitPrefix_defined b).graph_delta.to_definable

@[simp] theorem bitPrefix_zero (b : Bool) (suffix : V) : bitPrefix b 0 suffix = suffix := by
  cases b <;> simp [bitPrefix, zerosPrefix]

theorem bitPrefix_succ (b : Bool) (n suffix : V) :
    bitPrefix b (n+1) suffix = 2*bitPrefix b n suffix+digit b := by
  cases b
  · simp only [bitPrefix, digit, Bool.false_eq_true, if_false, zerosPrefix, exp_succ]
    ring
  · simpa only [bitPrefix, digit, if_true] using onesPrefix_succ n suffix

theorem bitPrefix_push (b : Bool) (n suffix : V) :
    bitPrefix b n (2*suffix+digit b) = bitPrefix b (n+1) suffix := by
  cases b
  · simp only [bitPrefix, digit, Bool.false_eq_true, if_false, zerosPrefix, exp_succ]
    ring
  · simpa only [bitPrefix, digit, if_true] using onesPrefix_push n suffix

lemma even_mod_two (x : V) : (2*x)%2 = 0 := by
  simpa only [add_zero, mul_comm] using
    (mod_mul_add_of_lt x 2 (by simp : (0 : V) < 2))
lemma even_div_two (x : V) : (2*x)/2 = x := by
  simpa only [add_zero] using (div_mul_add' x 2 (by simp : (0 : V) < 2))
lemma digit_mod_two (b : Bool) (x : V) : (2*x+digit b)%2 = digit (V := V) b := by
  cases b <;> simp [digit]
lemma digit_div_two (b : Bool) (x : V) : (2*x+digit b)/2 = x := by
  cases b <;> simp [digit]

theorem bitPrefix_bit (b : Bool) (n suffix : V) :
    bitPrefix b (n+1) suffix % 2 = digit (V := V) b := by
  rw [bitPrefix_succ, digit_mod_two]
theorem bitPrefix_half (b : Bool) (n suffix : V) :
    bitPrefix b (n+1) suffix / 2 = bitPrefix b n suffix := by
  rw [bitPrefix_succ, digit_div_two]

noncomputable def frame (q left right : V) : V := cantor q (cantor left right)
def frameDef : 𝚺₁.Semisentence 4 := .mkSigma
  “out q left right. ∃ tape, !ArithmeticCantor.pairDef tape left right ∧ !ArithmeticCantor.pairDef out q tape”
instance frame_defined : 𝚺₁-Function₃[V] frame via frameDef :=
  .mk fun e => by simp [frameDef, frame]
private instance frame_delta : 𝚫₁-Function₃[V] frame := frame_defined.graph_delta.to_definable
private instance runFrom_delta : 𝚫₁-Function₂[V] runFrom := runFrom_defined_delta.to_definable

noncomputable def leftFrame (q left right : V) : V := frame q (left/2) (left%2+2*right)
private instance leftFrame_delta : 𝚫₁-Function₃[V] leftFrame := by
  unfold leftFrame
  definability

lemma apply_right_zero (q left right : V) :
    applyValue (4*q+3) left right = frame q (2*left) (right/2) := by
  have hp : (4*q+3)-1 = 4*q+2 := by
    rw [show (4*q+3 : V) = (4*q+2)+1 by ring]; simp
  have hs : (4*q+2)/4 = q := div_mul_add' q 4 (by simpa only [Nat.cast_ofNat] using ((Nat.cast_lt (α := V)).mpr (by decide : (2 : Nat) < 4)))
  have hh : (4*q+2)/2 = 2*q+1 := by
    rw [show (4*q+2 : V) = 2*(2*q+1) by ring, even_div_two]
  have hw : (4*q+2)%2 = 0 := by
    rw [show (4*q+2 : V) = 2*(2*q+1) by ring, even_mod_two]
  simp [applyValue, hp, hs, hh, hw, frame]

lemma apply_right (b : Bool) (q left right : V) :
    applyValue (4*q+3+digit b) left right = frame q (2*left+digit b) (right/2) := by
  cases b
  · simpa [digit] using apply_right_zero q left right
  · simpa [digit, frame, show (4*q+3+1 : V) = 4*q+4 by ring] using apply_right_one q left right

lemma apply_left_zero (q left right : V) :
    applyValue (4*q+1) left right = frame q (left/2) (left%2+2*(2*(right/2))) := by
  have hp : (4*q+1)-1 = 4*q := by simp
  have hs : (4*q)/4 = q := by
    simpa only [add_zero] using (div_mul_add' q 4 (by simp : (0 : V) < 4))
  have hh : (4*q)/2 = 2*q := by
    rw [show (4*q : V) = 2*(2*q) by ring, even_div_two]
  have hw : (4*q)%2 = 0 := by
    rw [show (4*q : V) = 2*(2*q) by ring, even_mod_two]
  simp [applyValue, hp, hs, hh, hw, frame]

lemma apply_left_one (q left right : V) :
    applyValue (4*q+2) left right = frame q (left/2) (left%2+2*(1+2*(right/2))) := by
  have hp : (4*q+2)-1 = 4*q+1 := by
    rw [show (4*q+2 : V) = (4*q+1)+1 by ring]; simp
  have hs : (4*q+1)/4 = q := div_mul_add' q 4 (by simp)
  have hh : (4*q+1)/2 = 2*q := by
    rw [show (4*q+1 : V) = 2*(2*q)+1 by ring, odd_div_two]
  have hw : (4*q+1)%2 = 1 := by
    rw [show (4*q+1 : V) = 2*(2*q)+1 by ring, odd_mod_two]
  simp [applyValue, hp, hs, hh, hw, frame]

lemma apply_left (b : Bool) (q left right : V) :
    applyValue (4*q+1+digit b) left right =
      frame q (left/2) (left%2+2*(digit b+2*(right/2))) := by
  cases b
  · simpa [digit] using apply_left_zero q left right
  · simpa [digit, show (4*q+1+1 : V) = 4*q+2 by ring] using apply_left_one q left right

lemma step_right (b : Bool) (q : V)
    (hrow : actionLookup q (digit b) = 4*q+3+digit b) (n left suffix : V) :
    stepValue (frame q left (bitPrefix b (n+1) suffix)) =
      frame q (2*left+digit b) (bitPrefix b n suffix) := by
  have hn : 4*q+3+digit (V := V) b ≠ 0 := by
    rw [show (4*q+3+digit b : V) = (4*q+2+digit b)+1 by ring]; simp
  unfold frame
  change genericStepValue actionLookup (cantor q (cantor left (bitPrefix b (n+1) suffix))) = _
  simp only [genericStepValue, first_cantor, second_cantor, bitPrefix_bit, hrow, if_neg hn]
  rw [apply_right, bitPrefix_half]
  rfl

lemma step_left (b : Bool) (q : V)
    (hrow : actionLookup q (digit b) = 4*q+1+digit b) (n left right : V) :
    stepValue (leftFrame q (bitPrefix b (n+1) left) right) =
      leftFrame q (bitPrefix b n left) (2*right+digit b) := by
  have hn : 4*q+1+digit (V := V) b ≠ 0 := by
    rw [show (4*q+1+digit b : V) = (4*q+digit b)+1 by ring]; simp
  unfold leftFrame frame
  change genericStepValue actionLookup _ = _
  simp only [genericStepValue, first_cantor, second_cantor, bitPrefix_bit, bitPrefix_half]
  rw [show digit (V := V) b+2*right = 2*right+digit b by ring, digit_mod_two, hrow, if_neg hn]
  rw [apply_left, digit_div_two]
  congr 2
  ring

def RightScan (b : Bool) (q n : V) : Prop := ∀ left suffix : V,
  runFrom n (frame q left (bitPrefix b n suffix)) = frame q (bitPrefix b n left) suffix
private instance rightScan_definable (b : Bool) (q : V) :
    𝚷₁-Predicate (RightScan b q) := by
  unfold RightScan
  definability

def LeftScan (b : Bool) (q n : V) : Prop := ∀ left right : V,
  runFrom n (leftFrame q (bitPrefix b n left) right) = leftFrame q left (bitPrefix b n right)
private instance leftScan_definable (b : Bool) (q : V) :
    𝚷₁-Predicate (LeftScan b q) := by
  unfold LeftScan
  definability

theorem scan_right (b : Bool) (q : V)
    (hrow : actionLookup q (digit b) = 4*q+3+digit b) (n left suffix : V) :
    runFrom n (frame q left (bitPrefix b n suffix)) = frame q (bitPrefix b n left) suffix := by
  have h : ∀ n : V, RightScan b q n := by
    intro n
    induction n using ISigma1.pi1_succ_induction
    · exact rightScan_definable b q
    case zero => intro left suffix; simp
    case succ n ih =>
      intro left suffix
      rw [runFrom_first, step_right b q hrow, ih, bitPrefix_push]
  exact h n left suffix

theorem scan_left (b : Bool) (q : V)
    (hrow : actionLookup q (digit b) = 4*q+1+digit b) (n left right : V) :
    runFrom n (leftFrame q (bitPrefix b n left) right) = leftFrame q left (bitPrefix b n right) := by
  have h : ∀ n : V, LeftScan b q n := by
    intro n
    induction n using ISigma1.pi1_succ_induction
    · exact leftScan_definable b q
    case zero => intro left right; simp
    case succ n ih =>
      intro left right
      rw [runFrom_first, step_left b q hrow, ih, bitPrefix_push]
  exact h n left right

/-- Finite actual-table evidence lifts to the same row in every model. -/
lemma right_row_of_nat (b : Bool) (q : Nat)
    (hrow : lookupNat literalRows 0 q b.toNat = 4*q+3+b.toNat) :
    actionLookup (q : V) (digit b) = 4*(q : V)+3+digit b := by
  have h := actionLookup_numeral (V := V) q b.toNat
  rw [hrow] at h
  cases b <;> simpa [digit, numeral_eq_natCast] using h

lemma left_row_of_nat (b : Bool) (q : Nat)
    (hrow : lookupNat literalRows 0 q b.toNat = 4*q+1+b.toNat) :
    actionLookup (q : V) (digit b) = 4*(q : V)+1+digit b := by
  have h := actionLookup_numeral (V := V) q b.toNat
  rw [hrow] at h
  cases b <;> simpa [digit, numeral_eq_natCast] using h

theorem scan_right_numeral (b : Bool) (q : Nat)
    (hrow : lookupNat literalRows 0 q b.toNat = 4*q+3+b.toNat) (n left suffix : V) :
    runFrom n (frame (q : V) left (bitPrefix b n suffix)) =
      frame (q : V) (bitPrefix b n left) suffix :=
  scan_right b (q : V) (right_row_of_nat b q hrow) n left suffix

theorem scan_left_numeral (b : Bool) (q : Nat)
    (hrow : lookupNat literalRows 0 q b.toNat = 4*q+1+b.toNat) (n left right : V) :
    runFrom n (leftFrame (q : V) (bitPrefix b n left) right) =
      leftFrame (q : V) left (bitPrefix b n right) :=
  scan_left b (q : V) (left_row_of_nat b q hrow) n left right

end SetTheory.BusyBeaver.ZFC.ArithmeticMachineUniformScansPerm252
