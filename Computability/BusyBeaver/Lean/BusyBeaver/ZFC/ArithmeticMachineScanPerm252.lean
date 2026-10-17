import BusyBeaver.ZFC.ArithmeticTapePrefix254
import BusyBeaver.ZFC.ArithmeticMachineRunFromPerm252

/-!
An exact unbounded arithmetic scan of the actual frozen252 table.
Canonical state71 is numeric stateCode72. Its read1 transition writes1,
moves right, and returns to itself (positive action292). All model lengths
and both entire numeric tape halves are arbitrary. The proof asserts the
endpoint after n steps; the suffix may itself start with1, so no first-exit
claim is made. No register/dispatch or consistency simulation is asserted.
The literal table retains the Mira-Cult/Jeff/Wade and permutation attribution
recorded in TablePerm252.lean; no second machine table is introduced here.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticMachineScanPerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticTapePrefix254
open ArithmeticMachineGraphPerm252 ArithmeticMachineStepPerm252 ArithmeticMachineRunFromPerm252
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma odd_mod_two (x : V) : (2*x+1)%2 = 1 := by
  simpa only [mul_comm] using (mod_mul_add_of_lt x 2 (by simp : (1 : V) < 2))

lemma odd_div_two (x : V) : (2*x+1)/2 = x :=
  div_mul_add' x 2 (by simp : (1 : V) < 2)

/-- Decode a positive right/write1 action without restricting the tape. -/
lemma apply_right_one (q left right : V) :
    applyValue (4*q+4) left right = cantor q (cantor (2*left+1) (right/2)) := by
  have hp : (4*q+4)-1 = 4*q+3 := by
    rw [show (4*q+4 : V) = (4*q+3)+1 by ring]
    simp
  have h34 : (3 : V) < 4 := by
    have h := lt_succ_iff_le.mpr (le_rfl : (3 : V) ≤ 3)
    simpa only [show (3 : V)+1 = 4 by ring] using h
  have hs : (4*q+3)/4 = q := div_mul_add' q 4 h34
  have he : (4*q+3 : V) = 2*(2*q+1)+1 := by ring
  have hh : (4*q+3)/2 = 2*q+1 := by rw [he, odd_div_two]
  have hw : (4*q+3)%2 = 1 := by rw [he, odd_mod_two]
  simp [applyValue, hp, hs, hh, hw]

/-- The all-model static-key bridge is instantiated with the actual table. -/
lemma seekInc_action : actionLookup (72 : V) 1 = 292 := by
  have hl : lookupNat literalRows 0 72 1 = 292 := by decide
  have h := actionLookup_numeral (V := V) 72 1
  rw [hl] at h
  simpa [numeral_eq_natCast] using h

noncomputable def scanFrame (left right : V) : V := cantor 72 (cantor left right)

def scanFrameDef : 𝚺₁.Semisentence 3 := .mkSigma
  “out left right. ∃ tape, !ArithmeticCantor.pairDef tape left right ∧
    !ArithmeticCantor.pairDef out 72 tape”

instance scanFrame_defined : 𝚺₁-Function₂[V] scanFrame via scanFrameDef :=
  .mk fun e => by simp [scanFrameDef, scanFrame, numeral_eq_natCast]

private instance scanFrame_delta : 𝚫₁-Function₂[V] scanFrame :=
  scanFrame_defined.graph_delta.to_definable

private instance runFrom_delta : 𝚫₁-Function₂[V] runFrom := runFrom_defined_delta.to_definable

/-- One literal machine row moves exactly one low one between the halves. -/
theorem seekInc_step (n left suffix : V) :
    stepValue (scanFrame left (onesPrefix (n+1) suffix)) =
      scanFrame (2*left+1) (onesPrefix n suffix) := by
  have hn : (292 : V) ≠ 0 := by
    rw [show (292 : V) = 291+1 by ring]
    simp
  unfold scanFrame
  change genericStepValue actionLookup (cantor 72 (cantor left (onesPrefix (n+1) suffix))) = _
  simp only [genericStepValue, first_cantor, second_cantor, onesPrefix_bit,
    seekInc_action, if_neg hn]
  rw [show (292 : V) = 4*72+4 by ring, apply_right_one, onesPrefix_half]

/-- Universal tape parameters are a Pi1 predicate because runFrom is total
Delta1. This uses actual IΣ1 Pi1 induction, not unbounded Sigma1 induction. -/
def OnesScan (n : V) : Prop := ∀ left suffix,
  runFrom n (scanFrame left (onesPrefix n suffix)) = scanFrame (onesPrefix n left) suffix

private instance onesScan_definable : 𝚷₁-Predicate (OnesScan (V := V)) := by
  unfold OnesScan
  definability

theorem seekInc_scan (n left suffix : V) :
    runFrom n (scanFrame left (onesPrefix n suffix)) = scanFrame (onesPrefix n left) suffix := by
  have h : ∀ n : V, OnesScan n := by
    intro n
    induction n using ISigma1.pi1_succ_induction
    · exact onesScan_definable
    case zero => intro left suffix; simp
    case succ n ih =>
      intro left suffix
      rw [runFrom_first, seekInc_step, ih, onesPrefix_push]
  exact h n left suffix

theorem seekInc_scan_graph (out n left suffix : V) :
    runFromDef.val.Evalb ![out,n,scanFrame left (onesPrefix n suffix)] ↔
      out = scanFrame (onesPrefix n left) suffix := by
  simp [seekInc_scan]

end SetTheory.BusyBeaver.ZFC.ArithmeticMachineScanPerm252
