import BusyBeaver.ZFC.ArithmeticMachineGraphPerm252

/-!
A fixed bounded graph for an entire encoded frozen252 configuration step.
Configuration code P(stateCode,P(leftHalf,rightHalf)) retains the tape after a
halt. Action0 means absent lookup and preserves the whole configuration.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticMachineStepPerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticRow254 ArithmeticHistory254
open ArithmeticMachinePerm252 ArithmeticMachineGraphPerm252

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

noncomputable def applyValue (action left right : V) : V :=
  let z := action - 1
  let state := z / 4
  let move := (z / 2) % 2
  let write := z % 2
  if move = 0 then
    cantor state (cantor (left / 2) (left % 2 + 2 * (write + 2 * (right / 2))))
  else cantor state (cantor (2 * left + write) (right / 2))

/-- Predecessor, quotient and remainder witnesses are bounded by their own
input; the final paired tape tail is bounded by the output. -/
def applyDef : 𝚺₀.Semisentence 4 := .mkSigma
  “out action left right.
    ∃ z <⁺ action, !subDef z action 1 ∧
    ∃ state <⁺ action, !divDef state z 4 ∧
    ∃ half <⁺ action, !divDef half z 2 ∧
    ∃ move <⁺ action, !remDef move half 2 ∧
    ∃ write <⁺ action, !remDef write z 2 ∧
    ∃ leftQ <⁺ left, !divDef leftQ left 2 ∧
    ∃ leftB <⁺ left, !remDef leftB left 2 ∧
    ∃ rightQ <⁺ right, !divDef rightQ right 2 ∧
    ∃ tape <⁺ out, !ArithmeticCantor.pairDef out state tape ∧
      ((move = 0 ∧ !ArithmeticCantor.pairDef tape leftQ (leftB + 2 * (write + 2 * rightQ))) ∨
       (move ≠ 0 ∧ !ArithmeticCantor.pairDef tape (2 * left + write) rightQ))”

@[simp] lemma bounded_output_pair (out state left right : V) :
    (cantor left right ≤ out ∧ out = cantor state (cantor left right)) ↔
    out = cantor state (cantor left right) := by
  constructor
  · exact fun h => h.2
  · intro h
    rw [h]
    exact ⟨(components_le _ _).2, rfl⟩

instance apply_defined : 𝚺₀-Function₃[V] applyValue via applyDef := .mk fun e => by
  have hz : e 1 - 1 ≤ e 1 := tsub_le_self
  have hs : (e 1 - 1) / 4 ≤ e 1 := le_trans (div_le _ _) hz
  have hh : (e 1 - 1) / 2 ≤ e 1 := le_trans (div_le _ _) hz
  have hm : ((e 1 - 1) / 2) % 2 ≤ e 1 := le_trans (mod_le _ _) hh
  have hw : (e 1 - 1) % 2 ≤ e 1 := le_trans (mod_le _ _) hz
  rcases mod_two ((e 1 - 1) / 2) with h | h
  · simp [applyDef, applyValue, hz, hs, hh, hw, h]
  · have hm1 : 1 ≤ e 1 := by simpa only [h] using hm
    simp [applyDef, applyValue, hz, hs, hh, hm1, hw, h]

noncomputable def genericStepValue (lookup : V → V → V) (input : V) : V :=
  let state := first input
  let tape := second input
  let left := first tape
  let right := second tape
  let action := lookup state (right % 2)
  if action = 0 then input else applyValue action left right

def genericStepDef (lookupGraph : 𝚺₀.Semisentence 3) : 𝚺₀.Semisentence 2 := .mkSigma
  “out input.
    ∃ state <⁺ input, ∃ tape <⁺ input, !ArithmeticCantor.pairDef input state tape ∧
    ∃ left <⁺ input, ∃ right <⁺ input, !ArithmeticCantor.pairDef tape left right ∧
    ∃ bit <⁺ input, !remDef bit right 2 ∧
    ∃ action <⁺ !!(Semiterm.Operator.numeral ℒₒᵣ 1012),
      !lookupGraph action state bit ∧
      ((action = 0 ∧ out = input) ∨ (action ≠ 0 ∧ !applyDef out action left right))”

theorem generic_step_defined (lookup : V → V → V) (lookupGraph : 𝚺₀.Semisentence 3)
    (hgraph : 𝚺₀-Function₂[V] lookup via lookupGraph)
    (hbound : ∀ q bit, lookup q bit ≤ ORingStructure.numeral 1012) :
    𝚺₀-Function₁[V] (genericStepValue lookup) via genericStepDef lookupGraph := .mk fun e => by
  classical
  simp only [genericStepDef]
  simp [hgraph.iff]
  rw [payload_fields_flat]
  have hr : second (second (e 1)) ≤ e 1 :=
    le_trans (projections_spec (second (e 1))).2.1 (projections_spec (e 1)).2.1
  have hb : second (second (e 1)) % 2 ≤ e 1 := le_trans (mod_le _ _) hr
  by_cases h : lookup (first (e 1)) (second (second (e 1)) % 2) = 0
  · simp [genericStepValue, hb, h]
  · simp [genericStepValue, hb, hbound, h]

noncomputable def stepValue (input : V) : V := genericStepValue actionLookup input

def stepDef : 𝚺₀.Semisentence 2 := genericStepDef actionLookupDef

instance step_defined : 𝚺₀-Function₁[V] stepValue via stepDef :=
  generic_step_defined actionLookup actionLookupDef actionLookup_defined actionLookup_bound

theorem step_total (input : V) : ∃! out, stepDef.val.Evalb ![out,input] := by simp

def encodeConfig (u : NumericConfig) : Nat := Code254.P u.state (Code254.P u.left u.right)

def decodeConfig (code : Nat) : NumericConfig :=
  let p := SetTheory.Cantor.ofNat code
  let tape := SetTheory.Cantor.ofNat p.2
  ⟨p.1,tape.1,tape.2⟩

@[simp] theorem decode_encode (u : NumericConfig) : decodeConfig (encodeConfig u) = u := by
  simp [decodeConfig, encodeConfig, Code254.unP_P]

@[simp] theorem encode_decode (code : Nat) : encodeConfig (decodeConfig code) = code := by
  simp [decodeConfig, encodeConfig, Code254.P, SetTheory.Cantor.toNat_ofNat]

/-- Computable native step on all natural codes, including invalid states. -/
def nativeStep (code : Nat) : Nat := encodeConfig (numericStep machinePerm252 (decodeConfig code))

lemma lookupNat_absent (rows : List (Nat × Nat)) (start q bit : Nat)
    (hq : q ≤ start ∨ start + rows.length < q) : lookupNat rows start q bit = 0 := by
  induction rows generalizing start with
  | nil => rfl
  | cons row rows ih =>
    have hn : q ≠ start + 1 := by simp only [List.length_cons] at hq; omega
    have ht : q ≤ start + 1 ∨ start + 1 + rows.length < q := by
      simp only [List.length_cons] at hq; omega
    simp only [lookupNat, if_neg hn]
    exact ih (start + 1) ht

lemma lookupNat_zero (bit : Nat) : lookupNat literalRows 0 0 bit = 0 :=
  lookupNat_absent _ _ _ _ (.inl (by omega))

lemma lookupNat_invalid (q bit : Nat) (hq : 252 < q) : lookupNat literalRows 0 q bit = 0 :=
  lookupNat_absent _ _ _ _ (.inr (by simpa only [literalRows_length, Nat.zero_add] using hq))

lemma actionNumber_decode {n : Nat} (a : Action n) :
    (actionNumber a - 1) / 4 = stateCode a.next ∧
    ((actionNumber a - 1) / 2) % 2 = (if a.move = .right then 1 else 0) ∧
    (actionNumber a - 1) % 2 = a.write.toNat := by
  cases a with
  | mk write move next =>
    cases write <;> cases move <;> simp [actionNumber] <;> omega

lemma actionNumber_positive {n : Nat} (a : Action n) : 0 < actionNumber a := by
  unfold actionNumber
  omega

lemma foundation_sub_projection_nat (a b : Nat) :
    @Sub.sub Nat Arithmetic.instSub_foundation a b = a - b := by
  change Arithmetic.sub a b = a - b
  exact foundation_sub_nat a b

lemma applyValue_nat_formula (a l r : Nat) : applyValue a l r =
    (if ((a - 1) / 2) % 2 = 0 then
      Code254.P ((a - 1) / 4)
        (Code254.P (l / 2) (l % 2 + 2 * ((a - 1) % 2 + 2 * (r / 2))))
    else Code254.P ((a - 1) / 4)
      (Code254.P (2 * l + (a - 1) % 2) (r / 2))) := by
  unfold applyValue
  rw [← numeral_four_eq_four, ← numeral_two_eq_two]
  simp only [Nat.numeral_eq, HSub.hSub, HDiv.hDiv, HMod.hMod]
  simp only [foundation_sub_projection_nat, foundation_div_nat, foundation_rem_nat, cantor_nat]
  rfl

lemma applyValue_nat {n : Nat} (a : Action n) (u : NumericConfig) :
    applyValue (actionNumber a) u.left u.right = encodeConfig (applyAction a u) := by
  rw [applyValue_nat_formula]
  rcases actionNumber_decode a with ⟨hs, hm, hw⟩
  rw [hs, hm, hw]
  cases hmove : a.move <;> simp [applyAction, encodeConfig, hmove]

lemma native_read_bit (r : Nat) : (decide (r % 2 = 1)).toNat = r % 2 := by
  have h := Nat.mod_lt r (by decide : 0 < 2)
  by_cases hz : r % 2 = 0
  · simp [hz]
  · have ho : r % 2 = 1 := by omega
    simp [ho]

/-- The same encoded step equals the imported actual-machine numeric step for
EVERY numeric configuration, including halted and invalid positive states. -/
theorem stepValue_nat_encoded (u : NumericConfig) :
    stepValue (encodeConfig u) = encodeConfig (numericStep machinePerm252 u) := by
  have henc : encodeConfig u = (cantor u.state (cantor u.left u.right) : Nat) := by
    simp only [encodeConfig, cantor_nat]
  rw [henc]
  change genericStepValue actionLookup (cantor u.state (cantor u.left u.right)) = _
  unfold genericStepValue
  rw [← numeral_two_eq_two]
  simp only [Nat.numeral_eq, first_cantor, second_cantor, HMod.hMod]
  simp only [foundation_rem_nat, actionLookup_nat]
  by_cases hz : u.state = 0
  · rw [hz, lookupNat_zero, if_pos rfl, numericStep_halted machinePerm252 u hz]
    simp only [cantor_nat, encodeConfig, hz]
  by_cases hbig : 252 < u.state
  · rw [lookupNat_invalid _ _ hbig, if_pos rfl, numericStep_invalid machinePerm252 u hbig]
    simp only [cantor_nat, encodeConfig]
  have hfin : u.state - 1 < 252 := by omega
  let q : Fin 252 := ⟨u.state - 1, hfin⟩
  let bit : Bool := decide (u.right % 2 = 1)
  have hlookup : lookupNat literalRows 0 u.state (u.right % 2) =
      actionNumber (machinePerm252.transition q bit) := by
    have h := literal_lookup_actual q bit
    have hq : q.val + 1 = u.state := by dsimp [q]; omega
    simpa only [hq, bit, native_read_bit] using h
  rw [hlookup, if_neg (Nat.ne_of_gt (actionNumber_positive _)), applyValue_nat]
  unfold numericStep actionAt
  simp [hz, hfin, q, bit]

/-- All standard codes are included, since Cantor configuration coding is
bijective; this is not restricted to encodings of valid active states. -/
theorem stepValue_nat (code : Nat) : stepValue code = nativeStep code := by
  calc
    stepValue code = stepValue (encodeConfig (decodeConfig code)) := by rw [encode_decode]
    _ = encodeConfig (numericStep machinePerm252 (decodeConfig code)) := stepValue_nat_encoded _
    _ = nativeStep code := rfl

theorem stepDef_nat (out input : Nat) : stepDef.val.Evalb ![out,input] ↔ out = nativeStep input := by
  simp [stepValue_nat]

end SetTheory.BusyBeaver.ZFC.ArithmeticMachineStepPerm252
