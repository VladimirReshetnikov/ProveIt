import BusyBeaver.ZFC.ArithmeticCantor
import BusyBeaver.ZFC.EnumPerm

/-! # The literal command-permuted enumerator's raw tail

NIP and DROP carry no argument, MP carries one, and AX carries y then x.
All inputs range over an arbitrary internal IOpen model. Raw candidate zero
is retained; a shifted nonempty program pointer must first subtract one.
This parser graph is a runtime prerequisite, not a consistency calibration.
-/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticCommandWordPerm222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

noncomputable def tailValue (z : V) : V :=
  if first z < 2 then second z
  else if first z = 2 then second (second z)
  else second (second (second z))

def tailDef : 𝚺₀.Semisentence 2 := .mkSigma
  “out z. ∃ op <⁺ z, !firstDef op z ∧ ∃ p <⁺ z, !secondDef p z ∧
    ((op < 2 ∧ out = p) ∨
     (¬ op < 2 ∧ ∃ r <⁺ z, !secondDef r p ∧
       ((op = 2 ∧ out = r) ∨ (op ≠ 2 ∧ !secondDef out r))))”

lemma first_le (z : V) : first z ≤ z := (projections_spec z).1
lemma second_le (z : V) : second z ≤ z := (projections_spec z).2.1
lemma second2_le (z : V) : second (second z) ≤ z :=
  le_trans (second_le _) (second_le z)

instance tail_defined : 𝚺₀-Function₁[V] tailValue via tailDef := .mk fun e => by
  classical
  by_cases hs : first (e 1) < 2
  · simp [tailDef, tailValue, first_le, second_le, hs]
  · have h2 : (2 : V) ≤ first (e 1) := le_of_not_gt hs
    have hz : (2 : V) ≤ e 1 := le_trans h2 (first_le _)
    by_cases hm : first (e 1) = 2 <;>
      simp [tailDef, tailValue, first_le, second_le, second2_le, hs, hm, h2, hz]

instance tail_definable : 𝚺₀-Function₁[V] tailValue := tail_defined.to_definable

theorem tail_total (z : V) : ∃! out, tailDef.val.Evalb ![out,z] := by simp

theorem tail_le (z : V) : tailValue z ≤ z := by
  by_cases hs : first z < 2
  · simpa [tailValue, hs] using second_le z
  · by_cases hm : first z = 2
    · simpa [tailValue, hs, hm] using second2_le z
    · simpa [tailValue, hs, hm] using le_trans (second_le _) (second2_le z)

@[simp] theorem tail_nip (r : V) : tailValue (cantor 0 r) = r := by
  simp [tailValue]

@[simp] theorem tail_drop (r : V) : tailValue (cantor 1 r) = r := by
  simp [tailValue]

@[simp] theorem tail_mp (x r : V) : tailValue (cantor 2 (cantor x r)) = r := by
  simp [tailValue]

@[simp] theorem tail_ax (c y x r : V) :
    tailValue (cantor (c+3) (cantor y (cantor x r))) = r := by
  have h3 : (3 : V) ≤ c+3 := le_add_self
  have h23 : (2 : V) < 3 := by
    simpa only [two_add_one_eq_three] using lt_add_one (2 : V)
  have h2 : (2 : V) < c+3 := lt_of_lt_of_le h23 h3
  simp [tailValue, not_lt_of_ge (le_of_lt h2), ne_of_gt h2]

/-- The ordinary adapter checks all four literal pack forms and arbitrary
rest pointers, rather than only the boot candidate. -/
theorem tail_pack_nat (cmd : EnumPerm.Cmd) (r : ℕ) :
    tailValue (EnumPerm.pack cmd r) = r := by
  cases cmd with
  | nip => simpa only [EnumPerm.pack, ← cantor_nat] using tail_nip r
  | drop => simpa only [EnumPerm.pack, ← cantor_nat] using tail_drop r
  | mp x =>
      have hm := tail_mp (V := ℕ) x r
      simp only [← numeral_two_eq_two (M := ℕ), Nat.numeral_eq] at hm
      simpa only [EnumPerm.pack, ← cantor_nat] using hm
  | ax c x y =>
      have ha := tail_ax (V := ℕ) c y x r
      simp only [← numeral_three_eq_three (M := ℕ), Nat.numeral_eq] at ha
      simpa only [EnumPerm.pack, ← cantor_nat] using ha

private theorem tail_nat_formula (z : ℕ) :
    tailValue z = if (EnumPerm.unP z).1 < 2 then (EnumPerm.unP z).2
      else if (EnumPerm.unP z).1 = 2 then (EnumPerm.unP (EnumPerm.unP z).2).2
      else (EnumPerm.unP (EnumPerm.unP (EnumPerm.unP z).2).2).2 := by
  simp only [tailValue, first_nat, second_nat]
  rfl

/-- All raw inputs agree, including zero and arbitrary dirty payloads. -/
theorem tail_nat (z : ℕ) : tailValue z = (EnumPerm.decode z).2 := by
  rw [tail_nat_formula]
  unfold EnumPerm.decode
  generalize hk : (EnumPerm.unP z).1 = op
  rcases op with _ | _ | _ | op <;> simp

end DiophantineConsistency.ArithmeticCommandWordPerm222
