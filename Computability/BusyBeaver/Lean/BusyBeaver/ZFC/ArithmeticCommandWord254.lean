import BusyBeaver.ZFC.CommandWord254
import BusyBeaver.ZFC.ArithmeticCantor

/-!
Bounded graphs for actual raw-command tail replacement. The input z here is a
RAW Enum254 candidate/command code; a nonempty shifted word must first subtract
one. Empty shifted word0 is not executed as raw candidate0.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticCommandWord254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

noncomputable def tailValue (z : V) : V :=
  if first z < 3 then second (second z) else second (second (second (second z)))

def tailDef : 𝚺₀.Semisentence 2 := .mkSigma
  “out z. ∃ op <⁺ z, !firstDef op z ∧
    ∃ p <⁺ z, !secondDef p z ∧ ∃ r <⁺ z, !secondDef r p ∧
    ((op < 3 ∧ out = r) ∨ (¬ op < 3 ∧ ∃ s <⁺ z, !secondDef s r ∧ !secondDef out s))”

lemma first_le (z : V) : first z ≤ z := (projections_spec z).1
lemma second_le (z : V) : second z ≤ z := (projections_spec z).2.1
lemma second2_le (z : V) : second (second z) ≤ z := le_trans (second_le _) (second_le z)
lemma second3_le (z : V) : second (second (second z)) ≤ z := le_trans (second_le _) (second2_le z)

instance tail_defined : 𝚺₀-Function₁[V] tailValue via tailDef := .mk fun e => by
  by_cases h : first (e 1) < 3
  · simp [tailDef, tailValue, first_le, second_le, second2_le, h]
  · have hn : 3 ≤ first (e 1) := le_of_not_gt h
    simp [tailDef, tailValue, first_le, second_le, second2_le, second3_le, h, hn]

theorem tailValue_le (z : V) : tailValue z ≤ z := by
  by_cases h : first z < 3
  · simpa [tailValue, h] using second2_le z
  · simpa [tailValue, h] using le_trans (second_le _) (second3_le z)

noncomputable def replaceValue (z rest : V) : V :=
  let op := first z
  let p := second z
  let x := first p
  let r := second p
  if op < 3 then cantor op (cantor x rest)
  else cantor op (cantor x (cantor (first r) (cantor (first (second r)) rest)))

def replaceDef : 𝚺₀.Semisentence 3 := .mkSigma
  “out z rest. ∃ op <⁺ z, !firstDef op z ∧ ∃ p <⁺ z, !secondDef p z ∧
    ∃ x <⁺ z, !firstDef x p ∧ ∃ r <⁺ z, !secondDef r p ∧
    ((op < 3 ∧ ∃ a <⁺ out, !ArithmeticCantor.pairDef a x rest ∧ !ArithmeticCantor.pairDef out op a) ∨
     (¬ op < 3 ∧ ∃ y <⁺ z, !firstDef y r ∧ ∃ s <⁺ z, !secondDef s r ∧
       ∃ u <⁺ z, !firstDef u s ∧
       ∃ a <⁺ out, !ArithmeticCantor.pairDef a u rest ∧ ∃ b <⁺ out, !ArithmeticCantor.pairDef b y a ∧
       ∃ c <⁺ out, !ArithmeticCantor.pairDef c x b ∧ !ArithmeticCantor.pairDef out op c))”

lemma short_output_bounds (out op x rest : V) :
    (cantor x rest ≤ out ∧ out = cantor op (cantor x rest)) ↔
    out = cantor op (cantor x rest) := by
  constructor
  · exact fun h => h.2
  · intro h
    rw [h]
    exact ⟨(components_le _ _).2, rfl⟩

lemma long_output_bounds (out op x y u rest : V) :
    (cantor u rest ≤ out ∧ cantor y (cantor u rest) ≤ out ∧
      cantor x (cantor y (cantor u rest)) ≤ out ∧
      out = cantor op (cantor x (cantor y (cantor u rest)))) ↔
    out = cantor op (cantor x (cantor y (cantor u rest))) := by
  constructor
  · exact fun h => h.2.2.2
  · intro h
    rw [h]
    have hc : cantor x (cantor y (cantor u rest)) ≤
        cantor op (cantor x (cantor y (cantor u rest))) := (components_le _ _).2
    have hb := le_trans (components_le x (cantor y (cantor u rest))).2 hc
    have ha := le_trans (components_le y (cantor u rest)).2 hb
    exact ⟨ha,hb,hc,rfl⟩

instance replace_defined : 𝚺₀-Function₂[V] replaceValue via replaceDef := .mk fun e => by
  have hx : first (second (e 1)) ≤ e 1 := le_trans (first_le _) (second_le _)
  have hy : first (second (second (e 1))) ≤ e 1 := le_trans (first_le _) (second2_le _)
  have hu : first (second (second (second (e 1)))) ≤ e 1 := le_trans (first_le _) (second3_le _)
  by_cases h : first (e 1) < 3
  · simp [replaceDef, replaceValue, first_le, second_le, second2_le, hx, h, short_output_bounds]
  · have hn : 3 ≤ first (e 1) := le_of_not_gt h
    simp [replaceDef, replaceValue, first_le, second_le, second2_le, second3_le, hx, hy, hu, h, hn, long_output_bounds]

@[simp] theorem tailValue_nat (z : Nat) : tailValue z = CommandWord254.tail z := by
  rw [CommandWord254.tail_formula]
  unfold tailValue CommandWord254.tailFormula
  rw [← numeral_three_eq_three]
  simp only [first_nat, second_nat, Nat.numeral_eq]

@[simp] theorem replaceValue_nat (z rest : Nat) :
    replaceValue z rest = CommandWord254.replaceRest z rest := by
  rw [CommandWord254.replaceRest_formula]
  unfold replaceValue CommandWord254.replaceRestFormula
  rw [← numeral_three_eq_three]
  simp only [first_nat, second_nat, Nat.numeral_eq, cantor_nat]

end SetTheory.BusyBeaver.ZFC.ArithmeticCommandWord254
