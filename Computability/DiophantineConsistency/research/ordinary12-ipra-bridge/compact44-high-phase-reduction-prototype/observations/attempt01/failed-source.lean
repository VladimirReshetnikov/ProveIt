import DiophantineConsistency.CompactSymbolicPorts
import DiophantineConsistency.ArithmeticPackingBlocks
import Mathlib.Data.List.GetD

/-! Reduce symbolic high-mask no-carry to the finitely supported phases. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactHighPhaseReduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticBinaryCarry ArithmeticWindowDigits ArithmeticMaskConstants ArithmeticPackingBlocks
open CompactHighPopulation CompactSymbolicPorts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The potentially nonzero high-mask phases below its padding tail. -/
def active (p : V) : Prop := p = 0 ∨ (1013 ≤ p ∧ p < 1023) ∨
  (1065 ≤ p ∧ p < 1074) ∨ p = 2195 ∨ p = 3296 ∨ p = 4393 ∨ p = 5495

theorem zero_natural (n : ℕ) (hn : n < 8792)
    (h : ¬ (n = 0 ∨ (1013 ≤ n ∧ n < 1023) ∨
      (1065 ≤ n ∧ n < 1074) ∨ n = 2195 ∨ n = 3296 ∨ n = 4393 ∨ n = 5495)) :
    highDigits.getD n 0 = 0 := by
  have cases : (1 ≤ n ∧ n < 1013) ∨ (1023 ≤ n ∧ n < 1065) ∨
      (1074 ≤ n ∧ n < 2195) ∨ (2196 ≤ n ∧ n < 3296) ∨
      (3297 ≤ n ∧ n < 4393) ∨ (4394 ≤ n ∧ n < 5495) ∨
      (5496 ≤ n ∧ n < 8792) := by omega
  rcases cases with hc | hc | hc | hc | hc | hc | hc <;>
    simp (disch := omega) only [highDigits, List.getD_append_right, List.getD_append,
      List.getD_replicate, List.length_replicate, List.length_cons, List.length_nil,
      List.length_append, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, List.getD_cons_zero]

theorem inactive_digit_zero (p : V) (hp : p < 8792) (h : ¬ active p) :
    dig 67 (highNat : V) p = 0 := by
  obtain ⟨n, rfl⟩ := eq_nat_of_lt_nat (n := 8792) hp
  have hn : n < 8792 := by exact_mod_cast hp
  have hnat : ¬ (n = 0 ∨ (1013 ≤ n ∧ n < 1023) ∨
      (1065 ≤ n ∧ n < 1074) ∨ n = 2195 ∨ n = 3296 ∨ n = 4393 ∨ n = 5495) := by
    intro hbad
    apply h
    unfold active
    exact_mod_cast hbad
  have hd := dig_ofDigits (V:=V) 67 highDigits digit_lt n
  change dig 67 (highNat : V) (n : V) = _ at hd
  rw [zero_natural n hn hnat] at hd
  simpa using hd

/-- A word with a zero padding tail is disjoint from the symbolic high mask
once each explicitly listed active phase has been checked. -/
theorem noCarry_of_active (z : V) (hz : z < Exp.exp (67*8807 : V))
    (hpadding : ∀ p < 8807, 8792 ≤ p → dig 67 z p = 0)
    (hactive : ∀ p < 8792, active p → NoCarry (dig 67 z p) (dig 67 (highNat : V) p)) :
    NoCarry z (highNat : V) := by
  let f : V → V := fun p => dig 67 z p
  let g : V → V := fun p => dig 67 (highNat : V) p
  letI : 𝚺₁-Function₁ f := by unfold f; definability
  letI : 𝚺₁-Function₁ g := by unfold g; definability
  have hf : bsum 67 f 8807 = z := by
    apply bsum_unique (f := f) (fun p _ => dig_lt 67 z p)
    exact ⟨hz, fun p _ => rfl⟩
  have hg : bsum 67 g 8807 = (highNat : V) := by
    apply bsum_unique (f := g) (fun p _ => dig_lt 67 (highNat : V) p)
    exact ⟨CompactHighPopulation.model_lt, fun p _ => rfl⟩
  have hn : ∀ p < 8807, NoCarry (f p) (g p) := by
    intro p hp
    by_cases hpad : 8792 ≤ p
    · rw [show f p = 0 from hpadding p hp hpad, noCarry_iff]
      intro i
      simp [fbit_le_one]
    · have hlt : p < 8792 := not_le.mp hpad
      by_cases ha : active p
      · exact hactive p hlt ha
      · rw [show g p = 0 from inactive_digit_zero p hlt ha, noCarry_iff]
        intro i
        simpa using fbit_le_one (f p) i
  have hs := bsum_noCarry (w := (67:V)) (f := f) (g := g) (n := (8807:V))
    (fun p _ => dig_lt 67 z p) (fun p _ => dig_lt 67 (highNat:V) p) hn
  rwa [hf, hg] at hs

#print axioms CompactHighPhaseReduction.zero_natural
#print axioms CompactHighPhaseReduction.inactive_digit_zero
#print axioms CompactHighPhaseReduction.noCarry_of_active
end CompactHighPhaseReduction
