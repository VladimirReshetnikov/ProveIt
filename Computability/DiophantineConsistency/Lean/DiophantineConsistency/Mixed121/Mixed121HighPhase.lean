import DiophantineConsistency.Mixed121.Mixed121Masks
import DiophantineConsistency.ArithmeticPackingBlocks
import Mathlib.Data.List.GetD

/-! # Reducing high-mask no-carry to the finitely many active phases, at 121x8801

The 121x8801 counterpart of Compact44's `CompactHighPhaseReduction`.
`MF_native` (`Mixed121Ports.highDigits`) has nonzero digits only at the phases

    0, 1013..1022, 1065..1074, 2195, 3296, 4393, 5495

below its padding tail `8792..8799`; its top digit `8800` is zero. So a word
whose tail digits `≥ 8792` vanish is carry-free against `MF_native` as soon as
each active phase is (`noCarry_of_active`). Compact44's second run of ones
has nine cells and its tail fifteen; here they have ten and eight. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Mixed121HighPhase
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticBinaryCarry ArithmeticWindowDigits ArithmeticMaskConstants ArithmeticPackingBlocks
open Mixed121Ports
attribute [local irreducible] highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The potentially nonzero high-mask phases below its padding tail. -/
def active (p : V) : Prop := p = 0 ∨ (1013 ≤ p ∧ p < 1023) ∨
  (1065 ≤ p ∧ p < 1075) ∨ p = 2195 ∨ p = 3296 ∨ p = 4393 ∨ p = 5495

theorem zero_natural (n : ℕ) (hn : n < 8792)
    (h : ¬ (n = 0 ∨ (1013 ≤ n ∧ n < 1023) ∨
      (1065 ≤ n ∧ n < 1075) ∨ n = 2195 ∨ n = 3296 ∨ n = 4393 ∨ n = 5495)) :
    highDigits.getD n 0 = 0 := by
  have cases : (1 ≤ n ∧ n < 1013) ∨ (1023 ≤ n ∧ n < 1065) ∨
      (1075 ≤ n ∧ n < 2195) ∨ (2196 ≤ n ∧ n < 3296) ∨
      (3297 ≤ n ∧ n < 4393) ∨ (4394 ≤ n ∧ n < 5495) ∨
      (5496 ≤ n ∧ n < 8792) := by omega
  rcases cases with hc | hc | hc | hc | hc | hc | hc <;>
    simp (disch := (simp only [List.length_replicate, List.length_cons, List.length_nil,
      List.length_append, Nat.reduceAdd]; omega)) only [highDigits, highInit, List.getD_append_right,
      List.getD_append, List.length_replicate, List.length_cons, List.length_nil,
      List.length_append, Nat.reduceAdd] <;> exact List.getD_replicate (0 : ℕ) (by omega)

theorem inactive_digit_zero (p : V) (hp : p < 8792) (h : ¬ active p) :
    dig 121 (highNat : V) p = 0 := by
  obtain ⟨n, rfl⟩ := eq_nat_of_lt_nat (n := 8792) hp
  have hn : n < 8792 := by exact_mod_cast hp
  have hnat : ¬ (n = 0 ∨ (1013 ≤ n ∧ n < 1023) ∨
      (1065 ≤ n ∧ n < 1075) ∨ n = 2195 ∨ n = 3296 ∨ n = 4393 ∨ n = 5495) := by
    intro hbad
    apply h
    unfold active
    exact_mod_cast hbad
  have hd := dig_ofDigits (V:=V) 121 highDigits Mixed121Masks.high_digit_lt n
  rw [zero_natural n hn hnat] at hd
  rw [Mixed121Masks.highNat_eq]
  simpa only [Nat.cast_ofNat, Nat.cast_zero] using hd

/-- A word with a zero padding tail is disjoint from `MF_native` once each
explicitly listed active phase has been checked. -/
theorem noCarry_of_active (z : V) (hz : z < Exp.exp (121*8801 : V))
    (hpadding : ∀ p < 8801, 8792 ≤ p → dig 121 z p = 0)
    (hactive : ∀ p < 8792, active p → NoCarry (dig 121 z p) (dig 121 (highNat : V) p)) :
    NoCarry z (highNat : V) := by
  let f : V → V := fun p => dig 121 z p
  let g : V → V := fun p => dig 121 (highNat : V) p
  letI : 𝚺₁-Function₁ f := by unfold f; definability
  letI : 𝚺₁-Function₁ g := by unfold g; definability
  have hf : bsum 121 f 8801 = z := by
    apply bsum_unique (f := f) (fun p _ => dig_lt 121 z p)
    exact ⟨hz, fun p _ => rfl⟩
  have hg : bsum 121 g 8801 = (highNat : V) := by
    apply bsum_unique (f := g) (fun p _ => dig_lt 121 (highNat : V) p)
    have hlt : (highNat : V) < Exp.exp (121*8801 : V) := Mixed121Masks.model_high_lt
    exact ⟨hlt, fun p _ => rfl⟩
  have hn : ∀ p < 8801, NoCarry (f p) (g p) := by
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
        simp [fbit_le_one]
  have hs := bsum_noCarry (w := (121:V)) (f := f) (g := g) (n := (8801:V))
    (fun p _ => dig_lt 121 z p) (fun p _ => dig_lt 121 (highNat:V) p) hn
  rwa [hf, hg] at hs

#print axioms Mixed121HighPhase.zero_natural
#print axioms Mixed121HighPhase.inactive_digit_zero
#print axioms Mixed121HighPhase.noCarry_of_active
end Mixed121HighPhase
