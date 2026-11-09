import DiophantineConsistency.Source34.Source34Masks
import DiophantineConsistency.ArithmeticPackingBlocks
import Mathlib.Data.List.GetD

/-! # Reducing high-mask no-carry to the finitely many active phases, at the source34 ports

`Mixed121HighPhase` at the source34 tuple. `MF_native`
(`Source34Ports.highDigits`) has nonzero digits only at the phases

    0, 1000 + 2u, 1021 + 2u (u < 10), 2195, 3296, 4393, 5495

below its padding tail `8792..8799`; its top digit `8800` is zero. (121x8801:
the two field windows were the contiguous runs `1013..1022` and `1065..1074`.)
So a word whose tail digits `≥ 8792` vanish is carry-free against `MF_native`
as soon as each active phase is (`noCarry_of_active`). The parity-separated
windows are stated with an explicit index `u`, which is the form the field
lemmas consume. The window range `1000..1040` is checked digit by digit with
`decide +kernel`; the long zero runs by the list-append lemmas. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Source34HighPhase
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticBinaryCarry ArithmeticWindowDigits ArithmeticMaskConstants ArithmeticPackingBlocks
open Source34Ports
attribute [local irreducible] highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The potentially nonzero high-mask phases below its padding tail. -/
def active (p : V) : Prop := p = 0 ∨ (∃ u : ℕ, u < 10 ∧ p = ((1000+2*u : ℕ) : V)) ∨
  (∃ u : ℕ, u < 10 ∧ p = ((1021+2*u : ℕ) : V)) ∨ p = 2195 ∨ p = 3296 ∨ p = 4393 ∨ p = 5495

/-- The natural-number form of the inactive phases. -/
def ActiveNat (n : ℕ) : Prop := n = 0 ∨ (1000 ≤ n ∧ n < 1020 ∧ n % 2 = 0) ∨
  (1021 ≤ n ∧ n < 1041 ∧ n % 2 = 1) ∨ n = 2195 ∨ n = 3296 ∨ n = 4393 ∨ n = 5495

instance (n : ℕ) : Decidable (ActiveNat n) := by unfold ActiveNat; infer_instance

theorem window_zero : ∀ m < 41, ¬ ActiveNat (1000+m) → highDigits.getD (1000+m) 0 = 0 := by
  decide +kernel

theorem zero_natural (n : ℕ) (hn : n < 8792) (h : ¬ ActiveNat n) :
    highDigits.getD n 0 = 0 := by
  have cases : (1 ≤ n ∧ n < 1000) ∨ (1000 ≤ n ∧ n < 1041) ∨
      (1041 ≤ n ∧ n < 2195) ∨ (2196 ≤ n ∧ n < 3296) ∨
      (3297 ≤ n ∧ n < 4393) ∨ (4394 ≤ n ∧ n < 5495) ∨
      (5496 ≤ n ∧ n < 8792) := by unfold ActiveNat at h; omega
  rcases cases with hc | hc | hc | hc | hc | hc | hc
  · simp (disch := (simp only [List.length_replicate, List.length_cons, List.length_nil,
      List.length_append, Nat.reduceAdd]; omega)) only [highDigits, highInit, List.getD_append_right,
      List.getD_append, List.length_replicate, List.length_cons, List.length_nil,
      List.length_append, Nat.reduceAdd]
    exact List.getD_replicate (0 : ℕ) (by omega)
  · obtain ⟨m, hm, rfl⟩ : ∃ m, m < 41 ∧ n = 1000+m := ⟨n-1000, by omega, by omega⟩
    exact window_zero m hm h
  all_goals
    simp (disch := (simp only [track, List.length_replicate, List.length_cons, List.length_nil,
      List.length_append, Nat.reduceAdd]; omega)) only [highDigits, highInit, track,
      List.getD_append_right, List.getD_append, List.length_replicate, List.length_cons,
      List.length_nil, List.length_append, Nat.reduceAdd]
    exact List.getD_replicate (0 : ℕ) (by omega)

theorem inactive_digit_zero (p : V) (hp : p < 8792) (h : ¬ active p) :
    dig 121 (highNat : V) p = 0 := by
  obtain ⟨n, rfl⟩ := eq_nat_of_lt_nat (n := 8792) hp
  have hn : n < 8792 := by exact_mod_cast hp
  have hnat : ¬ ActiveNat n := by
    intro hbad
    apply h
    unfold active
    unfold ActiveNat at hbad
    rcases hbad with h0 | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | h4 | h5 | h6 | h7
    · left; exact_mod_cast h0
    · exact Or.inr (Or.inl ⟨(n-1000)/2, by omega, by congr 1; omega⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨(n-1021)/2, by omega, by congr 1; omega⟩))
    · right; right; right; left; exact_mod_cast h4
    · right; right; right; right; left; exact_mod_cast h5
    · right; right; right; right; right; left; exact_mod_cast h6
    · right; right; right; right; right; right; exact_mod_cast h7
  have hd := dig_ofDigits (V:=V) 121 highDigits Source34Masks.high_digit_lt n
  rw [zero_natural n hn hnat] at hd
  rw [Source34Masks.highNat_eq]
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
    have hlt : (highNat : V) < Exp.exp (121*8801 : V) := Source34Masks.model_high_lt
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

#print axioms Source34HighPhase.window_zero
#print axioms Source34HighPhase.zero_natural
#print axioms Source34HighPhase.inactive_digit_zero
#print axioms Source34HighPhase.noCarry_of_active
end Source34HighPhase
