import DiophantineConsistency.Compact44.CompactWordCellClient
import DiophantineConsistency.Compact44.HighMaskLocal
import DiophantineConsistency.ArithmeticPackingBlocks

/-! Exploratory clean target block: this packs only the two local occupied
aggregates, not the full kernel product or its carries. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace CompactWordTargetNoCarry
open DiophantineConsistency
open DiophantineConsistency.ArithmeticStandardCasts DiophantineConsistency.ArithmeticWindowDigits
  DiophantineConsistency.ArithmeticBinaryCarry DiophantineConsistency.ArithmeticPackingBlocks
  DiophantineConsistency.ArithmeticRepunit
open CompactWordCellClient CompactMarkedTransport CompactSymbolicPorts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
attribute [local irreducible] highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem fbit_cast (a i : ℕ) : fbit (a : V) (i : V) = ((a / 2^i % 2 : ℕ) : V) := by
  rw [fbit_eq_div, cast_exp, ← cast_div]
  exact (cast_mod (a / 2^i) 2).symm

private theorem noCarry_cast {a b : ℕ} (h : a &&& b = 0) : NoCarry (a : V) (b : V) := by
  intro i hi
  have hi' : i < ((a + b + 1 : ℕ) : V) := by push_cast; exact hi
  obtain ⟨k, rfl⟩ := eq_nat_of_lt_nat hi'
  rw [fbit_cast, fbit_cast]
  have hk : a / 2^k % 2 + b / 2^k % 2 ≤ 1 := by
    have h1 := Nat.testBit_and a b k
    rw [h, Nat.zero_testBit, Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq] at h1
    rcases Nat.mod_two_eq_zero_or_one (a / 2^k) with ha | ha <;>
      rcases Nat.mod_two_eq_zero_or_one (b / 2^k) with hb | hb <;> simp_all
  exact_mod_cast hk

def occupied : V := 1 + Exp.exp 51
def targetMask : V := Exp.exp 51 - 2

theorem occupied_cast : (occupied : V) = (((2^51 + 1 : ℕ)) : V) := by
  unfold occupied
  rw [show Exp.exp (51 : V) = ((2^51 : ℕ) : V) by simpa using cast_exp (V:=V) 51]
  push_cast
  ring

theorem mask_cast : (targetMask : V) = (((2^51 - 2 : ℕ)) : V) := by
  have h : (2 : ℕ) ≤ 2^51 := by norm_num
  have hn : (2^51 - 2 : ℕ) + 2 = 2^51 := Nat.sub_add_cancel h
  have hv : (((2^51 - 2 : ℕ)) : V) + 2 = ((2^51 : ℕ) : V) := by exact_mod_cast hn
  rw [← cast_exp (V:=V) 51] at hv
  exact (eq_tsub_of_add_eq hv).symm

theorem occupied_noCarry : NoCarry (occupied : V) targetMask := by
  rw [occupied_cast, mask_cast]
  apply noCarry_cast
  decide

theorem occupied_lt : (occupied : V) < Exp.exp 67 := by
  rw [occupied_cast, show Exp.exp (67 : V) = ((2^67 : ℕ) : V) by simpa using cast_exp (V:=V) 67]
  exact_mod_cast (show (2^51 + 1 : ℕ) < 2^67 by norm_num)

/-- Two target digits, with all other 67-bit digits equal to zero. -/
def targetDigit (k : V) : V := if k = 4393 ∨ k = 5495 then occupied else 0

instance targetDigit_definable : 𝚺₁-Function₁[V] targetDigit := by
  have hR : 𝚺₁.Definable (fun v : Fin 2 → V =>
      ((v 1 = 4393 ∨ v 1 = 5495) ∧ v 0 = occupied) ∨
      ((v 1 ≠ 4393 ∧ v 1 ≠ 5495) ∧ v 0 = 0)) := by
    unfold occupied
    definability
  apply hR.of_iff
  intro v
  unfold targetDigit
  by_cases h1 : v 1 = 4393 <;> by_cases h2 : v 1 = 5495 <;> simp [h1, h2]

def maskDigit (k : V) : V := dig 67 (highNat : V) k
instance maskDigit_definable : 𝚺₁-Function₁[V] maskDigit := by
  unfold maskDigit
  definability

theorem targetDigit_lt (k : V) : targetDigit k < Exp.exp 67 := by
  unfold targetDigit
  split
  · exact occupied_lt
  · exact exp_pos _

theorem targetDigit_noCarry (k : V) : NoCarry (targetDigit k) (maskDigit k) := by
  by_cases h1 : k = 4393
  · subst k
    simpa [targetDigit, maskDigit, HighMaskLocal.target4393, targetMask] using (occupied_noCarry (V:=V))
  by_cases h2 : k = 5495
  · subst k
    simpa [targetDigit, maskDigit, h1, HighMaskLocal.target5495, targetMask] using (occupied_noCarry (V:=V))
  have hz : targetDigit k = 0 := by simp [targetDigit, h1, h2]
  rw [hz, noCarry_iff]
  intro i
  simp

/-- The sparse block carrying the two occupied clause digits. -/
def targetBlock : V := bsum 67 targetDigit 8807

theorem targetBlock_digits (k : V) (hk : k < 8807) :
    dig 67 (targetBlock : V) k = targetDigit k :=
  dig_bsum (fun j _ => targetDigit_lt j) hk

theorem targetBlock_lt : (targetBlock : V) < Exp.exp (67*8807) :=
  bsum_lt (fun j _ => targetDigit_lt j)

theorem highNat_lt : (highNat : V) < Exp.exp (67*8807) := by
  unfold highNat
  exact CompactHighPopulation.model_lt

theorem targetBlock_noCarry : NoCarry (targetBlock : V) (highNat : V) := by
  have hmask : bsum 67 (maskDigit : V → V) 8807 = (highNat : V) := by
    apply bsum_unique (f := (maskDigit : V → V)) (fun j _ => dig_lt 67 (highNat:V) j)
    exact ⟨highNat_lt, fun j _ => rfl⟩
  have hc := bsum_noCarry (w := (67:V)) (f := targetDigit) (g := maskDigit) (n := 8807)
    (fun j _ => targetDigit_lt j) (fun j _ => dig_lt 67 (highNat:V) j)
    (fun j _ => targetDigit_noCarry j)
  unfold targetBlock
  rwa [hmask] at hc

/-- Repeating this sparse clean target block preserves no-carry at every
model length. This is not an identity for the actual packed product. -/
theorem repeated_noCarry {a b : V} (ha : a < Exp.exp (67*8807))
    (hb : b < Exp.exp (67*8807)) (h : NoCarry a b) (N : V) :
    NoCarry (a * rep (67*8807) N) (b * rep (67*8807) N) := by
  letI : 𝚺₁-Function₁ (fun _ : V => a) := by definability
  letI : 𝚺₁-Function₁ (fun _ : V => b) := by definability
  have hh := bsum_noCarry (w := (67*8807:V)) (n := N)
    (f := fun _ => a) (g := fun _ => b)
    (fun _ _ => ha) (fun _ _ => hb) (fun _ _ => h)
  rwa [bsum_const_rep ha, bsum_const_rep hb] at hh

theorem repeated_target_noCarry (N : V) :
    NoCarry ((targetBlock : V) * rep (67*8807) N) ((highNat : V) * rep (67*8807) N) :=
  repeated_noCarry targetBlock_lt highNat_lt targetBlock_noCarry N

/-- The two packed target digits equal the local selector/copy aggregate for
each word cell, independently of the word's period or temporal matching. -/
theorem word_target_digits {b : V → V} {N s j : V} (hword : CompactWord b N s) (hj : j < N) :
    let C := (∑ i, ((CompactCoefficientMass.selector (Compact943Data.row i) : ℕ) : V) * wordSelector b i j) +
      (∑ i, ((2^(10+i.val) : ℕ) : V) * wordPayloadBit b i j)
    dig 67 (targetBlock:V) 4393 = C ∧ dig 67 (targetBlock:V) 5495 = C := by
  have h := word_occupied hword hj
  dsimp only
  rw [targetBlock_digits _ (by norm_num), targetBlock_digits _ (by norm_num), h]
  simp [targetDigit, occupied]

#print axioms CompactWordTargetNoCarry.occupied_noCarry
#print axioms CompactWordTargetNoCarry.targetBlock_digits
#print axioms CompactWordTargetNoCarry.targetBlock_noCarry
#print axioms CompactWordTargetNoCarry.repeated_target_noCarry
#print axioms CompactWordTargetNoCarry.word_target_digits
end CompactWordTargetNoCarry
