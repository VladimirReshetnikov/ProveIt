import DiophantineConsistency.SplitCarry
import DiophantineConsistency.SplitWordBounds
import DiophantineConsistency.SplitNineRatio

/-! # Source words and their outer numerical bounds

The source is three supplied integer polynomials. Positivity is proved
before the weak cap, so converting its high integer to natural data does
not introduce a truncated polynomial branch.
-/

namespace DiophantineConsistency.SplitSourceWords

open Polynomial Finset
open scoped BigOperators

set_option maxHeartbeats 400000

structure Parameters where
  w : Fin 31 → ℕ
  q : Fin 22 → ℕ
  D0 : ℤ[X]
  D1 : ℤ[X]
  D2 : ℤ[X]

structure Valid (d : Parameters) (a : ℕ) : Prop where
  weights_injective : Function.Injective d.w
  weights_le : ∀ i, d.w i ≤ 116
  weight_top : ∃ i, d.w i = 116
  targets_injective : Function.Injective d.q
  targets_le : ∀ i, d.q i ≤ 2129
  kernels : SplitWordBounds.KernelBounds d.D0 d.D1 d.D2 ((2 : ℤ) ^ a)

def lowPositions (d : Parameters) : Finset ℕ := LowMaskCoding.positions d.w
def targetPositions (d : Parameters) : Finset ℕ := LowMaskCoding.positions d.q

noncomputable def highInt (d : Parameters) (a b g : ℕ) : ℤ :=
  SplitCarry.highInt (SplitNineRatio.base a b) g d.w d.D0 d.D1 d.D2 (targetPositions d)

noncomputable def word (d : Parameters) (a b g : ℕ) : ℕ :=
  SplitCarry.word (SplitNineRatio.base a b) 117 g (highInt d a b g)

def mask (d : Parameters) (a b : ℕ) : ℕ :=
  SplitCarry.packedMask (SplitNineRatio.base a b) b 117 d.w (targetPositions d)

theorem sum_positions {m : ℕ} (B : ℤ) (w : Fin m → ℕ) (hw : Function.Injective w) :
    (∑ j ∈ LowMaskCoding.positions w, B ^ j) = SplitWordBounds.powerSum B w := by
  unfold LowMaskCoding.positions SplitWordBounds.powerSum
  exact Finset.sum_image (fun i _ j _ h => hw h)

theorem highInt_eq (d : Parameters) (a b g : ℕ) (hi : Function.Injective d.q) :
    highInt d a b g =
      2 * SplitWordBounds.sourceValue d.D0 d.D1 d.D2 (SplitNineRatio.base a b)
        (SplitWordBounds.powerSum (SplitNineRatio.base a b) d.w + g) +
        SplitWordBounds.powerSum (SplitNineRatio.base a b) d.q := by
  unfold highInt SplitCarry.highInt targetPositions SplitWordBounds.sourceValue
  rw [sum_positions _ _ hi]
  dsimp only [SplitWordBounds.powerSum]
  ring

theorem scale (a b : ℕ) :
    (SplitNineRatio.base a b : ℤ) = 4096 * (2 : ℤ) ^ a * (b : ℤ) ^ 2 := by
  unfold SplitNineRatio.base NativeBaseBounds52.base
  push_cast
  rfl

/-- All nonnegative outer code assignments have a positive high source word. -/
theorem highInt_pos {d : Parameters} {a b : ℕ} (hd : Valid d a) (hb : 0 < b) (g : ℕ) :
    0 < highInt d a b g := by
  have hG := SplitWordBounds.source_pos_of_word hd.kernels (by positivity : 0 < (2 : ℤ) ^ a)
    (show (1 : ℤ) ≤ b by exact_mod_cast hb) (scale a b) d.w hd.weight_top
    (Int.natCast_nonneg g)
  have hT := SplitWordBounds.powerSum_nonneg
    (Int.natCast_nonneg (SplitNineRatio.base a b)) d.q
  rw [highInt_eq d a b g hd.targets_injective]
  linarith

theorem word_pos {d : Parameters} {a b : ℕ} (hd : Valid d a) (hb : 0 < b) (g : ℕ) :
    0 < word d a b g := by
  have hJ : 0 < (highInt d a b g).toNat := by
    have h := highInt_pos hd hb g
    have hc := Int.toNat_of_nonneg h.le
    omega
  have hB := (SplitNineRatio.base_bounds a hb).1
  unfold word SplitCarry.word
  positivity

theorem word_cast {d : Parameters} {a b : ℕ} (hd : Valid d a) (hb : 0 < b) (g : ℕ) :
    (word d a b g : ℤ) =
      SplitWordBounds.packedS (SplitNineRatio.base a b) g
        (SplitWordBounds.sourceValue d.D0 d.D1 d.D2 (SplitNineRatio.base a b)
          (SplitWordBounds.powerSum (SplitNineRatio.base a b) d.w + g))
        (SplitWordBounds.powerSum (SplitNineRatio.base a b) d.q) := by
  unfold word SplitCarry.word
  push_cast
  rw [Int.toNat_of_nonneg (highInt_pos hd hb g).le,
    highInt_eq d a b g hd.targets_injective]
  rfl

theorem mask_eq_population (d : Parameters) (a b : ℕ) :
    mask d a b = MaskPopulation.packedMask (SplitNineRatio.base a b) b 117
      (lowPositions d) (targetPositions d) := SplitCarry.packedMask_eq _ _ _ _ _

theorem mask_cast {d : Parameters} {a b : ℕ} (hd : Valid d a) (hb : 0 < b) :
    (mask d a b : ℤ) =
      SplitWordBounds.packedT (SplitNineRatio.base a b) b
        (SplitWordBounds.powerSum (SplitNineRatio.base a b) d.w)
        (SplitWordBounds.powerSum (SplitNineRatio.base a b) d.q) := by
  let B := SplitNineRatio.base a b
  obtain ⟨hB, hbB⟩ := SplitNineRatio.base_bounds a hb
  have hw : LowMaskCoding.positions d.w ⊆ range 117 :=
    LowMaskCoding.positions_subset (fun i => by have h := hd.weights_le i; omega)
  have he : (LowMaskCoding.supportValue B (LowMaskCoding.positions d.w) : ℤ) =
      SplitWordBounds.powerSum B d.w := by
    unfold LowMaskCoding.supportValue
    push_cast
    exact sum_positions _ _ hd.weights_injective
  have hlow := LowMaskCoding.mask_int_eq (show 1 ≤ b by omega)
    (show b ≤ B by dsimp [B]; omega) hw
  rw [he] at hlow
  unfold mask SplitCarry.packedMask LowMaskCoding.indexedMask SparseBorrowCarry.mask
  push_cast [Nat.cast_sub (show 2 ≤ SplitNineRatio.base a b by omega)]
  rw [← hlow]
  change _ = SplitWordBounds.packedT B b (SplitWordBounds.powerSum B d.w)
    (SplitWordBounds.powerSum B d.q)
  unfold targetPositions
  rw [sum_positions _ _ hd.targets_injective]
  rfl

/-- The ratio's weak cap supplies both low-block and reduced-rank ranges. -/
theorem weak_cap_bounds {d : Parameters} {a b g : ℕ} (hd : Valid d a) (hb : 0 < b)
    (hg : g < 4 * b * (SplitNineRatio.base a b) ^ 116) :
    g < (SplitNineRatio.base a b) ^ 117 ∧ word d a b g < SplitNineRatio.blockLength a b := by
  have h := SplitWordBounds.weak_cap_packing hd.kernels (by positivity : 0 < (2 : ℤ) ^ a)
    (show (1 : ℤ) ≤ b by exact_mod_cast hb) (scale a b)
    d.w hd.weights_injective hd.weights_le hd.weight_top d.q hd.targets_injective hd.targets_le
    (Int.natCast_nonneg g) (by exact_mod_cast hg)
  dsimp only at h
  constructor
  · exact_mod_cast h.2.1
  · have hS := h.2.2.2.2.2.2.2
    rw [← word_cast hd hb g] at hS
    unfold SplitNineRatio.blockLength
    exact_mod_cast hS

/-- The source rank is an ordinary integer polynomial expression on every
outer natural assignment, before the ratio or a source zero is known. -/
theorem rank_cast {d : Parameters} {a b : ℕ} (hd : Valid d a) (hb : 0 < b) (g : ℕ) :
    (SplitNineRatio.rank a b (word d a b g) (mask d a b) : ℤ) =
      let B : ℤ := SplitNineRatio.base a b
      let ell := SplitWordBounds.powerSum B d.w
      let targets := SplitWordBounds.powerSum B d.q
      let G := SplitWordBounds.sourceValue d.D0 d.D1 d.D2 B (ell + g)
      let S := SplitWordBounds.packedS B g G targets
      let T := SplitWordBounds.packedT B b ell targets
      (SplitNineRatio.blockLength a b : ℤ) * (S + T + 1) - S - 1 := by
  rw [SplitNineRatio.rank_cast _ _ _ hb, word_cast hd hb g, mask_cast hd hb]

end DiophantineConsistency.SplitSourceWords
