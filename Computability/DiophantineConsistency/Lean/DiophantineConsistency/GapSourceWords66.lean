import DiophantineConsistency.SplitCarry
import DiophantineConsistency.GapWordBounds66
import DiophantineConsistency.GapNineRatio66
import DiophantineConsistency.GapKernels66

/-! # H2082 source words and their outer numerical bounds

The source is three supplied integer polynomials, with H2082 degree ceilings.
The exponent a is half the coefficient-height exponent. Positivity is proved
before the weak cap, so converting its high integer to natural data does
not introduce a truncated polynomial branch.
-/

namespace DiophantineConsistency.GapSourceWords66

open Polynomial Finset
open scoped BigOperators

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

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
  targets_le : ∀ i, d.q i ≤ 2050
  kernels : GapWordBounds66.KernelBounds d.D0 d.D1 d.D2 ((2 : ℤ) ^ (2*a))

def lowPositions (d : Parameters) : Finset ℕ := LowMaskCoding.positions d.w
def targetPositions (d : Parameters) : Finset ℕ := LowMaskCoding.positions d.q

noncomputable def highInt (d : Parameters) (a b g : ℕ) : ℤ :=
  SplitCarry.highInt (GapNineRatio66.base a b) g d.w d.D0 d.D1 d.D2 (targetPositions d)

noncomputable def word (d : Parameters) (a b g : ℕ) : ℕ :=
  SplitCarry.word (GapNineRatio66.base a b) 117 g (highInt d a b g)

def mask (d : Parameters) (a b : ℕ) : ℕ :=
  SplitCarry.packedMask (GapNineRatio66.base a b) b 117 d.w (targetPositions d)

theorem sum_positions {m : ℕ} (B : ℤ) (w : Fin m → ℕ) (hw : Function.Injective w) :
    (∑ j ∈ LowMaskCoding.positions w, B ^ j) = GapWordBounds66.powerSum B w := by
  unfold LowMaskCoding.positions GapWordBounds66.powerSum SplitWordBounds.powerSum
  exact Finset.sum_image (fun i _ j _ h => hw h)

theorem highInt_eq (d : Parameters) (a b g : ℕ) (hi : Function.Injective d.q) :
    highInt d a b g =
      2 * GapWordBounds66.sourceValue d.D0 d.D1 d.D2 (GapNineRatio66.base a b)
        (GapWordBounds66.powerSum (GapNineRatio66.base a b) d.w + g) +
        GapWordBounds66.powerSum (GapNineRatio66.base a b) d.q := by
  unfold highInt SplitCarry.highInt targetPositions GapWordBounds66.sourceValue SplitWordBounds.sourceValue
  rw [sum_positions _ _ hi]
  dsimp only [GapWordBounds66.powerSum,SplitWordBounds.powerSum]
  ring

theorem scale (a b : ℕ) :
    (GapNineRatio66.base a b : ℤ) = 4096 * (2 : ℤ) ^ (2*a) * (b : ℤ) ^ 2 := by
  unfold GapNineRatio66.base SplitNineRatio.base NativeBaseBounds52.base
  push_cast
  rfl

/-- All nonnegative outer code assignments have a positive high source word. -/
theorem highInt_pos {d : Parameters} {a b : ℕ} (hd : Valid d a) (hb : 0 < b) (g : ℕ) :
    0 < highInt d a b g := by
  have hG := GapWordBounds66.source_pos_of_word hd.kernels (by positivity : 0 < (2 : ℤ) ^ (2*a))
    (show (1 : ℤ) ≤ b by exact_mod_cast hb) (scale a b) d.w hd.weight_top
    (Int.natCast_nonneg g)
  have hT := SplitWordBounds.powerSum_nonneg
    (Int.natCast_nonneg (GapNineRatio66.base a b)) d.q
  rw [highInt_eq d a b g hd.targets_injective]
  linarith

theorem word_pos {d : Parameters} {a b : ℕ} (hd : Valid d a) (hb : 0 < b) (g : ℕ) :
    0 < word d a b g := by
  have hJ : 0 < (highInt d a b g).toNat := by
    have h := highInt_pos hd hb g
    have hc := Int.toNat_of_nonneg h.le
    omega
  have hB := (GapNineRatio66.base_bounds a hb).1
  unfold word SplitCarry.word
  positivity

theorem word_cast {d : Parameters} {a b : ℕ} (hd : Valid d a) (hb : 0 < b) (g : ℕ) :
    (word d a b g : ℤ) =
      GapWordBounds66.packedS (GapNineRatio66.base a b) g
        (GapWordBounds66.sourceValue d.D0 d.D1 d.D2 (GapNineRatio66.base a b)
          (GapWordBounds66.powerSum (GapNineRatio66.base a b) d.w + g))
        (GapWordBounds66.powerSum (GapNineRatio66.base a b) d.q) := by
  unfold word SplitCarry.word
  push_cast
  rw [Int.toNat_of_nonneg (highInt_pos hd hb g).le,
    highInt_eq d a b g hd.targets_injective]
  rfl

theorem mask_eq_population (d : Parameters) (a b : ℕ) :
    mask d a b = MaskPopulation.packedMask (GapNineRatio66.base a b) b 117
      (lowPositions d) (targetPositions d) := SplitCarry.packedMask_eq _ _ _ _ _

theorem mask_cast {d : Parameters} {a b : ℕ} (hd : Valid d a) (hb : 0 < b) :
    (mask d a b : ℤ) =
      GapWordBounds66.packedT (GapNineRatio66.base a b) b
        (GapWordBounds66.powerSum (GapNineRatio66.base a b) d.w)
        (GapWordBounds66.powerSum (GapNineRatio66.base a b) d.q) := by
  let B := GapNineRatio66.base a b
  obtain ⟨hB, hbB⟩ := GapNineRatio66.base_bounds a hb
  have hw : LowMaskCoding.positions d.w ⊆ range 117 :=
    LowMaskCoding.positions_subset (fun i => by have h := hd.weights_le i; omega)
  have he : (LowMaskCoding.supportValue B (LowMaskCoding.positions d.w) : ℤ) =
      GapWordBounds66.powerSum B d.w := by
    unfold LowMaskCoding.supportValue
    push_cast
    exact sum_positions _ _ hd.weights_injective
  have hlow := LowMaskCoding.mask_int_eq (show 1 ≤ b by omega)
    (show b ≤ B by dsimp [B]; omega) hw
  rw [he] at hlow
  unfold mask SplitCarry.packedMask LowMaskCoding.indexedMask SparseBorrowCarry.mask
  push_cast [Nat.cast_sub (show 2 ≤ GapNineRatio66.base a b by omega)]
  rw [← hlow]
  change _ = GapWordBounds66.packedT B b (GapWordBounds66.powerSum B d.w)
    (GapWordBounds66.powerSum B d.q)
  unfold targetPositions
  rw [sum_positions _ _ hd.targets_injective]
  rfl

/-- The ratio's weak cap supplies both low-block and reduced-rank ranges. -/
theorem weak_cap_bounds {d : Parameters} {a b g : ℕ} (hd : Valid d a) (hb : 0 < b)
    (hg : g < 4 * b * (GapNineRatio66.base a b) ^ 116) :
    g < (GapNineRatio66.base a b) ^ 117 ∧ word d a b g < GapNineRatio66.blockLength a b := by
  have h := GapWordBounds66.weak_cap_packing hd.kernels (by positivity : 0 < (2 : ℤ) ^ (2*a))
    (show (1 : ℤ) ≤ b by exact_mod_cast hb) (scale a b)
    d.w hd.weights_injective hd.weights_le hd.weight_top d.q hd.targets_injective hd.targets_le
    (Int.natCast_nonneg g) (by exact_mod_cast hg)
  dsimp only at h
  constructor
  · exact_mod_cast h.2.1
  · have hS := h.2.2.2.2.2.2.2
    rw [← word_cast hd hb g] at hS
    unfold GapNineRatio66.blockLength
    exact_mod_cast hS

/-- The source rank is an ordinary integer polynomial expression on every
outer natural assignment, before the ratio or a source zero is known. -/
theorem rank_cast {d : Parameters} {a b : ℕ} (hd : Valid d a) (hb : 0 < b) (g : ℕ) :
    (GapNineRatio66.rank a b (word d a b g) (mask d a b) : ℤ) =
      let B : ℤ := GapNineRatio66.base a b
      let ell := GapWordBounds66.powerSum B d.w
      let targets := GapWordBounds66.powerSum B d.q
      let G := GapWordBounds66.sourceValue d.D0 d.D1 d.D2 B (ell + g)
      let S := GapWordBounds66.packedS B g G targets
      let T := GapWordBounds66.packedT B b ell targets
      (GapNineRatio66.blockLength a b : ℤ) * (S + T + 1) - S - 1 := by
  rw [GapNineRatio66.rank_cast _ _ _ hb, word_cast hd hb g, mask_cast hd hb]

/-- The actual H2082 weights, targets and literal sparse kernels. -/
noncomputable def literalParameters (ports : Fin 4 → ℤ) : Parameters :=
  ⟨GapCertificate66.weights,GapCertificate66.targets,
    GapKernels66.D0 ports,GapKernels66.D1 ports,GapKernels66.D2 ports⟩

theorem literal_valid_of_height (ports : Fin 4 → ℤ) (a : ℕ)
    (h0 : ∀ i, |(GapKernels66.D0 ports).coeff i| ≤ (2:ℤ)^(2*a))
    (h1 : ∀ i, |(GapKernels66.D1 ports).coeff i| ≤ (2:ℤ)^(2*a))
    (h2 : ∀ i, |(GapKernels66.D2 ports).coeff i| ≤ (2:ℤ)^(2*a)) :
    Valid (literalParameters ports) a :=
  ⟨GapCertificate66.weights_injective,GapCertificate66.maximum_weight,
    ⟨20,rfl⟩,GapCertificate66.targets_injective,GapCertificate66.maximum_target,
    ⟨GapKernelData66.degree_D0 ports,GapKernelData66.degree_D1 ports,
      GapKernelData66.degree_D2 ports,h0,h1,h2,GapKernelData66.leading_D2 ports⟩⟩

/-- The complete numerical validity contract follows from the four ordinary
port bounds; no source zero or native compiler calibration is used. -/
theorem literal_valid_pow (ports : Fin 4 → ℤ) (p q a : ℕ)
    (hp : 1 ≤ p) (hpq : p+4 ≤ q) (ha : p+q+1 = 2*a)
    (hb : 0 ≤ ports 0 ∧ ports 0 < 2^p)
    (hk : 0 ≤ ports 1 ∧ ports 1 < 2^q)
    (hm : 0 ≤ ports 2 ∧ ports 2 < 2^p)
    (hf : 0 ≤ ports 3 ∧ ports 3 < 2*2^p) :
    Valid (literalParameters ports) a := by
  obtain ⟨h0,h1,h2⟩ := GapKernels66.kernel_heights_pow ports p q hp hpq hb hk hm hf
  rw [ha] at h0 h1 h2
  exact literal_valid_of_height ports a h0 h1 h2

end DiophantineConsistency.GapSourceWords66
