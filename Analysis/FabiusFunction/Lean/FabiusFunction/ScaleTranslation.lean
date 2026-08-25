import FabiusFunction.GlobalExtension

/-!
# Power-of-two translation identities

The Thue–Morse series changes sign when translated by a power of two over
the corresponding initial block.  Combining this with the global derivative
formula gives the translated Taylor-remainder identity used in Lemma 1 and
Proposition 10 of Arias de Reyna's paper.  Closed-endpoint and
interval-membership forms are provided so callers need not strengthen natural
weak inequalities or repeat positivity facts already implied by a dyadic
interval.
-/

open scoped BigOperators ContDiff
open Finset Set

namespace Fabius

set_option autoImplicit false

/-- On its initial block, translation by `2^r` negates the signed extension. -/
theorem extendedFabius_add_pow_two (F : BoundedFabius) (hF : IsFabius F)
    (r : ℕ) (hr : 1 ≤ r) {x : ℝ} (hx0 : 0 ≤ x) (hxpow : x ≤ (2 : ℝ) ^ r) :
    extendedFabius F (x + (2 : ℝ) ^ r) = -extendedFabius F x := by
  let B : ℕ := 2 ^ (r - 1)
  have hpowNat : 2 ^ r = 2 * B := by
    calc
      2 ^ r = 2 ^ ((r - 1) + 1) := by
        congr 1
        omega
      _ = 2 ^ (r - 1) * 2 := by rw [pow_succ]
      _ = 2 * B := by simp only [B]; ring
  have hpowReal : (2 : ℝ) ^ r = 2 * (B : ℝ) := by
    exact_mod_cast hpowNat
  have horig : extendedFabius F x =
      ∑ n ∈ range B, (-1 : ℝ) ^ binaryWeight n *
        rvachevUp F (x - 2 * (n : ℝ) - 1) := by
    unfold extendedFabius
    rw [tsum_eq_sum]
    intro n hn
    have hnB : B ≤ n := by simpa using hn
    have hnBR : (B : ℝ) ≤ n := by exact_mod_cast hnB
    rw [rvachevUp_eq_zero_of_le_neg_one F hF (by
      rw [hpowReal] at hxpow
      nlinarith)]
    ring
  have hshift : extendedFabius F (x + (2 : ℝ) ^ r) =
      ∑ n ∈ Ico B (2 * B), (-1 : ℝ) ^ binaryWeight n *
        rvachevUp F (x + (2 : ℝ) ^ r - 2 * (n : ℝ) - 1) := by
    unfold extendedFabius
    rw [tsum_eq_sum]
    intro n hn
    rw [Finset.mem_Ico, not_and_or] at hn
    rcases hn with hn | hn
    · have hnlt : n < B := lt_of_not_ge hn
      have hnle : n + 1 ≤ B := by omega
      have hnleR : (n : ℝ) + 1 ≤ B := by exact_mod_cast hnle
      rw [rvachevUp_eq_zero_of_one_le F hF (by
        rw [hpowReal]
        nlinarith)]
      ring
    · have hnle : 2 * B ≤ n := by simpa using hn
      have hnleR : (2 * B : ℕ) ≤ n := hnle
      have hnleReal : (2 * B : ℝ) ≤ n := by exact_mod_cast hnleR
      rw [rvachevUp_eq_zero_of_le_neg_one F hF (by
        rw [hpowReal] at hxpow ⊢
        nlinarith)]
      ring
  rw [hshift, Finset.sum_Ico_eq_sum_range]
  have hsub : 2 * B - B = B := by omega
  rw [hsub, horig]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  have hmB : m < B := by simpa using hm
  have hmPow : m < 2 ^ (r - 1) := by simpa only [B] using hmB
  simp only [B]
  rw [binaryWeight_add_pow_two (r - 1) m hmPow, pow_succ]
  rw [hpowReal]
  push_cast
  simp only [B, Nat.cast_pow, Nat.cast_ofNat]
  ring_nf

/-- Translating by `2^scale` negates a sufficiently high iterated derivative,
including at the right endpoint of the source interval. -/
theorem iteratedDeriv_add_zpow_of_le
    (F : BoundedFabius) (hF : IsFabius F)
    (scale : ℤ) (order : ℕ) (horder : (0 : ℤ) ≤ scale + order)
    {t : ℝ} (ht0 : 0 ≤ t) (htle : t ≤ (2 : ℝ) ^ scale) :
    iteratedDeriv (order + 1) (extendedFabius F) (t + (2 : ℝ) ^ scale) =
      -iteratedDeriv (order + 1) (extendedFabius F) t := by
  let r : ℕ := (scale + order + 1).toNat
  have hrnonneg : (0 : ℤ) ≤ scale + order + 1 := by omega
  have hrCast : (r : ℤ) = scale + order + 1 := by
    exact Int.toNat_of_nonneg hrnonneg
  have hr : 1 ≤ r := by
    have : (1 : ℤ) ≤ scale + order + 1 := by omega
    rw [← hrCast] at this
    exact_mod_cast this
  have hpow : (2 : ℝ) ^ r =
      (2 : ℝ) ^ (order + 1) * (2 : ℝ) ^ scale := by
    rw [← zpow_natCast]
    rw [hrCast]
    have hexp : scale + (order : ℤ) + 1 = ((order + 1 : ℕ) : ℤ) + scale := by
      push_cast
      ring
    rw [hexp, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
  rw [iteratedDeriv_extendedFabius F hF, iteratedDeriv_extendedFabius F hF]
  have hz0 : 0 ≤ (2 : ℝ) ^ (order + 1) * t := mul_nonneg (by positivity) ht0
  have hzpow : (2 : ℝ) ^ (order + 1) * t ≤ (2 : ℝ) ^ r := by
    rw [hpow]
    exact mul_le_mul_of_nonneg_left htle (by positivity)
  have hshift := extendedFabius_add_pow_two F hF r hr hz0 hzpow
  have harg : (2 : ℝ) ^ (order + 1) * (t + (2 : ℝ) ^ scale) =
      (2 : ℝ) ^ (order + 1) * t + (2 : ℝ) ^ r := by
    rw [hpow]
    ring
  rw [harg, hshift]
  ring

/-- Open-endpoint compatibility form of `iteratedDeriv_add_zpow_of_le`. -/
theorem iteratedDeriv_add_zpow
    (F : BoundedFabius) (hF : IsFabius F)
    (scale : ℤ) (order : ℕ) (horder : (0 : ℤ) ≤ scale + order)
    {t : ℝ} (ht0 : 0 ≤ t) (htlt : t < (2 : ℝ) ^ scale) :
    iteratedDeriv (order + 1) (extendedFabius F) (t + (2 : ℝ) ^ scale) =
      -iteratedDeriv (order + 1) (extendedFabius F) t :=
  iteratedDeriv_add_zpow_of_le F hF scale order horder ht0 htlt.le

/-- The translated Taylor remainders on two adjacent closed intervals cancel.
The dyadic interval membership already implies the positivity hypothesis
carried by the original compatibility theorem below. -/
theorem taylorRemainder_translate_of_mem_Icc
    (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (scale : ℤ) (order : ℕ)
    (hx : x ∈ Icc ((2 : ℝ) ^ scale) ((2 : ℝ) ^ (scale + 1)))
    (horder : (0 : ℤ) ≤ scale + order) :
    (∫ t in (2 : ℝ) ^ scale..x,
        (x - t) ^ order * iteratedDeriv (order + 1) (extendedFabius F) t) =
      -(∫ t in 0..(x - (2 : ℝ) ^ scale),
        (x - (2 : ℝ) ^ scale - t) ^ order *
          iteratedDeriv (order + 1) (extendedFabius F) t) := by
  rcases hx with ⟨hlo, hhi⟩
  let a : ℝ := (2 : ℝ) ^ scale
  let y : ℝ := x - a
  have haPos : 0 < a := by exact zpow_pos (by norm_num) scale
  have hy0 : 0 ≤ y := by dsimp only [y, a]; linarith
  have hpowSucc : (2 : ℝ) ^ (scale + 1) = 2 * a := by
    dsimp only [a]
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
    ring
  have hyle : y ≤ a := by
    rw [hpowSucc] at hhi
    dsimp only [y]
    linarith
  let g : ℝ → ℝ := fun t =>
    (x - t) ^ order * iteratedDeriv (order + 1) (extendedFabius F) t
  let q : ℝ → ℝ := fun t =>
    (y - t) ^ order * iteratedDeriv (order + 1) (extendedFabius F) t
  have htranslate : (∫ t in a..x, g t) = ∫ t in 0..y, g (t + a) := by
    convert (intervalIntegral.integral_comp_add_right (a := 0) (b := y) g a).symm using 1
    dsimp only [y]
    ring_nf
  have hintegrand : Set.EqOn (fun t => g (t + a)) (fun t => -q t) (uIcc 0 y) := by
    intro t ht
    rw [uIcc_of_le hy0] at ht
    have hderiv := iteratedDeriv_add_zpow_of_le F hF scale order horder
      ht.1 (ht.2.trans hyle)
    dsimp only [g, q, a, y]
    rw [hderiv]
    ring
  change (∫ t in a..x, g t) = -∫ t in 0..y, q t
  rw [htranslate, intervalIntegral.integral_congr hintegrand,
    intervalIntegral.integral_neg]

/-- Half-open interval form of `taylorRemainder_translate_of_mem_Icc`. -/
theorem taylorRemainder_translate_of_mem_Ico
    (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (scale : ℤ) (order : ℕ)
    (hx : x ∈ Ico ((2 : ℝ) ^ scale) ((2 : ℝ) ^ (scale + 1)))
    (horder : (0 : ℤ) ≤ scale + order) :
    (∫ t in (2 : ℝ) ^ scale..x,
        (x - t) ^ order * iteratedDeriv (order + 1) (extendedFabius F) t) =
      -(∫ t in 0..(x - (2 : ℝ) ^ scale),
        (x - (2 : ℝ) ^ scale - t) ^ order *
          iteratedDeriv (order + 1) (extendedFabius F) t) :=
  taylorRemainder_translate_of_mem_Icc F hF x scale order
    ⟨hx.1, hx.2.le⟩ horder

set_option linter.unusedVariables false in
/-- Compatibility form of `taylorRemainder_translate_of_mem_Icc` retaining
the original explicit hypotheses and binder order. -/
theorem taylorRemainder_translate (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (scale : ℤ) (order : ℕ)
    (hx : 0 < x)
    (hlo : (2 : ℝ) ^ scale ≤ x)
    (hhi : x < (2 : ℝ) ^ (scale + 1))
    (horder : (0 : ℤ) ≤ scale + order) :
    (∫ t in (2 : ℝ) ^ scale..x,
        (x - t) ^ order * iteratedDeriv (order + 1) (extendedFabius F) t) =
      -(∫ t in 0..(x - (2 : ℝ) ^ scale),
        (x - (2 : ℝ) ^ scale - t) ^ order *
          iteratedDeriv (order + 1) (extendedFabius F) t) :=
  taylorRemainder_translate_of_mem_Ico F hF x scale order ⟨hlo, hhi⟩ horder

end Fabius
