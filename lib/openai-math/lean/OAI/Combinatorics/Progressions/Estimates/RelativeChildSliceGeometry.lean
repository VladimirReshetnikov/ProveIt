import OAI.Combinatorics.Progressions.Geometry.CommonStrideCoordinates
import OAI.Combinatorics.Progressions.Probability.RelativeSliceFiniteLaw

namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {X : Type*} {N : X → ℕ} {q : ℕ}

theorem coordinate_progression_subset (S : ResidueBoxSlice N q) (i : X) :
    integerProgressionSupport (S.start i : ℤ) (q : ℤ) (S.length i) ⊆
      Finset.Ico (0 : ℤ) (N i : ℤ) := by
  intro x hx
  rw [integerProgressionSupport, mem_translateSupport, Finset.mem_image] at hx
  obtain ⟨y, hy, he⟩ := hx
  have hy0 := (Finset.mem_Ico.mp hy).1
  have hyL := (Finset.mem_Ico.mp hy).2
  have hycast : (y.toNat : ℤ) = y := Int.toNat_of_nonneg hy0
  have hyt : y.toNat < S.length i := by exact_mod_cast hycast ▸ hyL
  have hx' : x = (S.start i : ℤ) + (q : ℤ) * y := by
    change (q : ℤ) * y = x - S.start i at he
    omega
  rw [hx']
  refine Finset.mem_Ico.mpr ⟨by positivity, ?_⟩
  have hh := S.inside i y.toNat hyt
  have hh' : (S.start i : ℤ) + (q : ℤ) * (y.toNat : ℤ) < N i := by exact_mod_cast hh
  simpa only [hycast] using hh'

theorem stride_lt_two_div_density (S : ResidueBoxSlice N q) {i : X}
    (hql : 0 < q) (hlen : 2 ≤ S.length i) {δ : ℝ} (hδ : 0 < δ)
    (hdense : δ * (N i : ℝ) ≤ S.length i) : (q : ℝ) < 2 / δ := by
  have hh := S.inside i (S.length i - 1) (by omega)
  have hlast : (S.start i : ℝ) + (q : ℝ) * ((S.length i : ℝ) - 1) < N i := by
    have h : (S.start i : ℝ) + (q : ℝ) * ((S.length i - 1 : ℕ) : ℝ) < N i := by
      exact_mod_cast hh
    simpa only [Nat.cast_sub (by omega : 1 ≤ S.length i), Nat.cast_one] using h
  have hN : (0 : ℝ) < N i := by
    have : 0 < N i := lt_of_le_of_lt (Nat.zero_le _) hh
    exact_mod_cast this
  have hl : (2 : ℝ) ≤ S.length i := by exact_mod_cast hlen
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr hql
  have hstart : (0 : ℝ) ≤ S.start i := Nat.cast_nonneg _
  have hwidth : (q : ℝ) * S.length i < 2 * N i := by nlinarith
  have hd := mul_le_mul_of_nonneg_left hdense hq.le
  apply (lt_div_iff₀ hδ).mpr
  exact (mul_lt_mul_iff_right₀ hN).mp (by nlinarith)

theorem stride_le_exp_cost (S : ResidueBoxSlice N q) {i : X}
    (hq : 0 < q) {cost : ℝ}
    (hlarge : 2 * Real.exp cost ≤ (N i : ℝ))
    (hdense : Real.exp (-cost) * (N i : ℝ) ≤ S.length i) :
    2 ≤ S.length i ∧ (q : ℝ) ≤ 2 * Real.exp cost := by
  have hmul : Real.exp (-cost) * (2 * Real.exp cost) = 2 := by
    rw [Real.exp_neg]
    field_simp
  have hl : (2 : ℝ) ≤ S.length i := by
    calc
      2 = Real.exp (-cost) * (2 * Real.exp cost) := hmul.symm
      _ ≤ Real.exp (-cost) * N i := mul_le_mul_of_nonneg_left hlarge (Real.exp_pos _).le
      _ ≤ S.length i := hdense
  have hlen : 2 ≤ S.length i := by exact_mod_cast hl
  refine ⟨hlen, ?_⟩
  have hs := S.stride_lt_two_div_density hq hlen (Real.exp_pos (-cost)) hdense
  simpa only [Real.exp_neg, div_inv_eq_mul] using hs.le

theorem normalized_endpoint_geometry (S : ResidueBoxSlice N q) (i : X)
    (hq : 0 < q) {cost : ℝ}
    (hlarge : 2 * Real.exp cost ≤ (N i : ℝ))
    (hdense : Real.exp (-cost) * (N i : ℝ) ≤ S.length i) :
    2 ≤ S.length i ∧
    0 ≤ (S.start i : ℝ) / N i ∧
    Real.exp (-cost) / 2 ≤ (q : ℝ) * ((S.length i : ℝ) - 1) / N i ∧
    |(S.start i : ℝ) / N i| +
      |(q : ℝ) * ((S.length i : ℝ) - 1) / N i| ≤ 1 := by
  have hN : 0 < N i := by
    exact_mod_cast (mul_pos (by norm_num : (0 : ℝ) < 2) (Real.exp_pos cost)).trans_le hlarge
  have hl := (S.stride_le_exp_cost hq hlarge hdense).1
  have hg := progression_slice_endpoint_geometry (S.start i : ℤ) hN hq hl
    (Real.exp_pos (-cost)) (S.coordinate_progression_subset i)
    (by simpa only [card_integerProgressionSupport _ _ _ hq] using hdense)
  exact ⟨hl, by simpa only [Int.cast_natCast] using hg.1,
    hg.2.1, by simpa only [Int.cast_natCast] using hg.2.2.1⟩

theorem commonStrideBox_subset [Fintype X] [DecidableEq X]
    (S : ResidueBoxSlice N q) :
    commonStrideBox (fun i => (S.start i : ℤ)) q S.length ⊆ integerBox N := by
  intro x hx
  rw [mem_integerBox]
  intro i
  exact Finset.mem_Ico.mp (S.coordinate_progression_subset i
    (Fintype.mem_piFinset.mp hx i))

theorem commonStrideBox_eq_parameter_image [Fintype X] [DecidableEq X]
    (S : ResidueBoxSlice N q) :
    commonStrideBox (fun i => (S.start i : ℤ)) q S.length =
      (integerBox S.length).image (fun u i => (S.start i : ℤ) + (q : ℤ) * u i) :=
  Erdos3.commonStrideBox_eq_image _ _ _

end Erdos3.ResidueBoxSlice

end

end OAI
