/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Lattices.RoundedAffineLifts
import OAI.Combinatorics.Progressions.Probability.AnisotropicSmoothPairLaw

namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open scoped Classical

noncomputable def jointFrameSourceLo {K I : Type*} (width : Option K × I → ℝ) :
    Option K × I → ℤ :=
  fun t => match t.1 with
    | none => 0
    | some _ => -⌈width t⌉

noncomputable def jointFrameSourceHi {K I : Type*} (N : I → ℕ)
    (width : Option K × I → ℝ) : Option K × I → ℤ :=
  fun t => match t.1 with
    | none => N t.2
    | some _ => ⌈width t⌉ + 1

theorem jointFrameSource_nonempty {K I : Type*} (N : I → ℕ)
    (hN : ∀ i, 0 < N i) (width : Option K × I → ℝ) (hw : ∀ t, 0 ≤ width t) :
    ∀ t, jointFrameSourceLo width t < jointFrameSourceHi N width t := by
  rintro ⟨_ | k, i⟩
  · simpa [jointFrameSourceLo, jointFrameSourceHi] using hN i
  · have hc : (0 : ℤ) ≤ ⌈width (some k,i)⌉ := Int.ceil_nonneg (hw _)
    dsimp [jointFrameSourceLo, jointFrameSourceHi]
    omega

theorem jointIntegerFrame_mem_sourceBox {K I : Type*} [Fintype K] [Fintype I]
    [DecidableEq I] (N margin : I → ℕ) (hmargin : ∀ i, 2 * margin i ≤ N i)
    (width : Option K × I → ℝ) (hroot : ∀ i, width (none,i) ≤ (margin i : ℝ))
    (z : trimmedIntegerBox N margin × rectangularWeightIndices 0 width 1) :
    ∀ t, jointIntegerFrame (z.1.val,z.2.val) t.1 t.2 ∈
      Finset.Ico (jointFrameSourceLo width t) (jointFrameSourceHi N width t) := by
  have hb := rectangularWeightIndices_zero_bound width z.2.property
  have hconstant : (fun i => z.1.val i + z.2.val (none,i)) ∈ integerBox N := by
    apply trimmedIntegerBox_add_mem N margin hmargin z.1.property
    intro i
    have h := (hb (none,i)).trans (hroot i)
    exact_mod_cast h
  rintro ⟨_ | k, i⟩
  · simpa only [jointIntegerFrame, jointFrameSourceLo, jointFrameSourceHi,
      Finset.mem_Ico] using (mem_integerBox N _).mp hconstant i
  · have hbound : |z.2.val (some k,i)| ≤ ⌈width (some k,i)⌉ := by
      exact_mod_cast (hb (some k,i)).trans (Int.le_ceil _)
    have hparts := abs_le.mp hbound
    simp only [jointIntegerFrame, jointFrameSourceLo, jointFrameSourceHi, Finset.mem_Ico]
    omega

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped Classical

theorem jointFrameSource_window_bounds {K I : Type*} [Fintype K] [Fintype I]
    (N : I → ℕ) (width : Option K × I → ℝ) {L : ℝ} (hL : 0 < L)
    (hwide : ∀ k i, 1 ≤ width (some k, i))
    (hsmall : ∀ k i, 3 * width (some k, i) ≤ (N i : ℝ) / L) :
    (∀ z ∈ Fintype.piFinset (fun t =>
        Finset.Ico (jointFrameSourceLo width t) (jointFrameSourceHi N width t)),
      ∀ t, |(z t : ℝ)| ≤ smoothPairCoefficientScale (2 * (N t.2 : ℝ)) L t.1 / 2) ∧
    (∀ k i, |(jointFrameSourceLo width (some k, i) : ℝ)| ≤ 2 * (N i : ℝ) / L) ∧
    (∀ k i, |(jointFrameSourceHi N width (some k, i) : ℝ)| ≤ 2 * (N i : ℝ) / L) := by
  have hceil0 (k : K) (i : I) : (0 : ℝ) ≤ (⌈width (some k, i)⌉ : ℤ) := by
    exact_mod_cast Int.ceil_nonneg (zero_le_one.trans (hwide k i))
  have hceil (k : K) (i : I) :
      (⌈width (some k, i)⌉ : ℝ) + 1 ≤ (N i : ℝ) / L := by
    have hc := Int.ceil_lt_add_one (width (some k, i))
    have hw := hwide k i
    have hs := hsmall k i
    linarith
  have hdouble (i : I) : (N i : ℝ) / L ≤ 2 * (N i : ℝ) / L := by
    apply div_le_div_of_nonneg_right _ hL.le
    nlinarith [Nat.cast_nonneg (N i) (α := ℝ)]
  refine ⟨?_, ?_, ?_⟩
  · intro z hz t
    have ht := Finset.mem_Ico.mp (Fintype.mem_piFinset.mp hz t)
    rcases t with ⟨_ | k, i⟩
    · simp only [jointFrameSourceLo, jointFrameSourceHi] at ht
      have hz0 : (0 : ℝ) ≤ z (none, i) := by exact_mod_cast ht.1
      have hzN : (z (none, i) : ℝ) < N i := by exact_mod_cast ht.2
      simpa only [smoothPairCoefficientScale, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0),
        abs_of_nonneg hz0] using hzN.le
    · have hlo : -(⌈width (some k, i)⌉ : ℝ) ≤ z (some k, i) := by
        exact_mod_cast ht.1
      have hhi : (z (some k, i) : ℝ) < (⌈width (some k, i)⌉ : ℝ) + 1 := by
        exact_mod_cast ht.2
      have hzbound : |(z (some k, i) : ℝ)| ≤ (N i : ℝ) / L := by
        apply abs_le.mpr
        constructor <;> linarith [hceil k i]
      have hscale : smoothPairCoefficientScale (2 * (N i : ℝ)) L (some k) / 2 =
          (N i : ℝ) / L := by
        dsimp [smoothPairCoefficientScale]
        ring
      rwa [hscale]
  · intro k i
    simp only [jointFrameSourceLo, Int.cast_neg, abs_neg,
      abs_of_nonneg (hceil0 k i)]
    exact (by linarith [hceil k i] : (⌈width (some k, i)⌉ : ℝ) ≤ (N i : ℝ) / L).trans
      (hdouble i)
  · intro k i
    simp only [jointFrameSourceHi, Int.cast_add, Int.cast_one,
      abs_of_nonneg (add_nonneg (hceil0 k i) zero_le_one)]
    exact (hceil k i).trans (hdouble i)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators Classical

private theorem jointFrame_slope_side_cap {W : ℝ} (hW : 1 ≤ W) :
    0 ≤ (2 * (⌈W⌉ : ℝ) + 1) * (2 / W) ∧
      (2 * (⌈W⌉ : ℝ) + 1) * (2 / W) ≤ 10 := by
  have hW0 : 0 < W := by linarith
  have hceil0 : (0 : ℝ) ≤ (⌈W⌉ : ℤ) := by exact_mod_cast Int.ceil_nonneg hW0.le
  constructor
  · positivity
  · rw [← mul_div_assoc]
    apply (div_le_iff₀ hW0).mpr
    have hc := Int.ceil_lt_add_one W
    nlinarith

theorem jointFrameSource_volume_cap_le {K I : Type*} [Fintype K] [Fintype I]
    (N margin : I → ℕ) (hmargin : ∀ i, 2 * margin i < N i)
    (hloss : (∑ i, 2 * (margin i : ℝ) / N i) ≤ 1/2)
    (width : Option K × I → ℝ) (hwidth : ∀ t : K × I, 1 ≤ width (some t.1,t.2)) :
    (∏ t, ((jointFrameSourceHi N width t - jointFrameSourceLo width t : ℤ) : ℝ)) *
        (((trimmedIntegerBox N margin).card : ℝ)⁻¹ *
          ∏ t : K × I, 2 / width (some t.1,t.2)) ≤ 2 * 10 ^ Fintype.card (K × I) := by
  have hvolume :
      (∏ t, ((jointFrameSourceHi N width t - jointFrameSourceLo width t : ℤ) : ℝ)) =
      (∏ i, (N i : ℝ)) *
        ∏ t : K × I, (2 * (⌈width (some t.1,t.2)⌉ : ℝ) + 1) := by
    rw [Fintype.prod_prod_type, Fintype.prod_option]
    simp only [jointFrameSourceHi, jointFrameSourceLo, sub_zero, Int.cast_natCast,
      Int.cast_sub, Int.cast_add, Int.cast_neg, Int.cast_one]
    rw [Fintype.prod_prod_type]
    congr 1
    apply Finset.prod_congr rfl
    intro k _
    apply Finset.prod_congr rfl
    intro i _
    ring
  have hproduct :
      (∏ t : K × I, (2 * (⌈width (some t.1,t.2)⌉ : ℝ) + 1) *
        (2 / width (some t.1,t.2))) ≤ 10 ^ Fintype.card (K × I) := by
    calc
      _ ≤ ∏ _t : K × I, (10 : ℝ) :=
        Finset.prod_le_prod₀ (fun t _ => (jointFrame_slope_side_cap (hwidth t)).1)
          (fun t _ => (jointFrame_slope_side_cap (hwidth t)).2)
      _ = _ := by simp
  calc
    _ = (((integerBox N).card : ℝ) / (trimmedIntegerBox N margin).card) *
        ∏ t : K × I, (2 * (⌈width (some t.1,t.2)⌉ : ℝ) + 1) *
          (2 / width (some t.1,t.2)) := by
      rw [hvolume, card_integerBox, Nat.cast_prod, Finset.prod_mul_distrib, div_eq_mul_inv]
      ring
    _ ≤ 2 * 10 ^ Fintype.card (K × I) :=
      mul_le_mul (trimmedIntegerBox_card_ratio_le_two N margin hmargin hloss) hproduct
        (Finset.prod_nonneg (fun t _ => (jointFrame_slope_side_cap (hwidth t)).1))
        (by norm_num)

theorem jointFrameSource_volume_exp_bound (d : ℕ) {p : ℝ}
    (hp : 4 * ((d : ℝ) + 1) ≤ p) :
    2 * (10 : ℝ)^d ≤ Real.exp p := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h16 : (16 : ℝ) ≤ Real.exp 4 := by
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 4
    norm_num [← Real.exp_nat_mul] at hpow ⊢
    exact hpow
  calc
    _ ≤ Real.exp 4 * (Real.exp 4)^d := by
      gcongr <;> linarith
    _ = Real.exp (4 * ((d : ℝ) + 1)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr hp

theorem jointFrameSource_volume_cap_le_exp {K I : Type*} [Fintype K] [Fintype I]
    (N margin : I → ℕ) (hmargin : ∀ i, 2 * margin i < N i)
    (hloss : (∑ i, 2 * (margin i : ℝ) / N i) ≤ 1/2)
    (width : Option K × I → ℝ) (hwidth : ∀ t : K × I, 1 ≤ width (some t.1,t.2))
    {p : ℝ} (hp : 4 * ((Fintype.card (K × I) : ℝ) + 1) ≤ p) :
    (∏ t, ((jointFrameSourceHi N width t - jointFrameSourceLo width t : ℤ) : ℝ)) *
        (((trimmedIntegerBox N margin).card : ℝ)⁻¹ *
          ∏ t : K × I, 2 / width (some t.1,t.2)) ≤ Real.exp p :=
  (jointFrameSource_volume_cap_le N margin hmargin hloss width hwidth).trans
    (jointFrameSource_volume_exp_bound _ hp)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators Classical

noncomputable def canonicalJointFrameWindowConstant (d : ℕ) (τ : ℝ) : ℝ :=
  16 * (2 * (d : ℝ) + 1) / τ

theorem canonicalJointFrameWindowConstant_two_le (d : ℕ) {τ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    2 ≤ canonicalJointFrameWindowConstant d τ := by
  unfold canonicalJointFrameWindowConstant
  apply (le_div_iff₀ hτ).mpr
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  nlinarith

theorem canonicalJointFrame_slope_small {K I : Type*} (N : I → ℕ)
    {L Wsite τ : ℝ} (hL : 1 ≤ L) (hW : L ≤ Wsite) (_hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (k : K) (i : I) :
    3 * trimmedSpatialWidths Wsite τ N (some k,i) ≤ (N i : ℝ) / L := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hden : 0 < 8 * (1 + Wsite) := by linarith
  have hc : 3 * τ * L ≤ 8 * (1 + Wsite) := by
    have hh := mul_le_mul_of_nonneg_right hτ1 hLp.le
    nlinarith
  have hN : (0 : ℝ) ≤ N i := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hc hN
  dsimp only [trimmedSpatialWidths, centeredSpatialWidths]
  rw [le_div_iff₀ hLp]
  have hdiv : (3 * τ * L * (N i : ℝ)) / (8 * (1 + Wsite)) ≤ (N i : ℝ) :=
    (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hmul)
  calc
    _ = (3 * τ * L * (N i : ℝ)) / (8 * (1 + Wsite)) := by ring
    _ ≤ (N i : ℝ) := hdiv

theorem canonicalJointFrame_slope_scale (d : ℕ) (N : ℕ)
    {L Wsite τ : ℝ} (hL : 1 ≤ L) (hW0 : 0 ≤ Wsite)
    (hW : Wsite ≤ 2 * (d : ℝ) * L) (hτ : 0 < τ) :
    2 * (N : ℝ) / L ≤ canonicalJointFrameWindowConstant d τ *
      (τ * ((N : ℝ) / (8 * (1 + Wsite)))) := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hden : 0 < 1 + Wsite := by linarith
  have hc : 1 + Wsite ≤ (2 * (d : ℝ) + 1) * L := by nlinarith
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2 * (N : ℝ) by positivity)
  have he : canonicalJointFrameWindowConstant d τ *
      (τ * ((N : ℝ) / (8 * (1 + Wsite)))) =
      2 * (2 * (d : ℝ) + 1) * (N : ℝ) / (1 + Wsite) := by
    unfold canonicalJointFrameWindowConstant
    field_simp [hτ.ne', hden.ne']
    ring
  rw [he]
  apply (div_le_div_iff₀ hLp hden).mpr
  nlinarith

theorem canonicalJointFrame_source_scale {K I : Type*} (d : ℕ) (N : I → ℕ)
    {L Wsite τ : ℝ} (hL : 1 ≤ L) (hW0 : 0 ≤ Wsite)
    (hW : Wsite ≤ 2 * (d : ℝ) * L) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (t : Option K × I) :
    smoothPairCoefficientScale (2 * (N t.2 : ℝ)) L t.1 ≤
      canonicalJointFrameWindowConstant d τ *
        ((jointFrameSourceHi N (trimmedSpatialWidths Wsite τ N) t -
          jointFrameSourceLo (trimmedSpatialWidths Wsite τ N) t : ℤ) : ℝ) := by
  have hK := canonicalJointFrameWindowConstant_two_le d hτ hτ1
  rcases t with ⟨_ | k,i⟩
  · simpa only [smoothPairCoefficientScale, jointFrameSourceHi, jointFrameSourceLo,
      sub_zero, Int.cast_natCast] using
      mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg (α := ℝ) (N i))
  · have hs := canonicalJointFrame_slope_scale d (N i) hL hW0 hW hτ
    have hw : 0 ≤ trimmedSpatialWidths Wsite τ N (some k,i) := by
      dsimp only [trimmedSpatialWidths, centeredSpatialWidths]
      positivity
    have hc := Int.le_ceil (trimmedSpatialWidths Wsite τ N (some k,i))
    have hlen : trimmedSpatialWidths Wsite τ N (some k,i) ≤
        ((jointFrameSourceHi N (trimmedSpatialWidths Wsite τ N) (some k,i) -
          jointFrameSourceLo (trimmedSpatialWidths Wsite τ N) (some k,i) : ℤ) : ℝ) := by
      dsimp only [jointFrameSourceHi, jointFrameSourceLo]
      push_cast
      linarith
    have hlen' : τ * ((N i : ℝ) / (8 * (1 + Wsite))) ≤
        ((jointFrameSourceHi N (trimmedSpatialWidths Wsite τ N) (some k,i) -
          jointFrameSourceLo (trimmedSpatialWidths Wsite τ N) (some k,i) : ℤ) : ℝ) := by
      simpa only [trimmedSpatialWidths, centeredSpatialWidths, one_mul] using hlen
    exact hs.trans (mul_le_mul_of_nonneg_left hlen' (by linarith))

theorem canonicalJointFrame_source_geometry {K I : Type*} [Fintype K] [Fintype I]
    (d : ℕ) (N : I → ℕ) {L Wsite τ : ℝ}
    (hL : 1 ≤ L) (hWL : L ≤ Wsite) (hW : Wsite ≤ 2 * (d : ℝ) * L)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hwide : ∀ i, 1 ≤ τ * ((N i : ℝ) / (8 * (1 + Wsite)))) :
    let width := trimmedSpatialWidths (K := K) Wsite τ N
    (∀ t, smoothPairCoefficientScale (2 * (N t.2 : ℝ)) L t.1 ≤
      canonicalJointFrameWindowConstant d τ *
        ((jointFrameSourceHi N width t - jointFrameSourceLo width t : ℤ) : ℝ)) ∧
    (∀ z ∈ Fintype.piFinset (fun t => Finset.Ico (jointFrameSourceLo width t)
        (jointFrameSourceHi N width t)), ∀ t,
      |(z t : ℝ) - (0 : ℤ)| ≤ smoothPairCoefficientScale (2 * (N t.2 : ℝ)) L t.1 / 2) ∧
    (∀ k i, |(jointFrameSourceLo width (some k,i) : ℝ)| ≤ 2 * (N i : ℝ) / L) ∧
    (∀ k i, |(jointFrameSourceHi N width (some k,i) : ℝ)| ≤ 2 * (N i : ℝ) / L) := by
  intro width
  have hW0 : 0 ≤ Wsite := by linarith
  have hwidth : ∀ k i, 1 ≤ width (some k,i) := by
    intro k i
    simpa only [width, trimmedSpatialWidths, centeredSpatialWidths, one_mul] using hwide i
  have hsmall : ∀ k i, 3 * width (some k,i) ≤ (N i : ℝ) / L :=
    canonicalJointFrame_slope_small N hL hWL hτ hτ1
  obtain ⟨hwindow, hlo, hhi⟩ := jointFrameSource_window_bounds N width
    (lt_of_lt_of_le zero_lt_one hL) hwidth hsmall
  refine ⟨canonicalJointFrame_source_scale d N hL hW0 hW hτ hτ1, ?_, hlo, hhi⟩
  simpa only [Int.cast_zero, sub_zero] using hwindow

end Erdos3.BooleanCubeKernel

end

end OAI
