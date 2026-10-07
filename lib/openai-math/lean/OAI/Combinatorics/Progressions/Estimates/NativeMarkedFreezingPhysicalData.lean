import OAI.Combinatorics.Progressions.Lattices.UniformExternalMarkedAffineSliceFreezingDictionary

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

noncomputable def nativeMarkedFreezingExponent (s a : ℕ) : ℕ :=
  Classical.choose
    (exists_uniform_external_marked_affine_slice_freezing_dictionary.{0, 0, 0, 0, 0} s a 3)

theorem nativeMarkedFreezingExponent_ge_two (s a : ℕ) :
    2 ≤ nativeMarkedFreezingExponent s a :=
  (Classical.choose_spec
    (exists_uniform_external_marked_affine_slice_freezing_dictionary.{0, 0, 0, 0, 0} s a 3)).1

def nativeMarkedFreezingPhysicalParameter (p : ℝ) (C : ℕ) : ℝ :=
  (p + 3) ^ 36 + (p + C) ^ C

theorem nativeMarkedFreezingPhysicalParameter_bounds {p : ℝ} (hp : 0 ≤ p) (C : ℕ) :
    p ≤ nativeMarkedFreezingPhysicalParameter p C ∧
      (p + C) ^ C ≤ nativeMarkedFreezingPhysicalParameter p C ∧
      (p + 3) ^ 7 ≤ nativeMarkedFreezingPhysicalParameter p C ∧
      p + 1 ≤ nativeMarkedFreezingPhysicalParameter p C := by
  have hbase : 1 ≤ p + 3 := by linarith
  have hpow : (p + 3) ^ 7 ≤ (p + 3) ^ 36 := pow_le_pow_right₀ hbase (by decide)
  have hinput : p + 1 ≤ (p + 3) ^ 36 := by
    simpa only [show p + 1 + 2 = p + 3 by ring] using
      (le_power_budget (show 0 ≤ p + 1 by linarith) (by decide : 1 ≤ 36))
  have hbudget : 0 ≤ (p + C) ^ C := by positivity
  have hfirst : (p + 3) ^ 36 ≤ nativeMarkedFreezingPhysicalParameter p C :=
    le_add_of_nonneg_right hbudget
  refine ⟨(by linarith [hinput.trans hfirst]), ?_, hpow.trans hfirst, hinput.trans hfirst⟩
  exact le_add_of_nonneg_left (by positivity)

variable {X σ κ L T : Type} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} (D : RationalFilteredNilmanifold L s d)
    (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T)
    (φ : L →ₗ⁅ℚ⁆ T) (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j)
    (w : σ → ℕ) (l : ℕ) (Tbox : σ → ℝ) (slow p : ℝ) (C : ℕ)

structure NativeMarkedFreezingPhysicalData where
  sectionMap : T →ₗ[ℚ] L
  section_filtered : ∀ j, ∀ y ∈ F.layer j, sectionMap y ∈ D.filtration.layer j
  section_rightInverse : Function.RightInverse sectionMap φ
  section_height : ∀ i j, RationalHeightLE
    (LinearMap.toMatrix c D.basis sectionMap i j)
    (rationalKernelHeight (Fintype.card κ) ⌈Real.exp p⌉₊)
  section_height_bound :
    (rationalKernelHeight (Fintype.card κ) ⌈Real.exp p⌉₊ : ℝ) ≤
      Real.exp (nativeMarkedFreezingPhysicalParameter p C)
  dictionary : ExternalMarkedAffineSliceFreezing.Dictionary (X := X)
    D F c φ hφ w sectionMap section_filtered l Tbox slow
    (Real.exp (-((p + 2) ^ 3))) (Real.exp ((p + C) ^ C))
  denominator_bound :
    ((matrixDenominator (LinearMap.toMatrix c D.basis sectionMap) * l *
      dictionary.denominator : ℕ) : ℝ) ≤
        Real.exp (nativeMarkedFreezingPhysicalParameter p C)

omit C in

theorem exists_nativeMarkedFreezingPhysicalData
    (a : ℕ)
    (ω : Fin d → ℕ)
    (hDlayers : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (τ : κ → ℕ)
    (hFlayers : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (hsurj : ∀ j, ∀ y ∈ F.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (hw : ∀ i, 0 < w i) (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p)
    (hσ : (Fintype.card σ : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hmap : ∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p)
    (hl : 0 < l) (hlp : (l : ℝ) ≤ Real.exp p)
    (hT : ∀ i, 0 < Tbox i) (hslow : slow ≤ Real.exp ((p + 2) ^ a)) :
    Nonempty (NativeMarkedFreezingPhysicalData (X := X) D F c φ hφ w l Tbox slow p
      (nativeMarkedFreezingExponent s a)) := by
  let C := nativeMarkedFreezingExponent s a
  obtain ⟨sectionMap, hsection, hright, hheight, hdict⟩ :=
    (Classical.choose_spec
      (exists_uniform_external_marked_affine_slice_freezing_dictionary.{0, 0, 0, 0, 0} s a 3)).2
      (X := X) D F c ω hDlayers τ hFlayers φ hφ hsurj w hw p hp hD hσ hκ hmap
  obtain ⟨dictionary⟩ := hdict l hl hlp Tbox hT slow hslow
  have hp1 : 0 ≤ p + 1 := by linarith
  have hp_le : p ≤ p + 1 := le_add_of_nonneg_right zero_le_one
  have hceil : (⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hmatrix : ∀ i j, RationalHeightLE (LinearMap.toMatrix c D.basis sectionMap i j)
      (rationalKernelHeight (Fintype.card κ) ⌈Real.exp p⌉₊) := by
    simpa only [LinearMap.toMatrix_apply] using hheight
  have hsectionBound := rationalKernelHeight_le_budget (Fintype.card κ) ⌈Real.exp p⌉₊
    hp1 (hκ.trans hp_le) hceil
  have hden := real_image_section_denominator_bound
    (LinearMap.toMatrix c D.basis sectionMap) ⌈Real.exp p⌉₊ l hmatrix hp1
    (hκ.trans hp_le) (by simpa only [Fintype.card_fin] using hD.1.trans hp_le)
    hceil (hlp.trans (Real.exp_le_exp.mpr hp_le))
  have hb := nativeMarkedFreezingPhysicalParameter_bounds hp C
  refine ⟨⟨sectionMap, hsection, hright, hmatrix, ?_, dictionary, ?_⟩⟩
  · exact hsectionBound.trans (Real.exp_le_exp.mpr (by
      simpa only [show p + 1 + 2 = p + 3 by ring] using hb.2.2.1))
  · calc
      _ = ((matrixDenominator (LinearMap.toMatrix c D.basis sectionMap) * l : ℕ) : ℝ) *
          dictionary.denominator := by rw [Nat.cast_mul]
      _ ≤ Real.exp ((p + 1 + 2) ^ 36) * Real.exp ((p + C) ^ C) :=
        mul_le_mul hden dictionary.denominator_bound (Nat.cast_nonneg _)
          (Real.exp_nonneg _)
      _ = Real.exp (nativeMarkedFreezingPhysicalParameter p C) := by
        rw [← Real.exp_add]
        congr 1
        simp only [nativeMarkedFreezingPhysicalParameter, show p + 1 + 2 = p + 3 by ring]

end Erdos3.RationalFilteredNilmanifold

end

end OAI
