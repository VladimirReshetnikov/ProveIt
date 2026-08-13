/-
This file is generated.  Do not edit it directly.

Regenerate with `Algebra/PolynomialFormulas/Tools/generate_fin5_transitive_classification_certificates.py` and verify with
`Algebra/PolynomialFormulas/Tools/generate_fin5_transitive_classification_certificates.py --check`.  Python supplies data only; every theorem
below is checked by Lean using ordinary kernel reduction.
-/

import PolynomialFormulas.Fin5TransitiveClassificationGenerationCore

namespace LeanProofs.PolynomialFormulas.Fin5TransitiveClassificationCertificates

def symmetric0Stage0 : Finset S5 := {1}

def symmetric0Stage1Codes : Finset ℕ :=
  [586, 2154, 2430, 2930].toFinset

def symmetric0Stage1 : Finset S5 :=
  elementsWithCodes symmetric0Stage1Codes

def symmetric0Stage2Codes : Finset ℕ :=
  [486, 586, 742, 1398, 1654, 2154, 2430, 2586, 2778, 2930].toFinset

def symmetric0Stage2 : Finset S5 :=
  elementsWithCodes symmetric0Stage2Codes

def symmetric0Stage3Codes : Finset ℕ :=
  [242, 434, 486, 586, 722, 742, 898, 1142, 1394, 1398,
   1654, 1778, 1986, 2022, 2154, 2430, 2586, 2778, 2830, 2930].toFinset

def symmetric0Stage3 : Finset S5 :=
  elementsWithCodes symmetric0Stage3Codes

def symmetric0Stage4Codes : Finset ℕ :=
  [222, 242, 434, 486, 558, 566, 586, 722, 738, 742,
   894, 898, 1022, 1142, 1210, 1298, 1366, 1394, 1398, 1478,
   1654, 1778, 1830, 1934, 1986, 2022, 2054, 2154, 2170, 2230,
   2430, 2586, 2642, 2778, 2830, 2930].toFinset

def symmetric0Stage4 : Finset S5 :=
  elementsWithCodes symmetric0Stage4Codes

def symmetric0CheckpointCodes : Finset ℕ :=
  [222, 238, 242, 298, 366, 434, 446, 486, 558, 566,
   582, 586, 714, 722, 738, 742, 894, 898, 978, 1022,
   1054, 1110, 1142, 1210, 1294, 1298, 1346, 1366, 1394, 1398,
   1454, 1478, 1654, 1670, 1730, 1778, 1830, 1934, 1986, 2022,
   2054, 2134, 2154, 2170, 2230, 2430, 2558, 2566, 2586, 2642,
   2678, 2710, 2778, 2790, 2830, 2886, 2902, 2910, 2926, 2930].toFinset

def symmetric0Checkpoint : Finset S5 :=
  elementsWithCodes symmetric0CheckpointCodes

def symmetric0Stage6Codes : Finset ℕ :=
  [214, 222, 238, 242, 294, 298, 334, 346, 366, 434,
   446, 482, 486, 542, 558, 566, 582, 586, 698, 714,
   722, 738, 742, 894, 898, 954, 978, 1022, 1054, 1110,
   1138, 1142, 1178, 1190, 1202, 1210, 1294, 1298, 1346, 1366,
   1394, 1398, 1454, 1478, 1490, 1634, 1654, 1670, 1730, 1766,
   1778, 1790, 1830, 1922, 1934, 1946, 1986, 2014, 2022, 2054,
   2070, 2102, 2110, 2134, 2146, 2154, 2170, 2230, 2386, 2402,
   2410, 2426, 2430, 2558, 2566, 2582, 2586, 2642, 2678, 2710,
   2758, 2778, 2790, 2830, 2886, 2902, 2910, 2926, 2930].toFinset

def symmetric0Stage6 : Finset S5 :=
  elementsWithCodes symmetric0Stage6Codes

def symmetric0Stage7Codes : Finset ℕ :=
  [198, 214, 222, 238, 242, 294, 298, 334, 346, 358,
   366, 414, 422, 434, 446, 482, 486, 542, 558, 566,
   582, 586, 694, 698, 714, 722, 738, 742, 894, 898,
   954, 978, 990, 1014, 1022, 1054, 1070, 1102, 1110, 1138,
   1142, 1178, 1190, 1202, 1210, 1294, 1298, 1334, 1346, 1358,
   1366, 1394, 1398, 1454, 1470, 1478, 1490, 1634, 1646, 1654,
   1670, 1730, 1758, 1766, 1778, 1790, 1830, 1922, 1934, 1946,
   1982, 1986, 2014, 2022, 2054, 2070, 2102, 2110, 2134, 2146,
   2154, 2170, 2230, 2386, 2402, 2410, 2426, 2430, 2542, 2558,
   2566, 2582, 2586, 2638, 2642, 2678, 2690, 2702, 2710, 2758,
   2766, 2778, 2790, 2826, 2830, 2886, 2902, 2910, 2926, 2930].toFinset

def symmetric0Stage7 : Finset S5 :=
  elementsWithCodes symmetric0Stage7Codes

def symmetric0Stage8Codes : Finset ℕ :=
  [194, 198, 214, 222, 238, 242, 294, 298, 334, 346,
   358, 366, 414, 422, 434, 446, 482, 486, 538, 542,
   558, 566, 582, 586, 694, 698, 714, 722, 738, 742,
   894, 898, 954, 970, 978, 990, 1014, 1022, 1054, 1070,
   1102, 1110, 1138, 1142, 1178, 1190, 1202, 1210, 1294, 1298,
   1334, 1346, 1358, 1366, 1394, 1398, 1454, 1470, 1478, 1490,
   1634, 1646, 1654, 1670, 1730, 1758, 1766, 1778, 1790, 1826,
   1830, 1914, 1922, 1934, 1946, 1982, 1986, 2014, 2022, 2054,
   2070, 2102, 2110, 2134, 2146, 2154, 2170, 2226, 2230, 2386,
   2402, 2410, 2426, 2430, 2542, 2558, 2566, 2582, 2586, 2638,
   2642, 2678, 2690, 2702, 2710, 2758, 2766, 2778, 2790, 2826,
   2830, 2886, 2902, 2910, 2926, 2930].toFinset

def symmetric0Stage8 : Finset S5 :=
  elementsWithCodes symmetric0Stage8Codes

def symmetric0Stage9Codes : Finset ℕ :=
  [194, 198, 214, 222, 238, 242, 294, 298, 334, 346,
   358, 366, 414, 422, 434, 446, 482, 486, 538, 542,
   558, 566, 582, 586, 694, 698, 714, 722, 738, 742,
   894, 898, 954, 970, 978, 990, 1014, 1022, 1054, 1070,
   1102, 1110, 1138, 1142, 1178, 1190, 1202, 1210, 1294, 1298,
   1334, 1346, 1358, 1366, 1394, 1398, 1454, 1470, 1478, 1490,
   1634, 1646, 1654, 1670, 1726, 1730, 1758, 1766, 1778, 1790,
   1826, 1830, 1914, 1922, 1934, 1946, 1982, 1986, 2014, 2022,
   2054, 2070, 2102, 2110, 2134, 2146, 2154, 2170, 2226, 2230,
   2386, 2402, 2410, 2426, 2430, 2538, 2542, 2558, 2566, 2582,
   2586, 2638, 2642, 2678, 2690, 2702, 2710, 2758, 2766, 2778,
   2790, 2826, 2830, 2882, 2886, 2902, 2910, 2926, 2930].toFinset

def symmetric0Stage9 : Finset S5 :=
  elementsWithCodes symmetric0Stage9Codes


def symmetric0Step0Added0Codes : Finset ℕ :=
  [586].toFinset

def symmetric0Step0Added0 : Finset S5 :=
  elementsWithCodes symmetric0Step0Added0Codes

def symmetric0Step0Added1Codes : Finset ℕ :=
  [2154].toFinset

def symmetric0Step0Added1 : Finset S5 :=
  elementsWithCodes symmetric0Step0Added1Codes

def symmetric0Step0Added2Codes : Finset ℕ :=
  [2430].toFinset

def symmetric0Step0Added2 : Finset S5 :=
  elementsWithCodes symmetric0Step0Added2Codes

set_option maxRecDepth 100000 in
theorem symmetric0_step_0_source_subset_certificate :
    ∀ x : S5, x ∈ symmetric0Stage0 → x ∈ symmetric0Stage1 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_0_rotation_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Stage0 →
      fiveCycle * x ∈ symmetric0Stage1 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_0_rotationInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Stage0 →
      fiveCycle⁻¹ * x ∈ symmetric0Stage1 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_0_generator_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Stage0 →
      representative 6 * x ∈ symmetric0Stage1 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_0_generatorInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Stage0 →
      (representative 6)⁻¹ * x ∈ symmetric0Stage1 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_0_lower_cases_certificate :
    ∀ x : S5, x ∈ symmetric0Stage1 →
      x ∈ symmetric0Stage0 ∨
        x ∈ symmetric0Step0Added0 ∨
        x ∈ symmetric0Step0Added1 ∨
        x ∈ symmetric0Step0Added2 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_0_added_0_preimage_certificate :
    ∀ x : S5, x ∈ symmetric0Step0Added0 →
      (fiveCycle)⁻¹ * x ∈ symmetric0Stage0 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_0_added_1_preimage_certificate :
    ∀ x : S5, x ∈ symmetric0Step0Added1 →
      (fiveCycle⁻¹)⁻¹ * x ∈ symmetric0Stage0 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_0_added_2_preimage_certificate :
    ∀ x : S5, x ∈ symmetric0Step0Added2 →
      (representative 6)⁻¹ * x ∈ symmetric0Stage0 := by
  decide


/-- Structural assembly of one S5 breadth step; the kernel computations above
check only membership implications and explicit inverse witnesses. -/
theorem symmetric0_step_0_certificate :
    generationStep (representative 6) symmetric0Stage0 =
      symmetric0Stage1 := by
  apply Finset.Subset.antisymm
  · intro x hx
    simp only [generationStep, Finset.mem_union] at hx
    rcases hx with ((((hsource | hrotation) | hrotationInv) | hgenerator) | hgeneratorInv)
    · exact symmetric0_step_0_source_subset_certificate x hsource
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotation
      exact symmetric0_step_0_rotation_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotationInv
      exact symmetric0_step_0_rotationInv_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgenerator
      exact symmetric0_step_0_generator_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgeneratorInv
      exact symmetric0_step_0_generatorInv_closed_certificate y hy
  · intro x hx
    have hcases := symmetric0_step_0_lower_cases_certificate x hx
    rcases hcases with hsource | hadded0 | hadded1 | hadded2
    · simp [generationStep, hsource]
    · have hpre := symmetric0_step_0_added_0_preimage_certificate x hadded0
      have himage :
          x ∈ symmetric0Stage0.image (fun y ↦ fiveCycle * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (Or.inr himage)))
    · have hpre := symmetric0_step_0_added_1_preimage_certificate x hadded1
      have himage :
          x ∈ symmetric0Stage0.image (fun y ↦ fiveCycle⁻¹ * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle⁻¹)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inr himage))
    · have hpre := symmetric0_step_0_added_2_preimage_certificate x hadded2
      have himage :
          x ∈ symmetric0Stage0.image (fun y ↦ representative 6 * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(representative 6)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inr himage)

def symmetric0Step1Added0Codes : Finset ℕ :=
  [742, 2586].toFinset

def symmetric0Step1Added0 : Finset S5 :=
  elementsWithCodes symmetric0Step1Added0Codes

def symmetric0Step1Added1Codes : Finset ℕ :=
  [1398, 1654].toFinset

def symmetric0Step1Added1 : Finset S5 :=
  elementsWithCodes symmetric0Step1Added1Codes

def symmetric0Step1Added2Codes : Finset ℕ :=
  [486, 2778].toFinset

def symmetric0Step1Added2 : Finset S5 :=
  elementsWithCodes symmetric0Step1Added2Codes

set_option maxRecDepth 100000 in
theorem symmetric0_step_1_source_subset_certificate :
    ∀ x : S5, x ∈ symmetric0Stage1 → x ∈ symmetric0Stage2 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_1_rotation_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Stage1 →
      fiveCycle * x ∈ symmetric0Stage2 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_1_rotationInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Stage1 →
      fiveCycle⁻¹ * x ∈ symmetric0Stage2 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_1_generator_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Stage1 →
      representative 6 * x ∈ symmetric0Stage2 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_1_generatorInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Stage1 →
      (representative 6)⁻¹ * x ∈ symmetric0Stage2 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_1_lower_cases_certificate :
    ∀ x : S5, x ∈ symmetric0Stage2 →
      x ∈ symmetric0Stage1 ∨
        x ∈ symmetric0Step1Added0 ∨
        x ∈ symmetric0Step1Added1 ∨
        x ∈ symmetric0Step1Added2 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_1_added_0_preimage_certificate :
    ∀ x : S5, x ∈ symmetric0Step1Added0 →
      (fiveCycle)⁻¹ * x ∈ symmetric0Stage1 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_1_added_1_preimage_certificate :
    ∀ x : S5, x ∈ symmetric0Step1Added1 →
      (fiveCycle⁻¹)⁻¹ * x ∈ symmetric0Stage1 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_1_added_2_preimage_certificate :
    ∀ x : S5, x ∈ symmetric0Step1Added2 →
      (representative 6)⁻¹ * x ∈ symmetric0Stage1 := by
  decide


/-- Structural assembly of one S5 breadth step; the kernel computations above
check only membership implications and explicit inverse witnesses. -/
theorem symmetric0_step_1_certificate :
    generationStep (representative 6) symmetric0Stage1 =
      symmetric0Stage2 := by
  apply Finset.Subset.antisymm
  · intro x hx
    simp only [generationStep, Finset.mem_union] at hx
    rcases hx with ((((hsource | hrotation) | hrotationInv) | hgenerator) | hgeneratorInv)
    · exact symmetric0_step_1_source_subset_certificate x hsource
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotation
      exact symmetric0_step_1_rotation_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotationInv
      exact symmetric0_step_1_rotationInv_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgenerator
      exact symmetric0_step_1_generator_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgeneratorInv
      exact symmetric0_step_1_generatorInv_closed_certificate y hy
  · intro x hx
    have hcases := symmetric0_step_1_lower_cases_certificate x hx
    rcases hcases with hsource | hadded0 | hadded1 | hadded2
    · simp [generationStep, hsource]
    · have hpre := symmetric0_step_1_added_0_preimage_certificate x hadded0
      have himage :
          x ∈ symmetric0Stage1.image (fun y ↦ fiveCycle * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (Or.inr himage)))
    · have hpre := symmetric0_step_1_added_1_preimage_certificate x hadded1
      have himage :
          x ∈ symmetric0Stage1.image (fun y ↦ fiveCycle⁻¹ * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle⁻¹)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inr himage))
    · have hpre := symmetric0_step_1_added_2_preimage_certificate x hadded2
      have himage :
          x ∈ symmetric0Stage1.image (fun y ↦ representative 6 * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(representative 6)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inr himage)

def symmetric0Step2Added0Codes : Finset ℕ :=
  [242, 434, 1142].toFinset

def symmetric0Step2Added0 : Finset S5 :=
  elementsWithCodes symmetric0Step2Added0Codes

def symmetric0Step2Added1Codes : Finset ℕ :=
  [898, 2022, 2830].toFinset

def symmetric0Step2Added1 : Finset S5 :=
  elementsWithCodes symmetric0Step2Added1Codes

def symmetric0Step2Added2Codes : Finset ℕ :=
  [722, 1394, 1778, 1986].toFinset

def symmetric0Step2Added2 : Finset S5 :=
  elementsWithCodes symmetric0Step2Added2Codes

set_option maxRecDepth 100000 in
theorem symmetric0_step_2_source_subset_certificate :
    ∀ x : S5, x ∈ symmetric0Stage2 → x ∈ symmetric0Stage3 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_2_rotation_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Stage2 →
      fiveCycle * x ∈ symmetric0Stage3 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_2_rotationInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Stage2 →
      fiveCycle⁻¹ * x ∈ symmetric0Stage3 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_2_generator_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Stage2 →
      representative 6 * x ∈ symmetric0Stage3 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_2_generatorInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Stage2 →
      (representative 6)⁻¹ * x ∈ symmetric0Stage3 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_2_lower_cases_certificate :
    ∀ x : S5, x ∈ symmetric0Stage3 →
      x ∈ symmetric0Stage2 ∨
        x ∈ symmetric0Step2Added0 ∨
        x ∈ symmetric0Step2Added1 ∨
        x ∈ symmetric0Step2Added2 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_2_added_0_preimage_certificate :
    ∀ x : S5, x ∈ symmetric0Step2Added0 →
      (fiveCycle)⁻¹ * x ∈ symmetric0Stage2 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_2_added_1_preimage_certificate :
    ∀ x : S5, x ∈ symmetric0Step2Added1 →
      (fiveCycle⁻¹)⁻¹ * x ∈ symmetric0Stage2 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_2_added_2_preimage_certificate :
    ∀ x : S5, x ∈ symmetric0Step2Added2 →
      (representative 6)⁻¹ * x ∈ symmetric0Stage2 := by
  decide


/-- Structural assembly of one S5 breadth step; the kernel computations above
check only membership implications and explicit inverse witnesses. -/
theorem symmetric0_step_2_certificate :
    generationStep (representative 6) symmetric0Stage2 =
      symmetric0Stage3 := by
  apply Finset.Subset.antisymm
  · intro x hx
    simp only [generationStep, Finset.mem_union] at hx
    rcases hx with ((((hsource | hrotation) | hrotationInv) | hgenerator) | hgeneratorInv)
    · exact symmetric0_step_2_source_subset_certificate x hsource
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotation
      exact symmetric0_step_2_rotation_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotationInv
      exact symmetric0_step_2_rotationInv_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgenerator
      exact symmetric0_step_2_generator_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgeneratorInv
      exact symmetric0_step_2_generatorInv_closed_certificate y hy
  · intro x hx
    have hcases := symmetric0_step_2_lower_cases_certificate x hx
    rcases hcases with hsource | hadded0 | hadded1 | hadded2
    · simp [generationStep, hsource]
    · have hpre := symmetric0_step_2_added_0_preimage_certificate x hadded0
      have himage :
          x ∈ symmetric0Stage2.image (fun y ↦ fiveCycle * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (Or.inr himage)))
    · have hpre := symmetric0_step_2_added_1_preimage_certificate x hadded1
      have himage :
          x ∈ symmetric0Stage2.image (fun y ↦ fiveCycle⁻¹ * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle⁻¹)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inr himage))
    · have hpre := symmetric0_step_2_added_2_preimage_certificate x hadded2
      have himage :
          x ∈ symmetric0Stage2.image (fun y ↦ representative 6 * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(representative 6)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inr himage)

def symmetric0Step3Added0Codes : Finset ℕ :=
  [1210, 1298, 1478, 1934, 2170, 2642].toFinset

def symmetric0Step3Added0 : Finset S5 :=
  elementsWithCodes symmetric0Step3Added0Codes

def symmetric0Step3Added1Codes : Finset ℕ :=
  [566, 738, 1022, 1366, 1830, 2054].toFinset

def symmetric0Step3Added1 : Finset S5 :=
  elementsWithCodes symmetric0Step3Added1Codes

def symmetric0Step3Added2Codes : Finset ℕ :=
  [222, 558, 894, 2230].toFinset

def symmetric0Step3Added2 : Finset S5 :=
  elementsWithCodes symmetric0Step3Added2Codes

set_option maxRecDepth 100000 in
theorem symmetric0_step_3_source_subset_certificate :
    ∀ x : S5, x ∈ symmetric0Stage3 → x ∈ symmetric0Stage4 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_3_rotation_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Stage3 →
      fiveCycle * x ∈ symmetric0Stage4 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_3_rotationInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Stage3 →
      fiveCycle⁻¹ * x ∈ symmetric0Stage4 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_3_generator_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Stage3 →
      representative 6 * x ∈ symmetric0Stage4 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_3_generatorInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Stage3 →
      (representative 6)⁻¹ * x ∈ symmetric0Stage4 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_3_lower_cases_certificate :
    ∀ x : S5, x ∈ symmetric0Stage4 →
      x ∈ symmetric0Stage3 ∨
        x ∈ symmetric0Step3Added0 ∨
        x ∈ symmetric0Step3Added1 ∨
        x ∈ symmetric0Step3Added2 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_3_added_0_preimage_certificate :
    ∀ x : S5, x ∈ symmetric0Step3Added0 →
      (fiveCycle)⁻¹ * x ∈ symmetric0Stage3 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_3_added_1_preimage_certificate :
    ∀ x : S5, x ∈ symmetric0Step3Added1 →
      (fiveCycle⁻¹)⁻¹ * x ∈ symmetric0Stage3 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_3_added_2_preimage_certificate :
    ∀ x : S5, x ∈ symmetric0Step3Added2 →
      (representative 6)⁻¹ * x ∈ symmetric0Stage3 := by
  decide


/-- Structural assembly of one S5 breadth step; the kernel computations above
check only membership implications and explicit inverse witnesses. -/
theorem symmetric0_step_3_certificate :
    generationStep (representative 6) symmetric0Stage3 =
      symmetric0Stage4 := by
  apply Finset.Subset.antisymm
  · intro x hx
    simp only [generationStep, Finset.mem_union] at hx
    rcases hx with ((((hsource | hrotation) | hrotationInv) | hgenerator) | hgeneratorInv)
    · exact symmetric0_step_3_source_subset_certificate x hsource
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotation
      exact symmetric0_step_3_rotation_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotationInv
      exact symmetric0_step_3_rotationInv_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgenerator
      exact symmetric0_step_3_generator_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgeneratorInv
      exact symmetric0_step_3_generatorInv_closed_certificate y hy
  · intro x hx
    have hcases := symmetric0_step_3_lower_cases_certificate x hx
    rcases hcases with hsource | hadded0 | hadded1 | hadded2
    · simp [generationStep, hsource]
    · have hpre := symmetric0_step_3_added_0_preimage_certificate x hadded0
      have himage :
          x ∈ symmetric0Stage3.image (fun y ↦ fiveCycle * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (Or.inr himage)))
    · have hpre := symmetric0_step_3_added_1_preimage_certificate x hadded1
      have himage :
          x ∈ symmetric0Stage3.image (fun y ↦ fiveCycle⁻¹ * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle⁻¹)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inr himage))
    · have hpre := symmetric0_step_3_added_2_preimage_certificate x hadded2
      have himage :
          x ∈ symmetric0Stage3.image (fun y ↦ representative 6 * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(representative 6)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inr himage)

def symmetric0Step4Added0Codes : Finset ℕ :=
  [298, 714, 978, 1670, 2134, 2710, 2886, 2926].toFinset

def symmetric0Step4Added0 : Finset S5 :=
  elementsWithCodes symmetric0Step4Added0Codes

def symmetric0Step4Added1Codes : Finset ℕ :=
  [238, 366, 582, 1054, 1454, 2566, 2902, 2910].toFinset

def symmetric0Step4Added1 : Finset S5 :=
  elementsWithCodes symmetric0Step4Added1Codes

def symmetric0Step4Added2Codes : Finset ℕ :=
  [446, 1110, 1294, 1346, 1730, 2558, 2678, 2790].toFinset

def symmetric0Step4Added2 : Finset S5 :=
  elementsWithCodes symmetric0Step4Added2Codes

set_option maxRecDepth 100000 in
theorem symmetric0_step_4_source_subset_certificate :
    ∀ x : S5, x ∈ symmetric0Stage4 → x ∈ symmetric0Checkpoint := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_4_rotation_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Stage4 →
      fiveCycle * x ∈ symmetric0Checkpoint := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_4_rotationInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Stage4 →
      fiveCycle⁻¹ * x ∈ symmetric0Checkpoint := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_4_generator_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Stage4 →
      representative 6 * x ∈ symmetric0Checkpoint := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_4_generatorInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Stage4 →
      (representative 6)⁻¹ * x ∈ symmetric0Checkpoint := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_4_lower_cases_certificate :
    ∀ x : S5, x ∈ symmetric0Checkpoint →
      x ∈ symmetric0Stage4 ∨
        x ∈ symmetric0Step4Added0 ∨
        x ∈ symmetric0Step4Added1 ∨
        x ∈ symmetric0Step4Added2 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_4_added_0_preimage_certificate :
    ∀ x : S5, x ∈ symmetric0Step4Added0 →
      (fiveCycle)⁻¹ * x ∈ symmetric0Stage4 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_4_added_1_preimage_certificate :
    ∀ x : S5, x ∈ symmetric0Step4Added1 →
      (fiveCycle⁻¹)⁻¹ * x ∈ symmetric0Stage4 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_4_added_2_preimage_certificate :
    ∀ x : S5, x ∈ symmetric0Step4Added2 →
      (representative 6)⁻¹ * x ∈ symmetric0Stage4 := by
  decide


/-- Structural assembly of one S5 breadth step; the kernel computations above
check only membership implications and explicit inverse witnesses. -/
theorem symmetric0_step_4_certificate :
    generationStep (representative 6) symmetric0Stage4 =
      symmetric0Checkpoint := by
  apply Finset.Subset.antisymm
  · intro x hx
    simp only [generationStep, Finset.mem_union] at hx
    rcases hx with ((((hsource | hrotation) | hrotationInv) | hgenerator) | hgeneratorInv)
    · exact symmetric0_step_4_source_subset_certificate x hsource
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotation
      exact symmetric0_step_4_rotation_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotationInv
      exact symmetric0_step_4_rotationInv_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgenerator
      exact symmetric0_step_4_generator_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgeneratorInv
      exact symmetric0_step_4_generatorInv_closed_certificate y hy
  · intro x hx
    have hcases := symmetric0_step_4_lower_cases_certificate x hx
    rcases hcases with hsource | hadded0 | hadded1 | hadded2
    · simp [generationStep, hsource]
    · have hpre := symmetric0_step_4_added_0_preimage_certificate x hadded0
      have himage :
          x ∈ symmetric0Stage4.image (fun y ↦ fiveCycle * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (Or.inr himage)))
    · have hpre := symmetric0_step_4_added_1_preimage_certificate x hadded1
      have himage :
          x ∈ symmetric0Stage4.image (fun y ↦ fiveCycle⁻¹ * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle⁻¹)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inr himage))
    · have hpre := symmetric0_step_4_added_2_preimage_certificate x hadded2
      have himage :
          x ∈ symmetric0Stage4.image (fun y ↦ representative 6 * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(representative 6)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inr himage)


theorem symmetric0_checkpoint_certificate :
    generatedStage (representative 6) 5 =
      symmetric0Checkpoint := by
  change generationStep (representative 6) (generationStep (representative 6) (generationStep (representative 6) (generationStep (representative 6) (generationStep (representative 6) (symmetric0Stage0))))) = symmetric0Checkpoint
  rw [symmetric0_step_0_certificate, symmetric0_step_1_certificate, symmetric0_step_2_certificate, symmetric0_step_3_certificate, symmetric0_step_4_certificate]


def symmetric0Step5Added0Codes : Finset ℕ :=
  [214, 334, 542, 1202, 1490, 1634, 1766, 2070, 2102, 2386,
   2426].toFinset

def symmetric0Step5Added0 : Finset S5 :=
  elementsWithCodes symmetric0Step5Added0Codes

def symmetric0Step5Added1Codes : Finset ℕ :=
  [698, 954, 1138, 1190, 1922, 2014, 2146, 2402, 2410, 2582].toFinset

def symmetric0Step5Added1 : Finset S5 :=
  elementsWithCodes symmetric0Step5Added1Codes

def symmetric0Step5Added2Codes : Finset ℕ :=
  [294, 346, 482, 1178, 1790, 1946, 2110, 2758].toFinset

def symmetric0Step5Added2 : Finset S5 :=
  elementsWithCodes symmetric0Step5Added2Codes

set_option maxRecDepth 100000 in
theorem symmetric0_step_5_source_subset_certificate :
    ∀ x : S5, x ∈ symmetric0Checkpoint → x ∈ symmetric0Stage6 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_5_rotation_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Checkpoint →
      fiveCycle * x ∈ symmetric0Stage6 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_5_rotationInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Checkpoint →
      fiveCycle⁻¹ * x ∈ symmetric0Stage6 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_5_generator_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Checkpoint →
      representative 6 * x ∈ symmetric0Stage6 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_5_generatorInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Checkpoint →
      (representative 6)⁻¹ * x ∈ symmetric0Stage6 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_5_lower_cases_certificate :
    ∀ x : S5, x ∈ symmetric0Stage6 →
      x ∈ symmetric0Checkpoint ∨
        x ∈ symmetric0Step5Added0 ∨
        x ∈ symmetric0Step5Added1 ∨
        x ∈ symmetric0Step5Added2 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_5_added_0_preimage_certificate :
    ∀ x : S5, x ∈ symmetric0Step5Added0 →
      (fiveCycle)⁻¹ * x ∈ symmetric0Checkpoint := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_5_added_1_preimage_certificate :
    ∀ x : S5, x ∈ symmetric0Step5Added1 →
      (fiveCycle⁻¹)⁻¹ * x ∈ symmetric0Checkpoint := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_5_added_2_preimage_certificate :
    ∀ x : S5, x ∈ symmetric0Step5Added2 →
      (representative 6)⁻¹ * x ∈ symmetric0Checkpoint := by
  decide


/-- Structural assembly of one S5 breadth step; the kernel computations above
check only membership implications and explicit inverse witnesses. -/
theorem symmetric0_step_5_certificate :
    generationStep (representative 6) symmetric0Checkpoint =
      symmetric0Stage6 := by
  apply Finset.Subset.antisymm
  · intro x hx
    simp only [generationStep, Finset.mem_union] at hx
    rcases hx with ((((hsource | hrotation) | hrotationInv) | hgenerator) | hgeneratorInv)
    · exact symmetric0_step_5_source_subset_certificate x hsource
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotation
      exact symmetric0_step_5_rotation_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotationInv
      exact symmetric0_step_5_rotationInv_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgenerator
      exact symmetric0_step_5_generator_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgeneratorInv
      exact symmetric0_step_5_generatorInv_closed_certificate y hy
  · intro x hx
    have hcases := symmetric0_step_5_lower_cases_certificate x hx
    rcases hcases with hsource | hadded0 | hadded1 | hadded2
    · simp [generationStep, hsource]
    · have hpre := symmetric0_step_5_added_0_preimage_certificate x hadded0
      have himage :
          x ∈ symmetric0Checkpoint.image (fun y ↦ fiveCycle * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (Or.inr himage)))
    · have hpre := symmetric0_step_5_added_1_preimage_certificate x hadded1
      have himage :
          x ∈ symmetric0Checkpoint.image (fun y ↦ fiveCycle⁻¹ * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle⁻¹)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inr himage))
    · have hpre := symmetric0_step_5_added_2_preimage_certificate x hadded2
      have himage :
          x ∈ symmetric0Checkpoint.image (fun y ↦ representative 6 * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(representative 6)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inr himage)

def symmetric0Step6Added0Codes : Finset ℕ :=
  [414, 990, 1070, 1102, 1334, 1358, 2542, 2702, 2766, 2826].toFinset

def symmetric0Step6Added0 : Finset S5 :=
  elementsWithCodes symmetric0Step6Added0Codes

def symmetric0Step6Added1Codes : Finset ℕ :=
  [198, 422, 1014, 1646, 2638, 2690].toFinset

def symmetric0Step6Added1 : Finset S5 :=
  elementsWithCodes symmetric0Step6Added1Codes

def symmetric0Step6Added2Codes : Finset ℕ :=
  [358, 694, 1470, 1758, 1982].toFinset

def symmetric0Step6Added2 : Finset S5 :=
  elementsWithCodes symmetric0Step6Added2Codes

set_option maxRecDepth 100000 in
theorem symmetric0_step_6_source_subset_certificate :
    ∀ x : S5, x ∈ symmetric0Stage6 → x ∈ symmetric0Stage7 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_6_rotation_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Stage6 →
      fiveCycle * x ∈ symmetric0Stage7 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_6_rotationInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Stage6 →
      fiveCycle⁻¹ * x ∈ symmetric0Stage7 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_6_generator_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Stage6 →
      representative 6 * x ∈ symmetric0Stage7 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_6_generatorInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Stage6 →
      (representative 6)⁻¹ * x ∈ symmetric0Stage7 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_6_lower_cases_certificate :
    ∀ x : S5, x ∈ symmetric0Stage7 →
      x ∈ symmetric0Stage6 ∨
        x ∈ symmetric0Step6Added0 ∨
        x ∈ symmetric0Step6Added1 ∨
        x ∈ symmetric0Step6Added2 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_6_added_0_preimage_certificate :
    ∀ x : S5, x ∈ symmetric0Step6Added0 →
      (fiveCycle)⁻¹ * x ∈ symmetric0Stage6 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_6_added_1_preimage_certificate :
    ∀ x : S5, x ∈ symmetric0Step6Added1 →
      (fiveCycle⁻¹)⁻¹ * x ∈ symmetric0Stage6 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_6_added_2_preimage_certificate :
    ∀ x : S5, x ∈ symmetric0Step6Added2 →
      (representative 6)⁻¹ * x ∈ symmetric0Stage6 := by
  decide


/-- Structural assembly of one S5 breadth step; the kernel computations above
check only membership implications and explicit inverse witnesses. -/
theorem symmetric0_step_6_certificate :
    generationStep (representative 6) symmetric0Stage6 =
      symmetric0Stage7 := by
  apply Finset.Subset.antisymm
  · intro x hx
    simp only [generationStep, Finset.mem_union] at hx
    rcases hx with ((((hsource | hrotation) | hrotationInv) | hgenerator) | hgeneratorInv)
    · exact symmetric0_step_6_source_subset_certificate x hsource
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotation
      exact symmetric0_step_6_rotation_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotationInv
      exact symmetric0_step_6_rotationInv_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgenerator
      exact symmetric0_step_6_generator_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgeneratorInv
      exact symmetric0_step_6_generatorInv_closed_certificate y hy
  · intro x hx
    have hcases := symmetric0_step_6_lower_cases_certificate x hx
    rcases hcases with hsource | hadded0 | hadded1 | hadded2
    · simp [generationStep, hsource]
    · have hpre := symmetric0_step_6_added_0_preimage_certificate x hadded0
      have himage :
          x ∈ symmetric0Stage6.image (fun y ↦ fiveCycle * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (Or.inr himage)))
    · have hpre := symmetric0_step_6_added_1_preimage_certificate x hadded1
      have himage :
          x ∈ symmetric0Stage6.image (fun y ↦ fiveCycle⁻¹ * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle⁻¹)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inr himage))
    · have hpre := symmetric0_step_6_added_2_preimage_certificate x hadded2
      have himage :
          x ∈ symmetric0Stage6.image (fun y ↦ representative 6 * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(representative 6)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inr himage)

def symmetric0Step7Added0Codes : Finset ℕ :=
  [1826, 1914, 2226].toFinset

def symmetric0Step7Added0 : Finset S5 :=
  elementsWithCodes symmetric0Step7Added0Codes

def symmetric0Step7Added1Codes : Finset ℕ :=
  [538].toFinset

def symmetric0Step7Added1 : Finset S5 :=
  elementsWithCodes symmetric0Step7Added1Codes

def symmetric0Step7Added2Codes : Finset ℕ :=
  [194, 970].toFinset

def symmetric0Step7Added2 : Finset S5 :=
  elementsWithCodes symmetric0Step7Added2Codes

set_option maxRecDepth 100000 in
theorem symmetric0_step_7_source_subset_certificate :
    ∀ x : S5, x ∈ symmetric0Stage7 → x ∈ symmetric0Stage8 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_7_rotation_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Stage7 →
      fiveCycle * x ∈ symmetric0Stage8 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_7_rotationInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Stage7 →
      fiveCycle⁻¹ * x ∈ symmetric0Stage8 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_7_generator_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Stage7 →
      representative 6 * x ∈ symmetric0Stage8 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_7_generatorInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Stage7 →
      (representative 6)⁻¹ * x ∈ symmetric0Stage8 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_7_lower_cases_certificate :
    ∀ x : S5, x ∈ symmetric0Stage8 →
      x ∈ symmetric0Stage7 ∨
        x ∈ symmetric0Step7Added0 ∨
        x ∈ symmetric0Step7Added1 ∨
        x ∈ symmetric0Step7Added2 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_7_added_0_preimage_certificate :
    ∀ x : S5, x ∈ symmetric0Step7Added0 →
      (fiveCycle)⁻¹ * x ∈ symmetric0Stage7 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_7_added_1_preimage_certificate :
    ∀ x : S5, x ∈ symmetric0Step7Added1 →
      (fiveCycle⁻¹)⁻¹ * x ∈ symmetric0Stage7 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_7_added_2_preimage_certificate :
    ∀ x : S5, x ∈ symmetric0Step7Added2 →
      (representative 6)⁻¹ * x ∈ symmetric0Stage7 := by
  decide


/-- Structural assembly of one S5 breadth step; the kernel computations above
check only membership implications and explicit inverse witnesses. -/
theorem symmetric0_step_7_certificate :
    generationStep (representative 6) symmetric0Stage7 =
      symmetric0Stage8 := by
  apply Finset.Subset.antisymm
  · intro x hx
    simp only [generationStep, Finset.mem_union] at hx
    rcases hx with ((((hsource | hrotation) | hrotationInv) | hgenerator) | hgeneratorInv)
    · exact symmetric0_step_7_source_subset_certificate x hsource
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotation
      exact symmetric0_step_7_rotation_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotationInv
      exact symmetric0_step_7_rotationInv_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgenerator
      exact symmetric0_step_7_generator_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgeneratorInv
      exact symmetric0_step_7_generatorInv_closed_certificate y hy
  · intro x hx
    have hcases := symmetric0_step_7_lower_cases_certificate x hx
    rcases hcases with hsource | hadded0 | hadded1 | hadded2
    · simp [generationStep, hsource]
    · have hpre := symmetric0_step_7_added_0_preimage_certificate x hadded0
      have himage :
          x ∈ symmetric0Stage7.image (fun y ↦ fiveCycle * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (Or.inr himage)))
    · have hpre := symmetric0_step_7_added_1_preimage_certificate x hadded1
      have himage :
          x ∈ symmetric0Stage7.image (fun y ↦ fiveCycle⁻¹ * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle⁻¹)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inr himage))
    · have hpre := symmetric0_step_7_added_2_preimage_certificate x hadded2
      have himage :
          x ∈ symmetric0Stage7.image (fun y ↦ representative 6 * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(representative 6)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inr himage)

def symmetric0Step8Added0Codes : Finset ℕ :=
  [1726, 2882].toFinset

def symmetric0Step8Added0 : Finset S5 :=
  elementsWithCodes symmetric0Step8Added0Codes

def symmetric0Step8Added1Codes : Finset ℕ :=
  [2538].toFinset

def symmetric0Step8Added1 : Finset S5 :=
  elementsWithCodes symmetric0Step8Added1Codes

set_option maxRecDepth 100000 in
theorem symmetric0_step_8_source_subset_certificate :
    ∀ x : S5, x ∈ symmetric0Stage8 → x ∈ symmetric0Stage9 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_8_rotation_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Stage8 →
      fiveCycle * x ∈ symmetric0Stage9 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_8_rotationInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Stage8 →
      fiveCycle⁻¹ * x ∈ symmetric0Stage9 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_8_generator_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Stage8 →
      representative 6 * x ∈ symmetric0Stage9 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_8_generatorInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Stage8 →
      (representative 6)⁻¹ * x ∈ symmetric0Stage9 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_8_lower_cases_certificate :
    ∀ x : S5, x ∈ symmetric0Stage9 →
      x ∈ symmetric0Stage8 ∨
        x ∈ symmetric0Step8Added0 ∨
        x ∈ symmetric0Step8Added1 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_8_added_0_preimage_certificate :
    ∀ x : S5, x ∈ symmetric0Step8Added0 →
      (fiveCycle)⁻¹ * x ∈ symmetric0Stage8 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_8_added_1_preimage_certificate :
    ∀ x : S5, x ∈ symmetric0Step8Added1 →
      (fiveCycle⁻¹)⁻¹ * x ∈ symmetric0Stage8 := by
  decide


/-- Structural assembly of one S5 breadth step; the kernel computations above
check only membership implications and explicit inverse witnesses. -/
theorem symmetric0_step_8_certificate :
    generationStep (representative 6) symmetric0Stage8 =
      symmetric0Stage9 := by
  apply Finset.Subset.antisymm
  · intro x hx
    simp only [generationStep, Finset.mem_union] at hx
    rcases hx with ((((hsource | hrotation) | hrotationInv) | hgenerator) | hgeneratorInv)
    · exact symmetric0_step_8_source_subset_certificate x hsource
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotation
      exact symmetric0_step_8_rotation_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotationInv
      exact symmetric0_step_8_rotationInv_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgenerator
      exact symmetric0_step_8_generator_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgeneratorInv
      exact symmetric0_step_8_generatorInv_closed_certificate y hy
  · intro x hx
    have hcases := symmetric0_step_8_lower_cases_certificate x hx
    rcases hcases with hsource | hadded0 | hadded1
    · simp [generationStep, hsource]
    · have hpre := symmetric0_step_8_added_0_preimage_certificate x hadded0
      have himage :
          x ∈ symmetric0Stage8.image (fun y ↦ fiveCycle * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (Or.inr himage)))
    · have hpre := symmetric0_step_8_added_1_preimage_certificate x hadded1
      have himage :
          x ∈ symmetric0Stage8.image (fun y ↦ fiveCycle⁻¹ * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle⁻¹)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inr himage))

def symmetric0Step9Added0Codes : Finset ℕ :=
  [2382].toFinset

def symmetric0Step9Added0 : Finset S5 :=
  elementsWithCodes symmetric0Step9Added0Codes

set_option maxRecDepth 100000 in
theorem symmetric0_step_9_source_subset_certificate :
    ∀ x : S5, x ∈ symmetric0Stage9 → x ∈ classElements (representativeClass 6) := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_9_rotation_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Stage9 →
      fiveCycle * x ∈ classElements (representativeClass 6) := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_9_rotationInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Stage9 →
      fiveCycle⁻¹ * x ∈ classElements (representativeClass 6) := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_9_generator_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Stage9 →
      representative 6 * x ∈ classElements (representativeClass 6) := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_9_generatorInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric0Stage9 →
      (representative 6)⁻¹ * x ∈ classElements (representativeClass 6) := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_9_lower_cases_certificate :
    ∀ x : S5, x ∈ classElements (representativeClass 6) →
      x ∈ symmetric0Stage9 ∨
        x ∈ symmetric0Step9Added0 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric0_step_9_added_0_preimage_certificate :
    ∀ x : S5, x ∈ symmetric0Step9Added0 →
      (fiveCycle)⁻¹ * x ∈ symmetric0Stage9 := by
  decide


/-- Structural assembly of one S5 breadth step; the kernel computations above
check only membership implications and explicit inverse witnesses. -/
theorem symmetric0_step_9_certificate :
    generationStep (representative 6) symmetric0Stage9 =
      classElements (representativeClass 6) := by
  apply Finset.Subset.antisymm
  · intro x hx
    simp only [generationStep, Finset.mem_union] at hx
    rcases hx with ((((hsource | hrotation) | hrotationInv) | hgenerator) | hgeneratorInv)
    · exact symmetric0_step_9_source_subset_certificate x hsource
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotation
      exact symmetric0_step_9_rotation_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotationInv
      exact symmetric0_step_9_rotationInv_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgenerator
      exact symmetric0_step_9_generator_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgeneratorInv
      exact symmetric0_step_9_generatorInv_closed_certificate y hy
  · intro x hx
    have hcases := symmetric0_step_9_lower_cases_certificate x hx
    rcases hcases with hsource | hadded0
    · simp [generationStep, hsource]
    · have hpre := symmetric0_step_9_added_0_preimage_certificate x hadded0
      have himage :
          x ∈ symmetric0Stage9.image (fun y ↦ fiveCycle * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (Or.inr himage)))


theorem symmetric0_finish_certificate :
    iterateGenerationStep (representative 6)
      symmetric0Checkpoint 5 =
        classElements (representativeClass 6) := by
  change generationStep (representative 6) (generationStep (representative 6) (generationStep (representative 6) (generationStep (representative 6) (generationStep (representative 6) (symmetric0Checkpoint))))) = classElements (representativeClass 6)
  rw [symmetric0_step_5_certificate, symmetric0_step_6_certificate, symmetric0_step_7_certificate, symmetric0_step_8_certificate, symmetric0_step_9_certificate]

theorem symmetric0_generation_certificate :
    generatedStage (representative 6) (representativeDepth 6) =
      classElements (representativeClass 6) := by
  change generatedStage (representative 6) 10 =
    classElements (representativeClass 6)
  calc
    generatedStage (representative 6) 10 =
        iterateGenerationStep (representative 6)
          (generatedStage (representative 6) 5)
          5 := by
      simpa using generatedStage_add (representative 6)
        5 5
    _ = iterateGenerationStep (representative 6)
          symmetric0Checkpoint 5 := by
      rw [symmetric0_checkpoint_certificate]
    _ = classElements (representativeClass 6) :=
      symmetric0_finish_certificate

end LeanProofs.PolynomialFormulas.Fin5TransitiveClassificationCertificates
