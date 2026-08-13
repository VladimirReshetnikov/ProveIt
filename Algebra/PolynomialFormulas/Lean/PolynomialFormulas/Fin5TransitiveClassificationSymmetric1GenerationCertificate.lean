/-
This file is generated.  Do not edit it directly.

Regenerate with `Algebra/PolynomialFormulas/Tools/generate_fin5_transitive_classification_certificates.py` and verify with
`Algebra/PolynomialFormulas/Tools/generate_fin5_transitive_classification_certificates.py --check`.  Python supplies data only; every theorem
below is checked by Lean using ordinary kernel reduction.
-/

import PolynomialFormulas.Fin5TransitiveClassificationGenerationCore

namespace LeanProofs.PolynomialFormulas.Fin5TransitiveClassificationCertificates

def symmetric1Stage0 : Finset S5 := {1}

def symmetric1Stage1Codes : Finset ℕ :=
  [586, 1730, 2154, 2930].toFinset

def symmetric1Stage1 : Finset S5 :=
  elementsWithCodes symmetric1Stage1Codes

def symmetric1Stage2Codes : Finset ℕ :=
  [346, 586, 742, 954, 1398, 1730, 2154, 2386, 2402, 2930].toFinset

def symmetric1Stage2 : Finset S5 :=
  elementsWithCodes symmetric1Stage2Codes

def symmetric1Stage3Codes : Finset ℕ :=
  [198, 346, 586, 694, 742, 954, 1102, 1202, 1398, 1646,
   1730, 2146, 2154, 2386, 2402, 2542, 2558, 2638, 2690, 2930].toFinset

def symmetric1Stage3 : Finset S5 :=
  elementsWithCodes symmetric1Stage3Codes

def symmetric1Stage4Codes : Finset ℕ :=
  [198, 214, 238, 294, 346, 446, 538, 586, 694, 742,
   954, 990, 1054, 1102, 1202, 1294, 1358, 1398, 1470, 1490,
   1646, 1730, 1758, 1914, 1982, 2146, 2154, 2386, 2402, 2542,
   2558, 2638, 2690, 2886, 2902, 2930].toFinset

def symmetric1Stage4 : Finset S5 :=
  elementsWithCodes symmetric1Stage4Codes

def symmetric1CheckpointCodes : Finset ℕ :=
  [198, 214, 222, 238, 294, 298, 346, 446, 486, 538,
   542, 558, 586, 694, 714, 742, 894, 954, 990, 1054,
   1070, 1102, 1138, 1190, 1202, 1294, 1358, 1398, 1470, 1490,
   1646, 1654, 1730, 1758, 1826, 1830, 1914, 1922, 1934, 1982,
   2014, 2070, 2146, 2154, 2226, 2230, 2386, 2402, 2542, 2558,
   2582, 2638, 2690, 2710, 2758, 2790, 2882, 2886, 2902, 2930].toFinset

def symmetric1Checkpoint : Finset S5 :=
  elementsWithCodes symmetric1CheckpointCodes

def symmetric1Stage6Codes : Finset ℕ :=
  [198, 214, 222, 238, 294, 298, 346, 358, 366, 414,
   446, 482, 486, 538, 542, 558, 586, 694, 698, 714,
   722, 742, 894, 898, 954, 978, 990, 1054, 1070, 1102,
   1110, 1138, 1142, 1190, 1202, 1294, 1334, 1346, 1358, 1398,
   1454, 1470, 1490, 1634, 1646, 1654, 1670, 1730, 1758, 1766,
   1778, 1790, 1826, 1830, 1914, 1922, 1934, 1982, 1986, 2014,
   2022, 2070, 2102, 2110, 2146, 2154, 2226, 2230, 2386, 2402,
   2426, 2430, 2542, 2558, 2566, 2582, 2638, 2642, 2678, 2690,
   2710, 2758, 2790, 2826, 2830, 2882, 2886, 2902, 2930].toFinset

def symmetric1Stage6 : Finset S5 :=
  elementsWithCodes symmetric1Stage6Codes

def symmetric1Stage7Codes : Finset ℕ :=
  [198, 214, 222, 238, 242, 294, 298, 334, 346, 358,
   366, 414, 422, 434, 446, 482, 486, 538, 542, 558,
   566, 586, 694, 698, 714, 722, 738, 742, 894, 898,
   954, 978, 990, 1014, 1022, 1054, 1070, 1102, 1110, 1138,
   1142, 1178, 1190, 1202, 1294, 1298, 1334, 1346, 1358, 1366,
   1394, 1398, 1454, 1470, 1478, 1490, 1634, 1646, 1654, 1670,
   1730, 1758, 1766, 1778, 1790, 1826, 1830, 1914, 1922, 1934,
   1946, 1982, 1986, 2014, 2022, 2054, 2070, 2102, 2110, 2146,
   2154, 2226, 2230, 2386, 2402, 2410, 2426, 2430, 2542, 2558,
   2566, 2582, 2586, 2638, 2642, 2678, 2690, 2702, 2710, 2758,
   2766, 2778, 2790, 2826, 2830, 2882, 2886, 2902, 2910, 2930].toFinset

def symmetric1Stage7 : Finset S5 :=
  elementsWithCodes symmetric1Stage7Codes

def symmetric1Stage8Codes : Finset ℕ :=
  [194, 198, 214, 222, 238, 242, 294, 298, 334, 346,
   358, 366, 414, 422, 434, 446, 482, 486, 538, 542,
   558, 566, 582, 586, 694, 698, 714, 722, 738, 742,
   894, 898, 954, 978, 990, 1014, 1022, 1054, 1070, 1102,
   1110, 1138, 1142, 1178, 1190, 1202, 1210, 1294, 1298, 1334,
   1346, 1358, 1366, 1394, 1398, 1454, 1470, 1478, 1490, 1634,
   1646, 1654, 1670, 1730, 1758, 1766, 1778, 1790, 1826, 1830,
   1914, 1922, 1934, 1946, 1982, 1986, 2014, 2022, 2054, 2070,
   2102, 2110, 2134, 2146, 2154, 2170, 2226, 2230, 2386, 2402,
   2410, 2426, 2430, 2538, 2542, 2558, 2566, 2582, 2586, 2638,
   2642, 2678, 2690, 2702, 2710, 2758, 2766, 2778, 2790, 2826,
   2830, 2882, 2886, 2902, 2910, 2930].toFinset

def symmetric1Stage8 : Finset S5 :=
  elementsWithCodes symmetric1Stage8Codes

def symmetric1Stage9Codes : Finset ℕ :=
  [194, 198, 214, 222, 238, 242, 294, 298, 334, 346,
   358, 366, 414, 422, 434, 446, 482, 486, 538, 542,
   558, 566, 582, 586, 694, 698, 714, 722, 738, 742,
   894, 898, 954, 970, 978, 990, 1014, 1022, 1054, 1070,
   1102, 1110, 1138, 1142, 1178, 1190, 1202, 1210, 1294, 1298,
   1334, 1346, 1358, 1366, 1394, 1398, 1454, 1470, 1478, 1490,
   1634, 1646, 1654, 1670, 1730, 1758, 1766, 1778, 1790, 1826,
   1830, 1914, 1922, 1934, 1946, 1982, 1986, 2014, 2022, 2054,
   2070, 2102, 2110, 2134, 2146, 2154, 2170, 2226, 2230, 2382,
   2386, 2402, 2410, 2426, 2430, 2538, 2542, 2558, 2566, 2582,
   2586, 2638, 2642, 2678, 2690, 2702, 2710, 2758, 2766, 2778,
   2790, 2826, 2830, 2882, 2886, 2902, 2910, 2926, 2930].toFinset

def symmetric1Stage9 : Finset S5 :=
  elementsWithCodes symmetric1Stage9Codes


def symmetric1Step0Added0Codes : Finset ℕ :=
  [586].toFinset

def symmetric1Step0Added0 : Finset S5 :=
  elementsWithCodes symmetric1Step0Added0Codes

def symmetric1Step0Added1Codes : Finset ℕ :=
  [2154].toFinset

def symmetric1Step0Added1 : Finset S5 :=
  elementsWithCodes symmetric1Step0Added1Codes

def symmetric1Step0Added2Codes : Finset ℕ :=
  [1730].toFinset

def symmetric1Step0Added2 : Finset S5 :=
  elementsWithCodes symmetric1Step0Added2Codes

set_option maxRecDepth 100000 in
theorem symmetric1_step_0_source_subset_certificate :
    ∀ x : S5, x ∈ symmetric1Stage0 → x ∈ symmetric1Stage1 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_0_rotation_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Stage0 →
      fiveCycle * x ∈ symmetric1Stage1 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_0_rotationInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Stage0 →
      fiveCycle⁻¹ * x ∈ symmetric1Stage1 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_0_generator_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Stage0 →
      representative 7 * x ∈ symmetric1Stage1 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_0_generatorInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Stage0 →
      (representative 7)⁻¹ * x ∈ symmetric1Stage1 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_0_lower_cases_certificate :
    ∀ x : S5, x ∈ symmetric1Stage1 →
      x ∈ symmetric1Stage0 ∨
        x ∈ symmetric1Step0Added0 ∨
        x ∈ symmetric1Step0Added1 ∨
        x ∈ symmetric1Step0Added2 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_0_added_0_preimage_certificate :
    ∀ x : S5, x ∈ symmetric1Step0Added0 →
      (fiveCycle)⁻¹ * x ∈ symmetric1Stage0 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_0_added_1_preimage_certificate :
    ∀ x : S5, x ∈ symmetric1Step0Added1 →
      (fiveCycle⁻¹)⁻¹ * x ∈ symmetric1Stage0 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_0_added_2_preimage_certificate :
    ∀ x : S5, x ∈ symmetric1Step0Added2 →
      (representative 7)⁻¹ * x ∈ symmetric1Stage0 := by
  decide


/-- Structural assembly of one S5 breadth step; the kernel computations above
check only membership implications and explicit inverse witnesses. -/
theorem symmetric1_step_0_certificate :
    generationStep (representative 7) symmetric1Stage0 =
      symmetric1Stage1 := by
  apply Finset.Subset.antisymm
  · intro x hx
    simp only [generationStep, Finset.mem_union] at hx
    rcases hx with ((((hsource | hrotation) | hrotationInv) | hgenerator) | hgeneratorInv)
    · exact symmetric1_step_0_source_subset_certificate x hsource
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotation
      exact symmetric1_step_0_rotation_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotationInv
      exact symmetric1_step_0_rotationInv_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgenerator
      exact symmetric1_step_0_generator_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgeneratorInv
      exact symmetric1_step_0_generatorInv_closed_certificate y hy
  · intro x hx
    have hcases := symmetric1_step_0_lower_cases_certificate x hx
    rcases hcases with hsource | hadded0 | hadded1 | hadded2
    · simp [generationStep, hsource]
    · have hpre := symmetric1_step_0_added_0_preimage_certificate x hadded0
      have himage :
          x ∈ symmetric1Stage0.image (fun y ↦ fiveCycle * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (Or.inr himage)))
    · have hpre := symmetric1_step_0_added_1_preimage_certificate x hadded1
      have himage :
          x ∈ symmetric1Stage0.image (fun y ↦ fiveCycle⁻¹ * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle⁻¹)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inr himage))
    · have hpre := symmetric1_step_0_added_2_preimage_certificate x hadded2
      have himage :
          x ∈ symmetric1Stage0.image (fun y ↦ representative 7 * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(representative 7)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inr himage)

def symmetric1Step1Added0Codes : Finset ℕ :=
  [742, 2386].toFinset

def symmetric1Step1Added0 : Finset S5 :=
  elementsWithCodes symmetric1Step1Added0Codes

def symmetric1Step1Added1Codes : Finset ℕ :=
  [954, 1398].toFinset

def symmetric1Step1Added1 : Finset S5 :=
  elementsWithCodes symmetric1Step1Added1Codes

def symmetric1Step1Added2Codes : Finset ℕ :=
  [346, 2402].toFinset

def symmetric1Step1Added2 : Finset S5 :=
  elementsWithCodes symmetric1Step1Added2Codes

set_option maxRecDepth 100000 in
theorem symmetric1_step_1_source_subset_certificate :
    ∀ x : S5, x ∈ symmetric1Stage1 → x ∈ symmetric1Stage2 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_1_rotation_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Stage1 →
      fiveCycle * x ∈ symmetric1Stage2 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_1_rotationInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Stage1 →
      fiveCycle⁻¹ * x ∈ symmetric1Stage2 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_1_generator_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Stage1 →
      representative 7 * x ∈ symmetric1Stage2 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_1_generatorInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Stage1 →
      (representative 7)⁻¹ * x ∈ symmetric1Stage2 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_1_lower_cases_certificate :
    ∀ x : S5, x ∈ symmetric1Stage2 →
      x ∈ symmetric1Stage1 ∨
        x ∈ symmetric1Step1Added0 ∨
        x ∈ symmetric1Step1Added1 ∨
        x ∈ symmetric1Step1Added2 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_1_added_0_preimage_certificate :
    ∀ x : S5, x ∈ symmetric1Step1Added0 →
      (fiveCycle)⁻¹ * x ∈ symmetric1Stage1 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_1_added_1_preimage_certificate :
    ∀ x : S5, x ∈ symmetric1Step1Added1 →
      (fiveCycle⁻¹)⁻¹ * x ∈ symmetric1Stage1 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_1_added_2_preimage_certificate :
    ∀ x : S5, x ∈ symmetric1Step1Added2 →
      (representative 7)⁻¹ * x ∈ symmetric1Stage1 := by
  decide


/-- Structural assembly of one S5 breadth step; the kernel computations above
check only membership implications and explicit inverse witnesses. -/
theorem symmetric1_step_1_certificate :
    generationStep (representative 7) symmetric1Stage1 =
      symmetric1Stage2 := by
  apply Finset.Subset.antisymm
  · intro x hx
    simp only [generationStep, Finset.mem_union] at hx
    rcases hx with ((((hsource | hrotation) | hrotationInv) | hgenerator) | hgeneratorInv)
    · exact symmetric1_step_1_source_subset_certificate x hsource
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotation
      exact symmetric1_step_1_rotation_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotationInv
      exact symmetric1_step_1_rotationInv_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgenerator
      exact symmetric1_step_1_generator_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgeneratorInv
      exact symmetric1_step_1_generatorInv_closed_certificate y hy
  · intro x hx
    have hcases := symmetric1_step_1_lower_cases_certificate x hx
    rcases hcases with hsource | hadded0 | hadded1 | hadded2
    · simp [generationStep, hsource]
    · have hpre := symmetric1_step_1_added_0_preimage_certificate x hadded0
      have himage :
          x ∈ symmetric1Stage1.image (fun y ↦ fiveCycle * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (Or.inr himage)))
    · have hpre := symmetric1_step_1_added_1_preimage_certificate x hadded1
      have himage :
          x ∈ symmetric1Stage1.image (fun y ↦ fiveCycle⁻¹ * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle⁻¹)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inr himage))
    · have hpre := symmetric1_step_1_added_2_preimage_certificate x hadded2
      have himage :
          x ∈ symmetric1Stage1.image (fun y ↦ representative 7 * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(representative 7)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inr himage)

def symmetric1Step2Added0Codes : Finset ℕ :=
  [1102, 2542, 2558].toFinset

def symmetric1Step2Added0 : Finset S5 :=
  elementsWithCodes symmetric1Step2Added0Codes

def symmetric1Step2Added1Codes : Finset ℕ :=
  [198, 1646, 2690].toFinset

def symmetric1Step2Added1 : Finset S5 :=
  elementsWithCodes symmetric1Step2Added1Codes

def symmetric1Step2Added2Codes : Finset ℕ :=
  [694, 1202, 2146, 2638].toFinset

def symmetric1Step2Added2 : Finset S5 :=
  elementsWithCodes symmetric1Step2Added2Codes

set_option maxRecDepth 100000 in
theorem symmetric1_step_2_source_subset_certificate :
    ∀ x : S5, x ∈ symmetric1Stage2 → x ∈ symmetric1Stage3 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_2_rotation_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Stage2 →
      fiveCycle * x ∈ symmetric1Stage3 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_2_rotationInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Stage2 →
      fiveCycle⁻¹ * x ∈ symmetric1Stage3 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_2_generator_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Stage2 →
      representative 7 * x ∈ symmetric1Stage3 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_2_generatorInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Stage2 →
      (representative 7)⁻¹ * x ∈ symmetric1Stage3 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_2_lower_cases_certificate :
    ∀ x : S5, x ∈ symmetric1Stage3 →
      x ∈ symmetric1Stage2 ∨
        x ∈ symmetric1Step2Added0 ∨
        x ∈ symmetric1Step2Added1 ∨
        x ∈ symmetric1Step2Added2 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_2_added_0_preimage_certificate :
    ∀ x : S5, x ∈ symmetric1Step2Added0 →
      (fiveCycle)⁻¹ * x ∈ symmetric1Stage2 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_2_added_1_preimage_certificate :
    ∀ x : S5, x ∈ symmetric1Step2Added1 →
      (fiveCycle⁻¹)⁻¹ * x ∈ symmetric1Stage2 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_2_added_2_preimage_certificate :
    ∀ x : S5, x ∈ symmetric1Step2Added2 →
      (representative 7)⁻¹ * x ∈ symmetric1Stage2 := by
  decide


/-- Structural assembly of one S5 breadth step; the kernel computations above
check only membership implications and explicit inverse witnesses. -/
theorem symmetric1_step_2_certificate :
    generationStep (representative 7) symmetric1Stage2 =
      symmetric1Stage3 := by
  apply Finset.Subset.antisymm
  · intro x hx
    simp only [generationStep, Finset.mem_union] at hx
    rcases hx with ((((hsource | hrotation) | hrotationInv) | hgenerator) | hgeneratorInv)
    · exact symmetric1_step_2_source_subset_certificate x hsource
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotation
      exact symmetric1_step_2_rotation_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotationInv
      exact symmetric1_step_2_rotationInv_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgenerator
      exact symmetric1_step_2_generator_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgeneratorInv
      exact symmetric1_step_2_generatorInv_closed_certificate y hy
  · intro x hx
    have hcases := symmetric1_step_2_lower_cases_certificate x hx
    rcases hcases with hsource | hadded0 | hadded1 | hadded2
    · simp [generationStep, hsource]
    · have hpre := symmetric1_step_2_added_0_preimage_certificate x hadded0
      have himage :
          x ∈ symmetric1Stage2.image (fun y ↦ fiveCycle * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (Or.inr himage)))
    · have hpre := symmetric1_step_2_added_1_preimage_certificate x hadded1
      have himage :
          x ∈ symmetric1Stage2.image (fun y ↦ fiveCycle⁻¹ * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle⁻¹)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inr himage))
    · have hpre := symmetric1_step_2_added_2_preimage_certificate x hadded2
      have himage :
          x ∈ symmetric1Stage2.image (fun y ↦ representative 7 * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(representative 7)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inr himage)

def symmetric1Step3Added0Codes : Finset ℕ :=
  [214, 294, 1358, 1470, 1758, 2902].toFinset

def symmetric1Step3Added0 : Finset S5 :=
  elementsWithCodes symmetric1Step3Added0Codes

def symmetric1Step3Added1Codes : Finset ℕ :=
  [446, 538, 990, 1490, 1914, 1982].toFinset

def symmetric1Step3Added1 : Finset S5 :=
  elementsWithCodes symmetric1Step3Added1Codes

def symmetric1Step3Added2Codes : Finset ℕ :=
  [238, 1054, 1294, 2886].toFinset

def symmetric1Step3Added2 : Finset S5 :=
  elementsWithCodes symmetric1Step3Added2Codes

set_option maxRecDepth 100000 in
theorem symmetric1_step_3_source_subset_certificate :
    ∀ x : S5, x ∈ symmetric1Stage3 → x ∈ symmetric1Stage4 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_3_rotation_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Stage3 →
      fiveCycle * x ∈ symmetric1Stage4 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_3_rotationInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Stage3 →
      fiveCycle⁻¹ * x ∈ symmetric1Stage4 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_3_generator_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Stage3 →
      representative 7 * x ∈ symmetric1Stage4 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_3_generatorInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Stage3 →
      (representative 7)⁻¹ * x ∈ symmetric1Stage4 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_3_lower_cases_certificate :
    ∀ x : S5, x ∈ symmetric1Stage4 →
      x ∈ symmetric1Stage3 ∨
        x ∈ symmetric1Step3Added0 ∨
        x ∈ symmetric1Step3Added1 ∨
        x ∈ symmetric1Step3Added2 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_3_added_0_preimage_certificate :
    ∀ x : S5, x ∈ symmetric1Step3Added0 →
      (fiveCycle)⁻¹ * x ∈ symmetric1Stage3 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_3_added_1_preimage_certificate :
    ∀ x : S5, x ∈ symmetric1Step3Added1 →
      (fiveCycle⁻¹)⁻¹ * x ∈ symmetric1Stage3 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_3_added_2_preimage_certificate :
    ∀ x : S5, x ∈ symmetric1Step3Added2 →
      (representative 7)⁻¹ * x ∈ symmetric1Stage3 := by
  decide


/-- Structural assembly of one S5 breadth step; the kernel computations above
check only membership implications and explicit inverse witnesses. -/
theorem symmetric1_step_3_certificate :
    generationStep (representative 7) symmetric1Stage3 =
      symmetric1Stage4 := by
  apply Finset.Subset.antisymm
  · intro x hx
    simp only [generationStep, Finset.mem_union] at hx
    rcases hx with ((((hsource | hrotation) | hrotationInv) | hgenerator) | hgeneratorInv)
    · exact symmetric1_step_3_source_subset_certificate x hsource
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotation
      exact symmetric1_step_3_rotation_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotationInv
      exact symmetric1_step_3_rotationInv_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgenerator
      exact symmetric1_step_3_generator_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgeneratorInv
      exact symmetric1_step_3_generatorInv_closed_certificate y hy
  · intro x hx
    have hcases := symmetric1_step_3_lower_cases_certificate x hx
    rcases hcases with hsource | hadded0 | hadded1 | hadded2
    · simp [generationStep, hsource]
    · have hpre := symmetric1_step_3_added_0_preimage_certificate x hadded0
      have himage :
          x ∈ symmetric1Stage3.image (fun y ↦ fiveCycle * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (Or.inr himage)))
    · have hpre := symmetric1_step_3_added_1_preimage_certificate x hadded1
      have himage :
          x ∈ symmetric1Stage3.image (fun y ↦ fiveCycle⁻¹ * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle⁻¹)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inr himage))
    · have hpre := symmetric1_step_3_added_2_preimage_certificate x hadded2
      have himage :
          x ∈ symmetric1Stage3.image (fun y ↦ representative 7 * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(representative 7)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inr himage)

def symmetric1Step4Added0Codes : Finset ℕ :=
  [542, 558, 894, 1070, 1830, 2014, 2070, 2226].toFinset

def symmetric1Step4Added0 : Finset S5 :=
  elementsWithCodes symmetric1Step4Added0Codes

def symmetric1Step4Added1Codes : Finset ℕ :=
  [298, 714, 1138, 1826, 2230, 2582, 2790, 2882].toFinset

def symmetric1Step4Added1 : Finset S5 :=
  elementsWithCodes symmetric1Step4Added1Codes

def symmetric1Step4Added2Codes : Finset ℕ :=
  [222, 486, 1190, 1654, 1922, 1934, 2710, 2758].toFinset

def symmetric1Step4Added2 : Finset S5 :=
  elementsWithCodes symmetric1Step4Added2Codes

set_option maxRecDepth 100000 in
theorem symmetric1_step_4_source_subset_certificate :
    ∀ x : S5, x ∈ symmetric1Stage4 → x ∈ symmetric1Checkpoint := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_4_rotation_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Stage4 →
      fiveCycle * x ∈ symmetric1Checkpoint := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_4_rotationInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Stage4 →
      fiveCycle⁻¹ * x ∈ symmetric1Checkpoint := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_4_generator_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Stage4 →
      representative 7 * x ∈ symmetric1Checkpoint := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_4_generatorInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Stage4 →
      (representative 7)⁻¹ * x ∈ symmetric1Checkpoint := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_4_lower_cases_certificate :
    ∀ x : S5, x ∈ symmetric1Checkpoint →
      x ∈ symmetric1Stage4 ∨
        x ∈ symmetric1Step4Added0 ∨
        x ∈ symmetric1Step4Added1 ∨
        x ∈ symmetric1Step4Added2 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_4_added_0_preimage_certificate :
    ∀ x : S5, x ∈ symmetric1Step4Added0 →
      (fiveCycle)⁻¹ * x ∈ symmetric1Stage4 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_4_added_1_preimage_certificate :
    ∀ x : S5, x ∈ symmetric1Step4Added1 →
      (fiveCycle⁻¹)⁻¹ * x ∈ symmetric1Stage4 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_4_added_2_preimage_certificate :
    ∀ x : S5, x ∈ symmetric1Step4Added2 →
      (representative 7)⁻¹ * x ∈ symmetric1Stage4 := by
  decide


/-- Structural assembly of one S5 breadth step; the kernel computations above
check only membership implications and explicit inverse witnesses. -/
theorem symmetric1_step_4_certificate :
    generationStep (representative 7) symmetric1Stage4 =
      symmetric1Checkpoint := by
  apply Finset.Subset.antisymm
  · intro x hx
    simp only [generationStep, Finset.mem_union] at hx
    rcases hx with ((((hsource | hrotation) | hrotationInv) | hgenerator) | hgeneratorInv)
    · exact symmetric1_step_4_source_subset_certificate x hsource
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotation
      exact symmetric1_step_4_rotation_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotationInv
      exact symmetric1_step_4_rotationInv_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgenerator
      exact symmetric1_step_4_generator_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgeneratorInv
      exact symmetric1_step_4_generatorInv_closed_certificate y hy
  · intro x hx
    have hcases := symmetric1_step_4_lower_cases_certificate x hx
    rcases hcases with hsource | hadded0 | hadded1 | hadded2
    · simp [generationStep, hsource]
    · have hpre := symmetric1_step_4_added_0_preimage_certificate x hadded0
      have himage :
          x ∈ symmetric1Stage4.image (fun y ↦ fiveCycle * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (Or.inr himage)))
    · have hpre := symmetric1_step_4_added_1_preimage_certificate x hadded1
      have himage :
          x ∈ symmetric1Stage4.image (fun y ↦ fiveCycle⁻¹ * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle⁻¹)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inr himage))
    · have hpre := symmetric1_step_4_added_2_preimage_certificate x hadded2
      have himage :
          x ∈ symmetric1Stage4.image (fun y ↦ representative 7 * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(representative 7)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inr himage)


theorem symmetric1_checkpoint_certificate :
    generatedStage (representative 7) 5 =
      symmetric1Checkpoint := by
  change generationStep (representative 7) (generationStep (representative 7) (generationStep (representative 7) (generationStep (representative 7) (generationStep (representative 7) (symmetric1Stage0))))) = symmetric1Checkpoint
  rw [symmetric1_step_0_certificate, symmetric1_step_1_certificate, symmetric1_step_2_certificate, symmetric1_step_3_certificate, symmetric1_step_4_certificate]


def symmetric1Step5Added0Codes : Finset ℕ :=
  [366, 414, 698, 978, 1142, 1346, 1670, 1986, 2430, 2678,
   2826].toFinset

def symmetric1Step5Added0 : Finset S5 :=
  elementsWithCodes symmetric1Step5Added0Codes

def symmetric1Step5Added1Codes : Finset ℕ :=
  [482, 898, 1454, 1766, 1778, 2102, 2426, 2566, 2642, 2830].toFinset

def symmetric1Step5Added1 : Finset S5 :=
  elementsWithCodes symmetric1Step5Added1Codes

def symmetric1Step5Added2Codes : Finset ℕ :=
  [358, 722, 1110, 1334, 1634, 1790, 2022, 2110].toFinset

def symmetric1Step5Added2 : Finset S5 :=
  elementsWithCodes symmetric1Step5Added2Codes

set_option maxRecDepth 100000 in
theorem symmetric1_step_5_source_subset_certificate :
    ∀ x : S5, x ∈ symmetric1Checkpoint → x ∈ symmetric1Stage6 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_5_rotation_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Checkpoint →
      fiveCycle * x ∈ symmetric1Stage6 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_5_rotationInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Checkpoint →
      fiveCycle⁻¹ * x ∈ symmetric1Stage6 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_5_generator_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Checkpoint →
      representative 7 * x ∈ symmetric1Stage6 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_5_generatorInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Checkpoint →
      (representative 7)⁻¹ * x ∈ symmetric1Stage6 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_5_lower_cases_certificate :
    ∀ x : S5, x ∈ symmetric1Stage6 →
      x ∈ symmetric1Checkpoint ∨
        x ∈ symmetric1Step5Added0 ∨
        x ∈ symmetric1Step5Added1 ∨
        x ∈ symmetric1Step5Added2 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_5_added_0_preimage_certificate :
    ∀ x : S5, x ∈ symmetric1Step5Added0 →
      (fiveCycle)⁻¹ * x ∈ symmetric1Checkpoint := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_5_added_1_preimage_certificate :
    ∀ x : S5, x ∈ symmetric1Step5Added1 →
      (fiveCycle⁻¹)⁻¹ * x ∈ symmetric1Checkpoint := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_5_added_2_preimage_certificate :
    ∀ x : S5, x ∈ symmetric1Step5Added2 →
      (representative 7)⁻¹ * x ∈ symmetric1Checkpoint := by
  decide


/-- Structural assembly of one S5 breadth step; the kernel computations above
check only membership implications and explicit inverse witnesses. -/
theorem symmetric1_step_5_certificate :
    generationStep (representative 7) symmetric1Checkpoint =
      symmetric1Stage6 := by
  apply Finset.Subset.antisymm
  · intro x hx
    simp only [generationStep, Finset.mem_union] at hx
    rcases hx with ((((hsource | hrotation) | hrotationInv) | hgenerator) | hgeneratorInv)
    · exact symmetric1_step_5_source_subset_certificate x hsource
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotation
      exact symmetric1_step_5_rotation_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotationInv
      exact symmetric1_step_5_rotationInv_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgenerator
      exact symmetric1_step_5_generator_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgeneratorInv
      exact symmetric1_step_5_generatorInv_closed_certificate y hy
  · intro x hx
    have hcases := symmetric1_step_5_lower_cases_certificate x hx
    rcases hcases with hsource | hadded0 | hadded1 | hadded2
    · simp [generationStep, hsource]
    · have hpre := symmetric1_step_5_added_0_preimage_certificate x hadded0
      have himage :
          x ∈ symmetric1Checkpoint.image (fun y ↦ fiveCycle * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (Or.inr himage)))
    · have hpre := symmetric1_step_5_added_1_preimage_certificate x hadded1
      have himage :
          x ∈ symmetric1Checkpoint.image (fun y ↦ fiveCycle⁻¹ * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle⁻¹)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inr himage))
    · have hpre := symmetric1_step_5_added_2_preimage_certificate x hadded2
      have himage :
          x ∈ symmetric1Checkpoint.image (fun y ↦ representative 7 * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(representative 7)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inr himage)

def symmetric1Step6Added0Codes : Finset ℕ :=
  [334, 1014, 1022, 1298, 1478, 1946, 2410, 2586, 2766, 2778].toFinset

def symmetric1Step6Added0 : Finset S5 :=
  elementsWithCodes symmetric1Step6Added0Codes

def symmetric1Step6Added1Codes : Finset ℕ :=
  [242, 566, 1178, 1366, 2054, 2702].toFinset

def symmetric1Step6Added1 : Finset S5 :=
  elementsWithCodes symmetric1Step6Added1Codes

def symmetric1Step6Added2Codes : Finset ℕ :=
  [422, 434, 738, 1394, 2910].toFinset

def symmetric1Step6Added2 : Finset S5 :=
  elementsWithCodes symmetric1Step6Added2Codes

set_option maxRecDepth 100000 in
theorem symmetric1_step_6_source_subset_certificate :
    ∀ x : S5, x ∈ symmetric1Stage6 → x ∈ symmetric1Stage7 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_6_rotation_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Stage6 →
      fiveCycle * x ∈ symmetric1Stage7 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_6_rotationInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Stage6 →
      fiveCycle⁻¹ * x ∈ symmetric1Stage7 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_6_generator_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Stage6 →
      representative 7 * x ∈ symmetric1Stage7 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_6_generatorInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Stage6 →
      (representative 7)⁻¹ * x ∈ symmetric1Stage7 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_6_lower_cases_certificate :
    ∀ x : S5, x ∈ symmetric1Stage7 →
      x ∈ symmetric1Stage6 ∨
        x ∈ symmetric1Step6Added0 ∨
        x ∈ symmetric1Step6Added1 ∨
        x ∈ symmetric1Step6Added2 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_6_added_0_preimage_certificate :
    ∀ x : S5, x ∈ symmetric1Step6Added0 →
      (fiveCycle)⁻¹ * x ∈ symmetric1Stage6 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_6_added_1_preimage_certificate :
    ∀ x : S5, x ∈ symmetric1Step6Added1 →
      (fiveCycle⁻¹)⁻¹ * x ∈ symmetric1Stage6 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_6_added_2_preimage_certificate :
    ∀ x : S5, x ∈ symmetric1Step6Added2 →
      (representative 7)⁻¹ * x ∈ symmetric1Stage6 := by
  decide


/-- Structural assembly of one S5 breadth step; the kernel computations above
check only membership implications and explicit inverse witnesses. -/
theorem symmetric1_step_6_certificate :
    generationStep (representative 7) symmetric1Stage6 =
      symmetric1Stage7 := by
  apply Finset.Subset.antisymm
  · intro x hx
    simp only [generationStep, Finset.mem_union] at hx
    rcases hx with ((((hsource | hrotation) | hrotationInv) | hgenerator) | hgeneratorInv)
    · exact symmetric1_step_6_source_subset_certificate x hsource
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotation
      exact symmetric1_step_6_rotation_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotationInv
      exact symmetric1_step_6_rotationInv_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgenerator
      exact symmetric1_step_6_generator_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgeneratorInv
      exact symmetric1_step_6_generatorInv_closed_certificate y hy
  · intro x hx
    have hcases := symmetric1_step_6_lower_cases_certificate x hx
    rcases hcases with hsource | hadded0 | hadded1 | hadded2
    · simp [generationStep, hsource]
    · have hpre := symmetric1_step_6_added_0_preimage_certificate x hadded0
      have himage :
          x ∈ symmetric1Stage6.image (fun y ↦ fiveCycle * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (Or.inr himage)))
    · have hpre := symmetric1_step_6_added_1_preimage_certificate x hadded1
      have himage :
          x ∈ symmetric1Stage6.image (fun y ↦ fiveCycle⁻¹ * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle⁻¹)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inr himage))
    · have hpre := symmetric1_step_6_added_2_preimage_certificate x hadded2
      have himage :
          x ∈ symmetric1Stage6.image (fun y ↦ representative 7 * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(representative 7)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inr himage)

def symmetric1Step7Added0Codes : Finset ℕ :=
  [1210, 2134, 2170].toFinset

def symmetric1Step7Added0 : Finset S5 :=
  elementsWithCodes symmetric1Step7Added0Codes

def symmetric1Step7Added1Codes : Finset ℕ :=
  [582].toFinset

def symmetric1Step7Added1 : Finset S5 :=
  elementsWithCodes symmetric1Step7Added1Codes

def symmetric1Step7Added2Codes : Finset ℕ :=
  [194, 2538].toFinset

def symmetric1Step7Added2 : Finset S5 :=
  elementsWithCodes symmetric1Step7Added2Codes

set_option maxRecDepth 100000 in
theorem symmetric1_step_7_source_subset_certificate :
    ∀ x : S5, x ∈ symmetric1Stage7 → x ∈ symmetric1Stage8 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_7_rotation_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Stage7 →
      fiveCycle * x ∈ symmetric1Stage8 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_7_rotationInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Stage7 →
      fiveCycle⁻¹ * x ∈ symmetric1Stage8 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_7_generator_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Stage7 →
      representative 7 * x ∈ symmetric1Stage8 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_7_generatorInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Stage7 →
      (representative 7)⁻¹ * x ∈ symmetric1Stage8 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_7_lower_cases_certificate :
    ∀ x : S5, x ∈ symmetric1Stage8 →
      x ∈ symmetric1Stage7 ∨
        x ∈ symmetric1Step7Added0 ∨
        x ∈ symmetric1Step7Added1 ∨
        x ∈ symmetric1Step7Added2 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_7_added_0_preimage_certificate :
    ∀ x : S5, x ∈ symmetric1Step7Added0 →
      (fiveCycle)⁻¹ * x ∈ symmetric1Stage7 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_7_added_1_preimage_certificate :
    ∀ x : S5, x ∈ symmetric1Step7Added1 →
      (fiveCycle⁻¹)⁻¹ * x ∈ symmetric1Stage7 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_7_added_2_preimage_certificate :
    ∀ x : S5, x ∈ symmetric1Step7Added2 →
      (representative 7)⁻¹ * x ∈ symmetric1Stage7 := by
  decide


/-- Structural assembly of one S5 breadth step; the kernel computations above
check only membership implications and explicit inverse witnesses. -/
theorem symmetric1_step_7_certificate :
    generationStep (representative 7) symmetric1Stage7 =
      symmetric1Stage8 := by
  apply Finset.Subset.antisymm
  · intro x hx
    simp only [generationStep, Finset.mem_union] at hx
    rcases hx with ((((hsource | hrotation) | hrotationInv) | hgenerator) | hgeneratorInv)
    · exact symmetric1_step_7_source_subset_certificate x hsource
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotation
      exact symmetric1_step_7_rotation_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotationInv
      exact symmetric1_step_7_rotationInv_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgenerator
      exact symmetric1_step_7_generator_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgeneratorInv
      exact symmetric1_step_7_generatorInv_closed_certificate y hy
  · intro x hx
    have hcases := symmetric1_step_7_lower_cases_certificate x hx
    rcases hcases with hsource | hadded0 | hadded1 | hadded2
    · simp [generationStep, hsource]
    · have hpre := symmetric1_step_7_added_0_preimage_certificate x hadded0
      have himage :
          x ∈ symmetric1Stage7.image (fun y ↦ fiveCycle * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (Or.inr himage)))
    · have hpre := symmetric1_step_7_added_1_preimage_certificate x hadded1
      have himage :
          x ∈ symmetric1Stage7.image (fun y ↦ fiveCycle⁻¹ * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle⁻¹)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inr himage))
    · have hpre := symmetric1_step_7_added_2_preimage_certificate x hadded2
      have himage :
          x ∈ symmetric1Stage7.image (fun y ↦ representative 7 * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(representative 7)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inr himage)

def symmetric1Step8Added0Codes : Finset ℕ :=
  [970, 2926].toFinset

def symmetric1Step8Added0 : Finset S5 :=
  elementsWithCodes symmetric1Step8Added0Codes

def symmetric1Step8Added1Codes : Finset ℕ :=
  [2382].toFinset

def symmetric1Step8Added1 : Finset S5 :=
  elementsWithCodes symmetric1Step8Added1Codes

set_option maxRecDepth 100000 in
theorem symmetric1_step_8_source_subset_certificate :
    ∀ x : S5, x ∈ symmetric1Stage8 → x ∈ symmetric1Stage9 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_8_rotation_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Stage8 →
      fiveCycle * x ∈ symmetric1Stage9 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_8_rotationInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Stage8 →
      fiveCycle⁻¹ * x ∈ symmetric1Stage9 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_8_generator_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Stage8 →
      representative 7 * x ∈ symmetric1Stage9 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_8_generatorInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Stage8 →
      (representative 7)⁻¹ * x ∈ symmetric1Stage9 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_8_lower_cases_certificate :
    ∀ x : S5, x ∈ symmetric1Stage9 →
      x ∈ symmetric1Stage8 ∨
        x ∈ symmetric1Step8Added0 ∨
        x ∈ symmetric1Step8Added1 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_8_added_0_preimage_certificate :
    ∀ x : S5, x ∈ symmetric1Step8Added0 →
      (fiveCycle)⁻¹ * x ∈ symmetric1Stage8 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_8_added_1_preimage_certificate :
    ∀ x : S5, x ∈ symmetric1Step8Added1 →
      (fiveCycle⁻¹)⁻¹ * x ∈ symmetric1Stage8 := by
  decide


/-- Structural assembly of one S5 breadth step; the kernel computations above
check only membership implications and explicit inverse witnesses. -/
theorem symmetric1_step_8_certificate :
    generationStep (representative 7) symmetric1Stage8 =
      symmetric1Stage9 := by
  apply Finset.Subset.antisymm
  · intro x hx
    simp only [generationStep, Finset.mem_union] at hx
    rcases hx with ((((hsource | hrotation) | hrotationInv) | hgenerator) | hgeneratorInv)
    · exact symmetric1_step_8_source_subset_certificate x hsource
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotation
      exact symmetric1_step_8_rotation_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotationInv
      exact symmetric1_step_8_rotationInv_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgenerator
      exact symmetric1_step_8_generator_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgeneratorInv
      exact symmetric1_step_8_generatorInv_closed_certificate y hy
  · intro x hx
    have hcases := symmetric1_step_8_lower_cases_certificate x hx
    rcases hcases with hsource | hadded0 | hadded1
    · simp [generationStep, hsource]
    · have hpre := symmetric1_step_8_added_0_preimage_certificate x hadded0
      have himage :
          x ∈ symmetric1Stage8.image (fun y ↦ fiveCycle * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (Or.inr himage)))
    · have hpre := symmetric1_step_8_added_1_preimage_certificate x hadded1
      have himage :
          x ∈ symmetric1Stage8.image (fun y ↦ fiveCycle⁻¹ * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle⁻¹)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inr himage))

def symmetric1Step9Added0Codes : Finset ℕ :=
  [1726].toFinset

def symmetric1Step9Added0 : Finset S5 :=
  elementsWithCodes symmetric1Step9Added0Codes

set_option maxRecDepth 100000 in
theorem symmetric1_step_9_source_subset_certificate :
    ∀ x : S5, x ∈ symmetric1Stage9 → x ∈ classElements (representativeClass 7) := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_9_rotation_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Stage9 →
      fiveCycle * x ∈ classElements (representativeClass 7) := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_9_rotationInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Stage9 →
      fiveCycle⁻¹ * x ∈ classElements (representativeClass 7) := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_9_generator_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Stage9 →
      representative 7 * x ∈ classElements (representativeClass 7) := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_9_generatorInv_closed_certificate :
    ∀ x : S5, x ∈ symmetric1Stage9 →
      (representative 7)⁻¹ * x ∈ classElements (representativeClass 7) := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_9_lower_cases_certificate :
    ∀ x : S5, x ∈ classElements (representativeClass 7) →
      x ∈ symmetric1Stage9 ∨
        x ∈ symmetric1Step9Added0 := by
  decide

set_option maxRecDepth 100000 in
theorem symmetric1_step_9_added_0_preimage_certificate :
    ∀ x : S5, x ∈ symmetric1Step9Added0 →
      (fiveCycle)⁻¹ * x ∈ symmetric1Stage9 := by
  decide


/-- Structural assembly of one S5 breadth step; the kernel computations above
check only membership implications and explicit inverse witnesses. -/
theorem symmetric1_step_9_certificate :
    generationStep (representative 7) symmetric1Stage9 =
      classElements (representativeClass 7) := by
  apply Finset.Subset.antisymm
  · intro x hx
    simp only [generationStep, Finset.mem_union] at hx
    rcases hx with ((((hsource | hrotation) | hrotationInv) | hgenerator) | hgeneratorInv)
    · exact symmetric1_step_9_source_subset_certificate x hsource
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotation
      exact symmetric1_step_9_rotation_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hrotationInv
      exact symmetric1_step_9_rotationInv_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgenerator
      exact symmetric1_step_9_generator_closed_certificate y hy
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hgeneratorInv
      exact symmetric1_step_9_generatorInv_closed_certificate y hy
  · intro x hx
    have hcases := symmetric1_step_9_lower_cases_certificate x hx
    rcases hcases with hsource | hadded0
    · simp [generationStep, hsource]
    · have hpre := symmetric1_step_9_added_0_preimage_certificate x hadded0
      have himage :
          x ∈ symmetric1Stage9.image (fun y ↦ fiveCycle * y) := by
        apply Finset.mem_image.mpr
        exact ⟨(fiveCycle)⁻¹ * x, hpre, by simp [mul_assoc]⟩
      simp only [generationStep, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (Or.inr himage)))


theorem symmetric1_finish_certificate :
    iterateGenerationStep (representative 7)
      symmetric1Checkpoint 5 =
        classElements (representativeClass 7) := by
  change generationStep (representative 7) (generationStep (representative 7) (generationStep (representative 7) (generationStep (representative 7) (generationStep (representative 7) (symmetric1Checkpoint))))) = classElements (representativeClass 7)
  rw [symmetric1_step_5_certificate, symmetric1_step_6_certificate, symmetric1_step_7_certificate, symmetric1_step_8_certificate, symmetric1_step_9_certificate]

theorem symmetric1_generation_certificate :
    generatedStage (representative 7) (representativeDepth 7) =
      classElements (representativeClass 7) := by
  change generatedStage (representative 7) 10 =
    classElements (representativeClass 7)
  calc
    generatedStage (representative 7) 10 =
        iterateGenerationStep (representative 7)
          (generatedStage (representative 7) 5)
          5 := by
      simpa using generatedStage_add (representative 7)
        5 5
    _ = iterateGenerationStep (representative 7)
          symmetric1Checkpoint 5 := by
      rw [symmetric1_checkpoint_certificate]
    _ = classElements (representativeClass 7) :=
      symmetric1_finish_certificate

end LeanProofs.PolynomialFormulas.Fin5TransitiveClassificationCertificates
