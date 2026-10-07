import OAI.Combinatorics.Progressions.Lattices.RetainedPhysicalCRT

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem weighted_double_expect_sub_smul {X T : Type*} [Fintype X] [Fintype T]
    (w : X → ℝ) (f g : X → T → ℝ) (r : ℝ) :
    (𝔼 x : X, w x * (𝔼 t : T, (f x t - r * g x t))) =
      (𝔼 x, w x * (𝔼 t, f x t)) - r * (𝔼 x, w x * (𝔼 t, g x t)) := by
  simp only [Finset.expect_sub_distrib, ← Finset.mul_expect, mul_sub]
  congr 1
  rw [Finset.mul_expect]
  congr 1
  funext x
  ring

theorem retained_physical_truncation_difference_le
    {ι I J : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [Fintype J]
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i c, (P i).step c = 1) (hpos : ∀ i c, 0 < (P i).length c)
    (c : ∀ i, (P i).Label) (q : ι → ℕ) [∀ i, NeZero (q i)]
    (sourceLo : Option J × I → ℤ) (sourceN : Option J × I → ℕ)
    (sourceHne : Nonempty (IntegerResidueBox sourceLo (fun i => sourceLo i + sourceN i)
      (fun _ => 1) (fun _ => 0)))
    (paramLo : J → ℤ) (paramN : J → ℕ)
    (paramHne : Nonempty (IntegerResidueBox paramLo (fun j => paramLo j + paramN j)
      (fun _ => 1) (fun _ => 0)))
    (D : ℕ) (a : J → ℤ) (b : ℕ) (w : (Option J × I → ℤ) → ℝ) (h g : (I → ℤ) → ℝ)
    (hw : ∀ z ∈ translatedIntegerBox sourceLo sourceN, 0 ≤ w z ∧ w z ≤ 1)
    (hh : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ h x ∧ h x ≤ 1)
    (hg : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ g x ∧ g x ≤ 1)
    (hretained : ∀ z ∈ translatedIntegerBox sourceLo sourceN,
      ∀ t ∈ translatedIntegerBox paramLo paramN,
        physicalBoxClassify lo N P (smoothAffineSample (fun j => a j + (D : ℤ) * t j) z) = some c)
    {etaParam etaSite r R : ℝ} (hparam : 0 ≤ etaParam) (hsite : 0 ≤ etaSite) (hr : 0 ≤ r)
    (hcloseParam : ProductMarginalsClose (primeCoordinateReference (σ := J) q)
      (residuePrimeCoordinateDensity paramLo paramN 1 (fun _ => 0) paramHne q (fun _ => 1)) etaParam b)
    (hcloseSite : ProductMarginalsClose (primeCoordinateReference (σ := I) q)
      (residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
        (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c)
        q (fun _ => 1)) etaSite b)
    (hreference : productTruncatedPairing (affinePeriodProductCoupling (σ := I) q D a)
      (lowDegreeCoordinateSets ι b)
      (residuePrimeCoordinateDensity sourceLo sourceN 1 (fun _ => 0) sourceHne q w)
      (fun x => residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
          (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q h x -
        r * residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
          (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q g x) ≤ R) :
    (𝔼 z : IntegerResidueBox sourceLo (fun i => sourceLo i + sourceN i) (fun _ => 1) (fun _ => 0),
      w (fun i => (z i).val) *
        (𝔼 t : IntegerResidueBox paramLo (fun j => paramLo j + paramN j) (fun _ => 1) (fun _ => 0),
          (physicalBoxTruncation lo N P hpos q b h
              (smoothAffineSample (fun j => a j + (D : ℤ) * (t j).val) (fun i => (z i).val)) -
            r * physicalBoxTruncation lo N P hpos q b g
              (smoothAffineSample (fun j => a j + (D : ℤ) * (t j).val) (fun i => (z i).val))))) ≤
      R + (1 + r) * etaParam * residueTruncationCap ι b etaSite := by
  have heh := retained_physical_truncation_crt lo N P hstep hpos c q
    sourceLo sourceN sourceHne paramLo paramN paramHne D a b w h hw hh hretained
    hparam hsite hcloseParam hcloseSite
  have heg := retained_physical_truncation_crt lo N P hstep hpos c q
    sourceLo sourceN sourceHne paramLo paramN paramHne D a b w g hw hg hretained
    hparam hsite hcloseParam hcloseSite
  rw [productTruncatedPairing_sub_smul_right] at hreference
  rw [weighted_double_expect_sub_smul]
  have hhup := (abs_le.mp heh).2
  have hglow := mul_le_mul_of_nonneg_left (abs_le.mp heg).1 hr
  nlinarith

end Erdos3

end

end OAI
