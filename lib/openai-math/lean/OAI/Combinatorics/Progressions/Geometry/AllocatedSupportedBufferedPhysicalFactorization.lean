/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Dynamics.AllocatedFullSiteRadiusBudget
import OAI.Combinatorics.Progressions.Estimates.AllocatedBufferedPhysicalFactorization
import OAI.Combinatorics.Progressions.Estimates.AllocatedCoveredSiteBuffer

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (α : Type*) [Fintype α]

noncomputable def allocatedBufferedPhysicalChartRadius (C : Fin m → ℝ) (j : Fin m) : ℝ :=
  min (allocatedPhysicalChartRadius (G := G) B α C (allocatedSiteRootAllowance α m) j)
    (1 / (8 * (C j + 1) * ((Fintype.card (I j) : ℝ) + 1) * (allocatedFullSiteRadius (G := G) B α : ℝ)))

theorem allocatedBufferedPhysicalChartRadius_pos (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (j : Fin m) :
    0 < allocatedBufferedPhysicalChartRadius (G := G) B α C j := by
  have hCj := hC j
  have hr : (0 : ℝ) < allocatedFullSiteRadius (G := G) B α := allocatedFullSiteRadius_pos B α
  exact lt_min (allocatedPhysicalChartRadius_pos B α C hC
    (allocatedSiteRootAllowance_one_le α m) j) (by positivity)

theorem allocatedBufferedPhysicalChartRadius_le_supported (C : Fin m → ℝ) (j : Fin m) :
    allocatedBufferedPhysicalChartRadius (G := G) B α C j ≤
      allocatedPhysicalChartRadius (G := G) B α C (allocatedSiteRootAllowance α m) j := min_le_left _ _

theorem allocatedBufferedPhysicalChartRadius_le_original (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (j : Fin m) :
    allocatedBufferedPhysicalChartRadius (G := G) B α C j ≤ allocatedPhysicalChartRadius (G := G) B α C 1 j :=
  (allocatedBufferedPhysicalChartRadius_le_supported B α C j).trans (allocatedSiteChartRadius_le_original B α C hC j)

theorem allocatedBufferedPhysicalChartRadius_budget (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    {R : Fin m → ℝ} (hR : ∀ j, 0 ≤ R j)
    (hsmall : ∀ j, R j ≤ allocatedBufferedPhysicalChartRadius (G := G) B α C j) (j : Fin m) :
    C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (allocatedFullSiteRadius (G := G) B α : ℝ) * R j)) ≤ 1 / 4 := by
  have hCj := hC j
  have hr : (0 : ℝ) < allocatedFullSiteRadius (G := G) B α := allocatedFullSiteRadius_pos B α
  have hD : 0 < 8 * (C j + 1) * ((Fintype.card (I j) : ℝ) + 1) * (allocatedFullSiteRadius (G := G) B α : ℝ) := by positivity
  have hs : R j ≤ 1 / (8 * (C j + 1) * ((Fintype.card (I j) : ℝ) + 1) * (allocatedFullSiteRadius (G := G) B α : ℝ)) :=
    (hsmall j).trans (min_le_right _ _)
  have hDR := (le_div_iff₀ hD).mp hs
  calc
    _ ≤ (C j + 1) * (((Fintype.card (I j) : ℝ) + 1) * (2 * (allocatedFullSiteRadius (G := G) B α : ℝ) * R j)) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
        (mul_nonneg (by positivity) (mul_nonneg (by positivity) (hR j)))
    _ = (R j * (8 * (C j + 1) * ((Fintype.card (I j) : ℝ) + 1) * (allocatedFullSiteRadius (G := G) B α : ℝ))) / 4 := by ring
    _ ≤ 1 / 4 := div_le_div_of_nonneg_right hDR (by norm_num)

theorem allocatedBufferedPhysicalChartRadius_inv_le_exp
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) {P : ℝ} (hP : 0 ≤ P)
    (hm : (m : ℝ) ≤ Real.exp P) (hq : (Fintype.card α : ℝ) ≤ P)
    (hallow : ((2 * m : ℕ) + 5) * (Fintype.card α : ℝ) + 5 ≤ P)
    (hCP : ∀ j, C j ≤ Real.exp P)
    (hNP : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp P)
    (hIP : ∀ j, (Fintype.card (I j) : ℝ) ≤ Real.exp P) (j : Fin m) :
    (allocatedBufferedPhysicalChartRadius (G := G) B α C j)⁻¹ ≤
      Real.exp (3 * (P + 1) + Fintype.card α + 2 +
        (j.val + 1 : ℕ) * (P + Fintype.card α + 1) + (6 * P + 6)) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hunit : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have hadd {a : ℝ} (ha : a ≤ Real.exp P) : a + 1 ≤ Real.exp (P + 1) := by
    calc
      _ ≤ 2 * Real.exp P := by linarith
      _ ≤ Real.exp 1 * Real.exp P := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have h8 : (8 : ℝ) ≤ Real.exp 3 := by
    calc
      _ = (2 : ℝ) ^ 3 := by norm_num
      _ ≤ (Real.exp 1) ^ 3 := pow_le_pow_left₀ (by norm_num) htwo 3
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hr := allocatedFullSiteRadius_le_exp B α hP hm hq
    ((allocatedSiteRootAllowance_le_exp α m).trans (Real.exp_le_exp.mpr hallow)) hNP
  have hCj := hC j
  have hCp := hadd (hCP j)
  have hIp := hadd (hIP j)
  have hden : 8 * (C j + 1) * ((Fintype.card (I j) : ℝ) + 1) * (allocatedFullSiteRadius (G := G) B α : ℝ) ≤
      Real.exp (6 * P + 6) := by
    calc
      _ ≤ Real.exp 3 * Real.exp (P + 1) * Real.exp (P + 1) * Real.exp (4 * P + 1) := by gcongr
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  have hold := allocatedSiteChartRadius_inv_le_exp B α C hC hP hallow hCP hNP hIP j
  unfold allocatedBufferedPhysicalChartRadius
  by_cases h : allocatedPhysicalChartRadius (G := G) B α C (allocatedSiteRootAllowance α m) j ≤
      1 / (8 * (C j + 1) * ((Fintype.card (I j) : ℝ) + 1) * (allocatedFullSiteRadius (G := G) B α : ℝ))
  · rw [min_eq_left h]
    exact hold.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_right (by positivity)))
  · rw [min_eq_right (le_of_not_ge h), one_div, inv_inv]
    exact hden.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_left (by positivity)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))
local notation "rows" => (fun j => (Subtype.val : jets j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit jets I n grid
local notation "quarter" => (fun j (_ : jets j) => standardLatticeClosedQuarterBox (J j))
local notation "chart" => mixedCoveredJetChart (O := jets) U o b hb bW d
local notation "region" => mixedCoveredJetRegion (O := jets) (E := Q) U o b d quarter

theorem allocatedCoveredSiteTerm_supported_buffered_factorization
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j w, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ C j * ‖w‖)
    (hsmall : ∀ j, R j ≤ allocatedBufferedPhysicalChartRadius (G := G) B α C j)
    (modulus : ℕ)
    (residue : ∀ j : Fin m, Matrix (BoundedBooleanJet α (j.val + 1))
      (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (f : Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (hsupport : ∀ s w, (∃ a, 2 * idealSiteBoxRadius α m < |w a|) → f s w = 0)
    (y : EuclideanJetLayers U jets) :
    allocatedCoveredComplexProfileDensity B U b hR hσ S x u v rows hb o bW d quarter
        (allocatedSiteTermDensity B U b S x modulus residue f) y =
      (allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d quarter
        (allocatedMaskedSiteEnvelope B U b S x modulus residue) y : ℂ) *
        ∏ s, allocatedBufferedSiteChartFactor B U b S o hb bW d (allocatedFullSiteRadius (G := G) B α)
          (allocatedFullSiteRadius_pos B α) (f s) (coveredBooleanSiteValue U y s) := by
  have hsmall' (j : Fin m) : R j ≤ allocatedPhysicalChartRadius (G := G) B α C (allocatedSiteRootAllowance α m) j :=
    (hsmall j).trans (allocatedBufferedPhysicalChartRadius_le_supported B α C j)
  by_cases hy : y ∈ chart '' region
  · obtain ⟨z, hz, rfl⟩ := hy
    have hinj := mixedCoveredJetChart_injOn U o b hb bW d quarter
      (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
    rw [allocatedCoveredComplexProfileDensity, allocatedCoveredProfileDensity,
      restrictedComplexChartDensity_apply _ _ _ _ hinj hz,
      restrictedChartDensity_apply _ _ _ _ hinj hz, Complex.ofReal_one, one_mul, one_mul]
    by_cases hg : allocatedGridJetDensity B U b hR hσ S x u v rows
        (fun a => coefficientJetAxisEquiv jets I n z.1 a.val) = 0
    · simp only [allocatedCoveredFixedFactor, hg, zero_mul, zero_div, Complex.ofReal_zero]
    · by_cases hs : ∀ s a, |allocatedIdealSiteCoordinates B U b S (split z.1).2 s a| ≤ 2 * idealSiteBoxRadius α m
      · have hsites := mixedCoveredBooleanSiteValue_mem_quarter U o b d z
          (fun j => C j * (((Fintype.card (I j) : ℝ) + 1) * (allocatedSiteJetSize (G := G) B α j * R j)))
          (fun j => mul_nonneg (hC j) (mul_nonneg (by positivity)
            (mul_nonneg (allocatedSiteJetSize_nonneg B α j) (hR j).le)))
          (allocatedSiteBox_mixed_point_bound B U b hR hσ S x u v hσ1 o d z hg hs C hC hchart)
          (allocatedSiteChartRadius_budget B α C hC (fun j => (hR j).le) hsmall')
        have hbox := allocatedSiteBox_full_site_bound B U b hR hσ S x u v hσ1 z.1 hg hs
        rw [allocatedBufferedSiteChartFactor_product B U b S o hb bW d
          (allocatedFullSiteRadius (G := G) B α) (allocatedFullSiteRadius_pos B α) f z hsites hbox]
        simp only [allocatedMaskedSiteEnvelope, allocatedIdealSiteEnvelope, ite_eq_left hs,
          allocatedSiteTermDensity, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_inv]
        ring
      · obtain ⟨s, a, ha⟩ : ∃ s a, 2 * idealSiteBoxRadius α m <
            |allocatedIdealSiteCoordinates B U b S (split z.1).2 s a| := by
          simpa only [not_forall, not_le] using hs
        have hp : (∏ s, f s (allocatedIdealSiteCoordinates B U b S (split z.1).2 s)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ s) (hsupport s _ ⟨a, ha⟩)
        simp only [allocatedSiteTermDensity, hp, zero_div, mul_zero, allocatedMaskedSiteEnvelope,
          allocatedIdealSiteEnvelope, ite_eq_right hs, Complex.ofReal_zero, zero_mul]
  · rw [allocatedCoveredComplexProfileDensity, allocatedCoveredProfileDensity,
      restrictedComplexChartDensity_zero _ _ _ _ hy, restrictedChartDensity_zero _ _ _ _ hy,
      Complex.ofReal_zero, zero_mul]

theorem allocatedCoveredSiteTerm_supported_buffered_sum
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j w, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ C j * ‖w‖)
    (hsmall : ∀ j, R j ≤ allocatedBufferedPhysicalChartRadius (G := G) B α C j)
    (modulus : ℕ)
    (residue : ∀ j : Fin m, Matrix (BoundedBooleanJet α (j.val + 1))
      (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    {T : Type*} [Fintype T] (c : T → ℂ)
    (f : T → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (hsupport : ∀ i s w, (∃ a, 2 * idealSiteBoxRadius α m < |w a|) → f i s w = 0)
    (y : EuclideanJetLayers U jets) :
    (∑ i, c i * allocatedCoveredComplexProfileDensity B U b hR hσ S x u v rows hb o bW d quarter
        (allocatedSiteTermDensity B U b S x modulus residue (f i)) y) =
      (allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d quarter
        (allocatedMaskedSiteEnvelope B U b S x modulus residue) y : ℂ) *
        ∑ i, c i * ∏ s, allocatedBufferedSiteChartFactor B U b S o hb bW d
          (allocatedFullSiteRadius (G := G) B α) (allocatedFullSiteRadius_pos B α)
          (f i s) (coveredBooleanSiteValue U y s) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [allocatedCoveredSiteTerm_supported_buffered_factorization B U b hR hσ S x u v hb o bW d
    hσ1 C hC hchart hsmall modulus residue (f i) (hsupport i) y]
  ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule _root_.Set _root_.OAI.Set VectorPolynomial
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (u : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "rows" => (fun j => (Subtype.val : jets j → Finset (Fin dim)))
local notation "quarter" => (fun j (_ : jets j) => standardLatticeClosedQuarterBox (J j))

theorem allocatedCoveredSiteTerm_supported_buffered_physical_factorization
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j w, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ C j * ‖w‖)
    (hsmall : ∀ j, R j ≤ allocatedBufferedPhysicalChartRadius (G := G) B (Fin dim) C j)
    (modulus : ℕ)
    (residue : ∀ j : Fin m, Matrix (BoundedBooleanJet (Fin dim) (j.val + 1))
      (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (f : Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)
    (hsupport : ∀ s w, (∃ a, 2 * idealSiteBoxRadius (Fin dim) m < |w a|) → f s w = 0)
    {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (cube : X → (Unit ⊕ Fin dim) → ℤ) :
    allocatedCoveredComplexProfileDensity B U b hR hσ S x u v rows hb o bW d quarter
        (allocatedSiteTermDensity B U b S x modulus residue f) (physicalCubeEuclideanSample U d p hm cube) =
      (allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d quarter
        (allocatedMaskedSiteEnvelope B U b S x modulus residue) (physicalCubeEuclideanSample U d p hm cube) : ℂ) *
        ∏ s, allocatedBufferedSiteChartFactor B U b S o hb bW d (allocatedFullSiteRadius (G := G) B (Fin dim))
          (allocatedFullSiteRadius_pos B (Fin dim)) (f s)
          (physicalSingleSiteValue U d p hm (fun a => (physicalCubeVertexValue cube s a : ℝ))) := by
  have h := allocatedCoveredSiteTerm_supported_buffered_factorization B U b hR hσ S x u v hb o bW d
    hσ1 C hC hchart hsmall modulus residue f hsupport (physicalCubeEuclideanSample U d p hm cube)
  simpa only [coveredBooleanSiteValue_physical U d p hm hp cube] using h

end Erdos3.BooleanCubeKernel

end

end OAI
