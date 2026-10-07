import OAI.Combinatorics.Progressions.Estimates.ReconstructedCubeNativePartner

namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators Classical

variable {K X : Type*} [Fintype K] [Fintype X] [DecidableEq X] {dim : ℕ}
variable (root : K → ℤ) (D : Matrix (Fin dim) K ℤ) (base : X → ℤ)
variable (residue : Option K × X → ℤ) (q N : X → ℕ) (H : X → ℝ) (radius mesh : ℝ)
variable {modulus : ℕ} (t : X → SpatialSiteLabel (Fin dim) modulus radius mesh)
variable (input : (X → ℤ) → ℂ) (analytic : Finset (Fin dim) → (X → ℤ) → ℂ)
local notation "spatial" => physicalResidueSpatialSiteFactor root D base residue q radius mesh H t

theorem physicalSpatialProduct_support
    (hinput : ∀ u, u ∉ integerBox N → input u = 0)
    (u : X → (Unit ⊕ Fin dim) → ℤ)
    (hproduct : (∏ site, conjugationPower site.card (input (physicalCubeVertexValue u site)) *
      (spatial site (physicalCubeVertexValue u site) * analytic site (physicalCubeVertexValue u site))) ≠ 0) :
    (∀ site, physicalCubeVertexValue u site ∈ integerBox N) ∧
      u ∈ Set.range (physicalResidueReconstruction root D base residue q) := by
  have hsite (site : Finset (Fin dim)) := (Finset.prod_ne_zero_iff.mp hproduct) site (Finset.mem_univ site)
  constructor
  · intro site
    by_contra hnot
    apply hsite site
    simp only [hinput _ hnot, map_zero, zero_mul]
  · apply physicalResidueSpatialSiteFactor_prod_nonzero_mem_range root D base residue q radius mesh H t u
    apply Finset.prod_ne_zero_iff.mpr
    intro site _
    exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (hsite site)).2).1

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical
attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {s n : ℕ} {K : Type*} [Fintype K]
variable (root : K → ℤ) (D : Matrix (Fin (s + 1)) K ℤ) (base : Fin n → ℤ)
variable (residue : Option K × Fin n → ℤ) (stride N : Fin n → ℕ)
variable [∀ i, NeZero (N i)] (H : Fin n → ℝ) (radius mesh : ℝ)
variable {modulus : ℕ} (t : Fin n → SpatialSiteLabel (Fin (s + 1)) modulus radius mesh)
variable (f : (Fin n → ℤ) → ℂ) (analytic : Finset (Fin (s + 1)) → (Fin n → ℤ) → ℂ)
local notation "spatial" => physicalResidueSpatialSiteFactor root D base residue stride radius mesh H t
local notation "twist" => (fun site u => spatial site u * analytic site u)
local notation "mask" => physicalResidueWindowSiteMask root D base residue stride H radius

theorem native_partner_of_spatial_site_source
    (hstride : ∀ i, 0 < stride i) (hmesh : 0 < mesh)
    (hf : ∀ x ∈ integerBox N, ‖f x‖ ≤ 1)
    (hzero : ∀ x, x ∉ integerBox N → f x = 0)
    (ha : ∀ site x, x ∈ integerBox N → ‖analytic site x‖ ≤ 1)
    {p q volume : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hn : (n : ℝ) ≤ p + q)
    (hvolume : 0 < volume) (hratio : (integerBoxCubeCount N (s + 1) : ℝ) / volume ≤ Real.exp q)
    (hsource : Real.exp (-p) ≤ ‖(∑ v ∈ spatialWindow H radius,
      let u := physicalResidueReconstruction root D base residue stride v
      ∏ site, conjugationPower site.card (f (physicalCubeVertexValue u site)) *
        (spatial site (physicalCubeVertexValue u site) * analytic site (physicalCubeVertexValue u site))) /
          (volume : ℂ)‖) :
    ∃ V : NativeSampleCorrelation (fun _ : Fin n => 1) s
      ((p + q + 2) ^ Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))
      (integerBox N) id (fun x => f x * (mask ∅ x * (spatial ∅ x * analytic ∅ x))),
      V.test.normBound ≤ 1 ∧
      Real.exp (-((p + q + 2) ^ Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))) ≤
        ‖𝔼 x ∈ integerBox N, f x * star (star (mask ∅ x * (spatial ∅ x * analytic ∅ x)) * V.test.eval x)‖ := by
  have ht : ∀ site x, x ∈ integerBox N → ‖twist site x‖ ≤ 1 := by
    intro site x hx
    rw [norm_mul]
    exact (mul_le_mul (physicalResidueSpatialSiteFactor_bound root D base residue stride radius hmesh H t site x)
      (ha site x hx) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hsupport := physicalSpatialProduct_support root D base residue stride N H radius mesh t f analytic hzero
  exact native_partner_of_reconstructed_cube_norm root D base residue stride N hstride H radius f twist hf ht
    (fun u hu => (hsupport u hu).1) (fun u hu => (hsupport u hu).2) hp hq hn hvolume hratio hsource

theorem native_partner_of_supported_spatial_site_source
    (hstride : ∀ i, 0 < stride i) (hmesh : 0 < mesh)
    (hf : ∀ x ∈ integerBox N, ‖f x‖ ≤ 1)
    (hzero : ∀ x, x ∉ integerBox N → f x = 0)
    (ha : ∀ site x, x ∈ integerBox N → ‖analytic site x‖ ≤ 1)
    (hwindow : ∀ v, v ∉ spatialWindow H radius →
      (∏ site, spatial site (physicalCubeVertexValue
        (physicalResidueReconstruction root D base residue stride v) site)) = 0)
    {p q volume : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hn : (n : ℝ) ≤ p + q)
    (hvolume : 0 < volume) (hratio : (integerBoxCubeCount N (s + 1) : ℝ) / volume ≤ Real.exp q)
    (hsource : Real.exp (-p) ≤ ‖(∑ v ∈ spatialWindow H radius,
      let u := physicalResidueReconstruction root D base residue stride v
      ∏ site, conjugationPower site.card (f (physicalCubeVertexValue u site)) *
        (spatial site (physicalCubeVertexValue u site) * analytic site (physicalCubeVertexValue u site))) /
          (volume : ℂ)‖) :
    ∃ V : NativeSampleCorrelation (fun _ : Fin n => 1) s
      ((p + q + 2) ^ Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))
      (integerBox N) id (fun x => f x * (spatial ∅ x * analytic ∅ x)),
      V.test.normBound ≤ 1 ∧
      Real.exp (-((p + q + 2) ^ Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))) ≤
        ‖𝔼 x ∈ integerBox N, f x * star (star (spatial ∅ x * analytic ∅ x) * V.test.eval x)‖ := by
  let φ := fun u => ∏ site, conjugationPower site.card (f (physicalCubeVertexValue u site)) *
    (spatial site (physicalCubeVertexValue u site) * analytic site (physicalCubeVertexValue u site))
  have hsupport := physicalSpatialProduct_support root D base residue stride N H radius mesh t f analytic hzero
  have hwindow' (v) (hv : v ∉ spatialWindow H radius) :
      φ (physicalResidueReconstruction root D base residue stride v) = 0 := by
    dsimp only [φ]
    simp only [Finset.prod_mul_distrib]
    rw [hwindow v hv, zero_mul, mul_zero]
  have he := physicalResidueWindow_sum_eq_count_mul_mean root D base residue stride N hstride
    (spatialWindow H radius) φ (fun v _ hv => (hsupport _ hv).1) hwindow'
    (fun u hu => (hsupport u hu).2)
  let z : ℂ := 𝔼 cube : SupportedCube (s + 1) (integerBox N : Set (Fin n → ℤ)),
    φ ((physicalCubeParametersEquiv (Fin n) (s + 1)).symm cube.val)
  have hbound : Real.exp (-p) ≤ Real.exp q * ‖z‖ := by
    change Real.exp (-p) ≤ ‖(∑ v ∈ spatialWindow H radius,
      φ (physicalResidueReconstruction root D base residue stride v)) / (volume : ℂ)‖ at hsource
    rw [he, norm_div, norm_mul] at hsource
    have hc : 0 ≤ (integerBoxCubeCount N (s + 1) : ℝ) := Nat.cast_nonneg _
    simp only [Complex.norm_natCast, Complex.norm_real, Real.norm_of_nonneg hvolume.le] at hsource
    calc
      _ ≤ (integerBoxCubeCount N (s + 1) : ℝ) / volume * ‖z‖ := by
        simpa only [z, div_mul_eq_mul_div] using hsource
      _ ≤ _ := mul_le_mul_of_nonneg_right hratio (norm_nonneg _)
  have hnorm : Real.exp (-(p + q)) ≤ ‖z‖ := by
    have hexp : Real.exp (-(p + q)) = Real.exp (-p) / Real.exp q := by
      rw [← Real.exp_sub]
      congr 1
      ring
    rw [hexp]
    exact (div_le_iff₀ (Real.exp_pos q)).mpr (by simpa only [mul_comm] using hbound)
  apply native_partner_of_physical_cube_norm N (p + q) (add_nonneg hp hq) hn f twist hf ?_ hnorm
  intro site u hu
  rw [norm_mul]
  exact (mul_le_mul (physicalResidueSpatialSiteFactor_bound root D base residue stride radius hmesh H t site u)
    (ha site u hu) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

end Erdos3

end

end OAI
