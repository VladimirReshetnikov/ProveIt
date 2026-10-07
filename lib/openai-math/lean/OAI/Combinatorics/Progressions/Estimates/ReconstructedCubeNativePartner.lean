import OAI.Combinatorics.Progressions.Lattices.PhysicalResidueWindowSiteMask
import OAI.Combinatorics.Progressions.Polynomial.CubeMixtureAllDegrees

namespace OAI

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical
attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem native_partner_of_physical_cube_norm {s n : ℕ} (N : Fin n → ℕ)
    [∀ i, NeZero (N i)] (p : ℝ) (hp : 0 ≤ p) (hn : (n : ℝ) ≤ p)
    (f : (Fin n → ℤ) → ℂ) (twist : Finset (Fin (s + 1)) → (Fin n → ℤ) → ℂ)
    (hf : ∀ x ∈ integerBox N, ‖f x‖ ≤ 1)
    (ht : ∀ site x, x ∈ integerBox N → ‖twist site x‖ ≤ 1)
    (hsource : Real.exp (-p) ≤ ‖𝔼 cube : SupportedCube (s + 1) (integerBox N : Set (Fin n → ℤ)),
      let u := (physicalCubeParametersEquiv (Fin n) (s + 1)).symm cube.val
      ∏ site, conjugationPower site.card (f (physicalCubeVertexValue u site)) *
        twist site (physicalCubeVertexValue u site)‖) :
    ∃ V : NativeSampleCorrelation (fun _ : Fin n => 1) s
      ((p + 2) ^ Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))
      (integerBox N) id (fun x => f x * twist ∅ x),
      V.test.normBound ≤ 1 ∧
      Real.exp (-((p + 2) ^ Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))) ≤
        ‖𝔼 x ∈ integerBox N, f x * star (star (twist ∅ x) * V.test.eval x)‖ := by
  let z : ℂ := 𝔼 cube : SupportedCube (s + 1) (integerBox N : Set (Fin n → ℤ)),
    let u := (physicalCubeParametersEquiv (Fin n) (s + 1)).symm cube.val
    ∏ site, conjugationPower site.card (f (physicalCubeVertexValue u site)) *
      twist site (physicalCubeVertexValue u site)
  obtain ⟨c, hc, hcz⟩ := Complex.exists_norm_eq_mul_self z
  have hmass : (∑ _ : Unit, ‖c‖) ≤ Real.exp p := by
    simpa only [Finset.univ_unique, Finset.sum_singleton, hc] using Real.one_le_exp hp
  have hpositive : Real.exp (-p) ≤ (c * z).re := by
    rw [← hcz, Complex.ofReal_re]
    exact hsource
  have he : ‖c * z - ∑ _ : Unit, c * z‖ ≤ Real.exp (-p) / 2 := by
    simp only [Finset.univ_unique, Finset.sum_singleton, sub_self, norm_zero]
    positivity
  obtain ⟨i, V, hV, hcorr⟩ :=
    (Classical.choose_spec (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s)).2
      N p hp hn f (fun _ : Unit => c) (fun _ => twist) hf (fun _ => ht) hmass (c * z) hpositive he
  exact ⟨V, hV, hcorr⟩

end Erdos3

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical
attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem native_partner_of_reconstructed_cube_norm {s n : ℕ} {K : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix (Fin (s + 1)) K ℤ) (base : Fin n → ℤ)
    (residue : Option K × Fin n → ℤ) (stride N : Fin n → ℕ)
    [∀ i, NeZero (N i)] (hstride : ∀ i, 0 < stride i)
    (H : Fin n → ℝ) (radius : ℝ)
    (f : (Fin n → ℤ) → ℂ) (twist : Finset (Fin (s + 1)) → (Fin n → ℤ) → ℂ)
    (hf : ∀ x ∈ integerBox N, ‖f x‖ ≤ 1)
    (ht : ∀ site x, x ∈ integerBox N → ‖twist site x‖ ≤ 1)
    (hbox : ∀ u, (∏ site, conjugationPower site.card (f (physicalCubeVertexValue u site)) *
        twist site (physicalCubeVertexValue u site)) ≠ 0 →
      ∀ site, physicalCubeVertexValue u site ∈ integerBox N)
    (hresidue : ∀ u, (∏ site, conjugationPower site.card (f (physicalCubeVertexValue u site)) *
        twist site (physicalCubeVertexValue u site)) ≠ 0 →
      u ∈ Set.range (physicalResidueReconstruction root D base residue stride))
    {p q volume : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hn : (n : ℝ) ≤ p + q)
    (hvolume : 0 < volume) (hratio : (integerBoxCubeCount N (s + 1) : ℝ) / volume ≤ Real.exp q)
    (hsource : Real.exp (-p) ≤ ‖(∑ v ∈ spatialWindow H radius,
      let u := physicalResidueReconstruction root D base residue stride v
      ∏ site, conjugationPower site.card (f (physicalCubeVertexValue u site)) *
        twist site (physicalCubeVertexValue u site)) / (volume : ℂ)‖) :
    let mask := physicalResidueWindowSiteMask root D base residue stride H radius
    ∃ V : NativeSampleCorrelation (fun _ : Fin n => 1) s
      ((p + q + 2) ^ Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))
      (integerBox N) id (fun x => f x * (mask ∅ x * twist ∅ x)),
      V.test.normBound ≤ 1 ∧
      Real.exp (-((p + q + 2) ^ Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))) ≤
        ‖𝔼 x ∈ integerBox N, f x * star (star (mask ∅ x * twist ∅ x) * V.test.eval x)‖ := by
  intro mask
  have hb := physicalResidueWindow_norm_le_cube_mean root base residue stride H radius D N hstride
    (fun site u => conjugationPower site.card (f u) * twist site u) hbox hresidue hvolume hratio
  let z : ℂ := 𝔼 cube : SupportedCube (s + 1) (integerBox N : Set (Fin n → ℤ)),
    let u := (physicalCubeParametersEquiv (Fin n) (s + 1)).symm cube.val
    ∏ site, conjugationPower site.card (f (physicalCubeVertexValue u site)) *
      (mask site (physicalCubeVertexValue u site) * twist site (physicalCubeVertexValue u site))
  have hz : Real.exp (-p) ≤ Real.exp q * ‖z‖ := by
    simpa only [z, mask, mul_assoc, mul_left_comm, mul_comm] using hsource.trans hb
  have hnorm : Real.exp (-(p + q)) ≤ ‖z‖ := by
    have he : Real.exp (-(p + q)) = Real.exp (-p) / Real.exp q := by
      rw [← Real.exp_sub]
      congr 1
      ring
    rw [he]
    exact (div_le_iff₀ (Real.exp_pos q)).mpr (by simpa only [mul_comm] using hz)
  apply native_partner_of_physical_cube_norm N (p + q) (add_nonneg hp hq) hn f
    (fun site u => mask site u * twist site u) hf ?_ hnorm
  intro site u hu
  rw [norm_mul]
  exact (mul_le_mul (physicalResidueWindowSiteMask_bound root D base residue stride H radius site u)
    (ht site u hu) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

end Erdos3

end

end OAI
