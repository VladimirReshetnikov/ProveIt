import OAI.Combinatorics.Progressions.Estimates.AllocatedNormalizedSiteTwist

namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {K X α : Type*} [Fintype K] [Fintype X] [Fintype α]
variable (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
variable (residue : Option K × X → ℤ) (stride N : X → ℕ)
variable {τ : ℝ} (mesh : ℝ≥0) {modulus period : ℕ}
variable (t : X → SpatialSiteLabel α modulus 4 mesh) (site : Finset α)
variable {Y : Type*} (F : Y → ℂ)

local notation "smooth" => physicalResidueSpatialSmooth root D base residue stride 4 mesh
  (trimmedSpatialRootScale τ N stride) (fun x => (N x : ℝ)) t site

noncomputable def physicalSpatialAnalyticContinuous (v : (X → ℝ) × Y) : ℂ :=
  smooth v.1 * F v.2

theorem physicalSpatialAnalytic_normalized [PseudoMetricSpace Y]
    (hN : ∀ x, 0 < N x) (hperiod : ∀ x, stride x * modulus ∣ period)
    (u : X → ℤ) (y : Y) :
    physicalResidueSpatialSiteFactor root D base residue stride 4 mesh
      (trimmedSpatialRootScale τ N stride) t site u * F y =
    physicalResidueSpatialMaskMod root D base residue stride 4 mesh hperiod t site
      (fun x => (u x : ZMod period)) *
    physicalSpatialAnalyticContinuous (τ := τ) root D base residue stride N mesh t site F
      (fun x => (u x : ℝ) / N x, y) := by
  rw [physicalResidueSpatialMaskMod_eval,
    physicalResidueSpatialSiteFactor_normalized root D base residue stride 4 mesh
      (trimmedSpatialRootScale τ N stride) (fun x => (N x : ℝ)) t site
      (fun x => Nat.cast_ne_zero.mpr (hN x).ne')]
  exact mul_assoc _ _ _

theorem physicalSpatialAnalyticContinuous_bounds [PseudoMetricSpace Y]
    (hN : ∀ x, 0 < N x) (hstride : ∀ x, 0 < stride x) (hτ : 0 < τ) (hmesh : 0 < mesh)
    {L : ℝ≥0} (hF : LipschitzWith L F) (hFb : ∀ y, ‖F y‖ ≤ 1)
    {P EX ES Eτ : ℝ} (hP : 0 ≤ P)
    (hbox : (4 : ℝ) ≤ Real.exp P) (hinv : 1 / (mesh : ℝ) ≤ Real.exp P)
    (hX : (Fintype.card X : ℝ) ≤ Real.exp EX)
    (hα : (Fintype.card (Unit ⊕ α) : ℝ) ≤ Real.exp ES)
    (hτexp : 1 / τ ≤ Real.exp Eτ) :
    (∀ v, ‖physicalSpatialAnalyticContinuous (τ := τ) root D base residue stride N mesh t site F v‖ ≤ 1) ∧
      LipschitzWith (⟨Real.exp (ES + EX + (3 * P + 6) + (Eτ + 8)), Real.exp_nonneg _⟩ + L)
        (physicalSpatialAnalyticContinuous (τ := τ) root D base residue stride N mesh t site F) := by
  let Lscale : ℝ≥0 := ⟨8 / τ, div_nonneg (by norm_num) hτ.le⟩
  have hscale (x : X) : |(N x : ℝ) / ((stride x : ℝ) * trimmedSpatialRootScale τ N stride x)| ≤ Lscale := by
    rw [trimmedSpatialRootScale_normalized_ratio N stride hτ hN hstride x]
    exact (abs_of_nonneg (div_nonneg (by norm_num) hτ.le)).le
  have hscaleExp : (Lscale : ℝ) ≤ Real.exp (Eτ + 8) := by
    calc
      _ = 8 * (1 / τ) := by change 8 / τ = 8 * (1 / τ); ring
      _ ≤ Real.exp 8 * Real.exp Eτ := mul_le_mul
        (by linarith [Real.add_one_le_exp (8 : ℝ)] : (8 : ℝ) ≤ Real.exp 8)
        hτexp (div_nonneg zero_le_one hτ.le) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hsp := physicalResidueSpatialSmooth_bounds root D base residue stride 4 mesh
    (trimmedSpatialRootScale τ N stride) (fun x => (N x : ℝ)) t site hmesh hscale
  have hspLip := physicalResidueSpatialSmooth_pre_lipschitz root D base residue stride 4 mesh
    (trimmedSpatialRootScale τ N stride) (fun x => (N x : ℝ)) t site hmesh hscale hP
    (by norm_num) hbox hinv hX hα hscaleExp
  exact VectorPolynomial.normalizedSiteTwistProduct_bounds smooth F hspLip hF hsp.1 hFb

end Erdos3.BooleanCubeKernel

end

end OAI
