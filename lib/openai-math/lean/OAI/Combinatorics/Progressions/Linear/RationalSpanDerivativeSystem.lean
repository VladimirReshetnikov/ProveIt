import Mathlib.Analysis.InnerProductSpace.PiL2
import OAI.Combinatorics.Progressions.Estimates.FirstCoefficientDerivativeBounds
import OAI.Combinatorics.Progressions.Geometry.WeightedCoordinateExtraction

namespace OAI

section

namespace Erdos3

open Module

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E]

noncomputable def basisWeightedCoordinates (b : Basis ι ℝ E) (scale : ι → ℝ) :
    E →ₗ[ℝ] (ι → ℝ) :=
  LinearMap.pi (fun i => scale i • b.coord i)

@[simp] theorem basisWeightedCoordinates_apply (b : Basis ι ℝ E) (scale : ι → ℝ)
    (x : E) (i : ι) :
    basisWeightedCoordinates b scale x i = scale i * b.repr x i := rfl

theorem basisWeightedCoordinates_norm_le_iff [Fintype ι]
    (b : Basis ι ℝ E) (scale : ι → ℝ) (hscale : ∀ i, 0 < scale i)
    {M : ℝ} (hM : 0 ≤ M) (x : E) :
    ‖basisWeightedCoordinates b scale x‖ ≤ M ↔ ∀ i, |b.equivFun x i| ≤ M / scale i := by
  constructor
  · intro hx i
    apply (le_div_iff₀ (hscale i)).mpr
    have hi := (norm_le_pi_norm (basisWeightedCoordinates b scale x) i).trans hx
    simpa only [basisWeightedCoordinates_apply, Real.norm_eq_abs, abs_mul,
      abs_of_pos (hscale i), Basis.equivFun_apply, mul_comm] using hi
  · intro hx
    apply (pi_norm_le_iff_of_nonneg hM).mpr
    intro i
    have hi := (le_div_iff₀ (hscale i)).mp (hx i)
    simpa only [basisWeightedCoordinates_apply, Real.norm_eq_abs, abs_mul,
      abs_of_pos (hscale i), Basis.equivFun_apply, mul_comm] using hi

theorem basisWeightedCoordinates_operator_bound [Fintype ι]
    (b : Basis ι ℝ E) (scale : ι → ℝ) (hscale : ∀ i, 0 < scale i)
    (A : E →ₗ[ℝ] E) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ M, 0 ≤ M → ∀ x, (∀ i, |b.equivFun x i| ≤ M / scale i) →
      ∀ i, |b.equivFun (A x) i| ≤ C * M / scale i) (x : E) :
    ‖basisWeightedCoordinates b scale (A x)‖ ≤ C * ‖basisWeightedCoordinates b scale x‖ := by
  apply (basisWeightedCoordinates_norm_le_iff b scale hscale
    (mul_nonneg hC (norm_nonneg _)) (A x)).mpr
  exact hA _ (norm_nonneg _) x
    ((basisWeightedCoordinates_norm_le_iff b scale hscale (norm_nonneg _) x).mp le_rfl)

theorem basisWeightedCoordinates_norm_le_euclidean [Fintype ι]
    (b : Basis ι ℝ E) (scale : ι → ℝ) (x : E) :
    ‖basisWeightedCoordinates b scale x‖ ≤
      ‖(EuclideanSpace.equiv ι ℝ).symm (basisWeightedCoordinates b scale x)‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact PiLp.norm_apply_le
    ((EuclideanSpace.equiv ι ℝ).symm (basisWeightedCoordinates b scale x)) i

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem transport_coordinate_derivatives_to_rational_span
    {σ E V : Type*} [Fintype σ] [DecidableEq σ]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup V] [Module ℚ V]
    {a d : ℕ} (ha : a ≤ d) (b : Basis (Fin d) ℝ E)
    (η : (Fin a → ℝ) ≃ₗ[ℝ] (ℝ ⊗[ℚ] V)) (P : E →ₗ[ℝ] (ℝ ⊗[ℚ] V))
    (hP : ∀ x, η (fun i => b.equivFun x (Fin.castLE ha i)) = P x)
    (T : σ → ℝ) (Y : (σ → ℝ) →ₗ[ℝ] E) (f : E ≃ₗ[ℝ] E)
    (scale : Fin d → ℝ) (bound : ℝ)
    (D : CoordinateDerivativeSystem ha T (b.equivFun.toLinearMap.comp Y)
      (b.equivFun.symm.trans (f.trans b.equivFun)) scale bound)
    (K : Submodule ℚ V) (bK : Basis (Fin D.k) ℚ K)
    (hspan : D.K.map η.toLinearMap = K.baseChange ℝ)
    (hbasis : ∀ j, (1 : ℝ) ⊗ₜ[ℚ] (bK j : V) = η ((D.basisMatrix.map (Rat.castHom ℝ)).col j)) :
    ∃ S R : (K.baseChange ℝ) →ₗ[ℝ] E,
      S = f.toLinearMap.comp R ∧ P.comp S = (K.baseChange ℝ).subtype ∧
      P.comp R = (K.baseChange ℝ).subtype ∧
      (∀ x, ‖basisWeightedCoordinates b scale (S x)‖ ≤ bound * ‖η.symm x.val‖) ∧
      (∀ j, b.equivFun (R (realSubmoduleBasis K bK j)) ∈ realDenominatorGrid D.liftDenominator) ∧
      ∃ (small rational : σ → E) (k : σ → K.baseChange ℝ),
        (∀ i, Y (Pi.single i 1) = small i + f (rational i) + S (k i)) ∧
        (∀ i, b.equivFun (rational i) ∈ realDenominatorGrid D.derivativeDenominator) ∧
        (∀ i, ‖basisWeightedCoordinates b scale (small i)‖ ≤ bound / T i) := by
  have hraw := transport_coordinate_derivative_system ha b η P hP T Y f scale bound D
  obtain ⟨_, R₀, S₀, hSR₀, hR₀, hS₀, hnorm₀, hgrid₀, hsystem₀⟩ := hraw
  let eK : (K.baseChange ℝ) ≃ₗ[ℝ] D.K.map η.toLinearMap :=
    LinearEquiv.ofEq _ _ hspan.symm
  have heK (x : K.baseChange ℝ) : (eK x).val = x.val :=
    LinearEquiv.coe_ofEq_apply hspan.symm x
  let S := S₀.comp eK.toLinearMap
  let R := R₀.comp eK.toLinearMap
  have hSR : S = f.toLinearMap.comp R := by
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun hSR₀ (eK x)
  have hS : P.comp S = (K.baseChange ℝ).subtype := by
    apply LinearMap.ext
    intro x
    exact (hS₀ (eK x)).trans (heK x)
  have hR : P.comp R = (K.baseChange ℝ).subtype := by
    apply LinearMap.ext
    intro x
    exact (hR₀ (eK x)).trans (heK x)
  refine ⟨S, R, hSR, hS, hR, ?_, ?_, ?_⟩
  · intro x
    have h := (basisWeightedCoordinates_norm_le_euclidean b scale (S x)).trans (hnorm₀ (eK x))
    simpa only [heK] using h
  · intro j
    obtain ⟨x, hx, hg⟩ := hgrid₀ j
    have he : eK (realSubmoduleBasis K bK j) = x := by
      apply Subtype.ext
      exact (heK _).trans ((realSubmoduleBasis_coe K bK j).trans ((hbasis j).trans hx.symm))
    exact (congrArg (fun z => b.equivFun (R₀ z) ∈ realDenominatorGrid D.liftDenominator) he).mpr hg
  · choose small rational k₀ hsystem hgrid hsmall using hsystem₀
    refine ⟨small, rational, fun i => eK.symm (k₀ i), ?_, hgrid, ?_⟩
    · intro i
      have he : S (eK.symm (k₀ i)) = S₀ (k₀ i) :=
        congrArg S₀ (eK.apply_symm_apply (k₀ i))
      have hi : Pi.basisFun ℝ σ i = (Pi.single i 1 : σ → ℝ) := Pi.basisFun_apply ℝ σ i
      exact (congrArg Y hi).symm.trans
        ((hsystem i).trans (congrArg (fun z => small i + f (rational i) + z) he.symm))
    · intro i
      exact (basisWeightedCoordinates_norm_le_euclidean b scale (small i)).trans (hsmall i)

end Erdos3

end

end OAI
