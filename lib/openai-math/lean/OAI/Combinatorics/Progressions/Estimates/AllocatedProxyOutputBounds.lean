import OAI.Combinatorics.Progressions.Linear.AllocatedKernelOutputRegularity
import OAI.Combinatorics.Progressions.Probability.CanonicalZeroSpatialDensity

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {M : ℕ} (hM : 0 < M)
variable (hi : ∀ j : Fin m,
  fixedKernelInverseBound S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (M : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMP : (M : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "bound" => NNReal.mk (Real.exp (allocatedDensityLog (G := G) B α O P))
  (le_of_lt (Real.exp_pos _))
local notation "cap" => bound ^ Fintype.card (LayerSamplerAxis I n)
local notation "lip" => (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound * cap
local notation "input" => PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := α) (fun a => ¬grid a)

include hR hσ hM hi hP hMP hRP hRi hσi hcount

theorem allocatedNormalizedLongJetDensity_output_bounds (hσ1 : ∀ j, σ j ≤ 1)
    (y : input → ℝ) :
    (∀ v, allocatedNormalizedLongJetDensity B U basis S x u rows s hA y v ∈
      Set.Icc (0 : ℝ) cap) ∧
    LipschitzWith lip (allocatedNormalizedLongJetDensity B U basis S x u rows s hA y) := by
  have hrow (a : {a // ¬grid a}) :
      (∀ z, |allocatedNormalizedLongJetFactor B U basis S x u rows s hA y a z| ≤ bound) ∧
      LipschitzWith bound (allocatedNormalizedLongJetFactor B U basis S x u rows s hA y a) := by
    rcases a with ⟨⟨j, a⟩, ha⟩
    cases a with
    | inl i =>
      exact allocatedContinuousKernelDensity_output_bounds B U basis hR hσ S x rows s hA
        hM hi hP hMP hRP hRi hσi hcount u hσ1 j i y
    | inr i =>
      exact allocatedIntegerKernelDensity_output_bounds B U basis hR hσ S x rows s hA
        hM hi hP hMP hRP hRi hσi hcount u hσ1 j i y
  have hbound : 1 ≤ bound := by
    exact_mod_cast Real.one_le_exp_iff.mpr (allocatedDensityLog_bounds (G := G) B α O hP).1
  have hs := sigmaAxisWeight_output_bounds
    (allocatedNormalizedLongJetFactor B U basis S x u rows s hA y)
    hbound (fun a => (hrow a).2) (fun a => (hrow a).1)
  have hc : Fintype.card {a // ¬grid a} ≤ Fintype.card (LayerSamplerAxis I n) :=
    Fintype.card_subtype_le _
  have hpow : bound ^ Fintype.card {a // ¬grid a} ≤ cap := pow_le_pow_right₀ hbound hc
  have hcn : (Fintype.card {a // ¬grid a} : ℝ≥0) ≤ Fintype.card (LayerSamplerAxis I n) := by
    exact_mod_cast hc
  have hlip : (Fintype.card {a // ¬grid a} : ℝ≥0) * bound * bound ^ Fintype.card {a // ¬grid a} ≤ lip :=
    mul_le_mul (mul_le_mul_of_nonneg_right hcn zero_le) hpow zero_le zero_le
  refine ⟨fun v => ⟨(allocatedNormalizedLongJetDensity_probability
    B U basis hR hσ S x u rows s hA hσ1 y).1 v, ?_⟩, hs.2.weaken hlip⟩
  exact (le_abs_self _).trans ((hs.1 v).trans (NNReal.coe_le_coe.mpr hpow))

theorem allocatedContinuousLongJetProxy_output_bounds (hσ1 : ∀ j, σ j ≤ 1) :
    (∀ v, allocatedContinuousLongJetProxy B U basis S x u rows s hA v ∈ Set.Icc (0 : ℝ) cap) ∧
    LipschitzWith lip (allocatedContinuousLongJetProxy B U basis S x u rows s hA) := by
  have hm := allocatedNormalizedLongJetDensity_measurable B U basis hR hσ S x u rows s hA hσ1
  exact densityMixture_uniform_bound
    (jointBooleanSource (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val))
    (allocatedNormalizedLongJetDensity B U basis S x u rows s hA) cap lip
    (fun v => (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (allocatedNormalizedLongJetDensity_output_bounds
      B U basis hR hσ S x rows s hA hM hi hP hMP hRP hRi hσi hcount u hσ1))

end Erdos3.VectorPolynomial

end

end OAI
