import OAI.Combinatorics.Progressions.Estimates.AllocatedContinuousProxyAveraging
import OAI.Combinatorics.Progressions.Estimates.PhysicalActiveIdealSite

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [∀ j, Nonempty (O j)]

local notation "hLayer" => layerSamplerDegree I n

theorem exists_allocated_proxy_l1_comparison
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
      (δ : ℝ) = booleanRegularizationRadius (B := B)
        (O := fun a : LayerSamplerAxis I n => O a.1) (α := α) hLayer
        (unitProfilePrincipalSize (B := B)) (fun d => 2 * unitProfilePrincipalSize (B := B) d)
        A T (ε / 2) ∧
      let t := booleanMassPerturbationScale (B := B)
        (O := fun a : LayerSamplerAxis I n => O a.1) (α := α)
        ((G × Option α) ⊕ (Σ d, SamplerCoefficientSlot G B hLayer d)) hLayer
        (unitProfilePrincipalSize (B := B)) (fun d => 2 * unitProfilePrincipalSize (B := B) d)
        A T m 1 (ε / 2)
      0 < t ∧ t ≤ 1 ∧
      ∀ {J : Fin m → Type*} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        {R : Fin m → ℝ} (hR : ∀ j, 0 < R j)
        {σ : Fin m → ℝ} (_hσ : ∀ j, 0 < σ j) (_hσt : ∀ j, σ j ≤ t)
        (S : LayerSamplerScale (G := G) B U basis R σ)
        (x : G → IntegerScalarCubeBox α S.value)
        (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
          (allocatedPrincipalSides B U basis S))
        (rows : ∀ j, O j → Finset α)
        (_hrows : ∀ j, Function.Injective (rows j))
        (_hcard : ∀ j o, (rows j o).card ≤ j.val + 1)
        (_block : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1 ↪ B a.val)
        (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0),
      let ideal := physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer
        (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1)
        (fun a => R a.1) (fun a => hR a.1) δ
      let proxy := allocatedContinuousLongJetProxy B U basis S x u rows s hA
      (∫ v, |ideal v - proxy v|) ≤ ε ∧
      ∀ f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1) → ℝ) → ℂ,
        Measurable f → (∀ v, ‖f v‖ ≤ 1) →
        ‖(∫ v, (ideal v : ℂ) * f v) - ∫ v, (proxy v : ℂ) * f v‖ ≤ ε := by
  obtain ⟨δ, hδ, hδ1, hδeq, ht, ht1, _⟩ := exists_active_fixed_profile_comparison
    (G := G) (Z := G × Option α) (B := B)
    (O := fun a : LayerSamplerAxis I n => O a.1) (α := α)
    hLayer (fun _ => Nat.succ_pos _) ψ hψ hrange hzero hone A T hLip hTransition
    (degree := m) (fun a => Nat.succ_le_of_lt a.1.isLt) hε
  refine ⟨δ, hδ, hδ1, hδeq, ht, ht1, ?_⟩
  intro J _ U basis R hR σ hσ hσt S x u rows hrows hcard block s hA
  obtain ⟨δ', _, _, hδ'eq, _, _, hcomp⟩ := exists_allocated_tail_test_comparison
    B U basis hR hσ S x u rows hrows hcard
    ψ hψ hrange hzero hone A T hLip hTransition hε
  have hsame : δ' = δ := NNReal.coe_injective (hδ'eq.trans hδeq.symm)
  subst δ'
  have hσ1 : ∀ j, σ j ≤ 1 := fun j => (hσt j).trans ht1
  have hpi := physicalActiveProfileIdeal_probability (G := G) (B := B) (G × Option α)
    hLayer (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1)
    (fun a => R a.1) (fun a => hR a.1) δ hδ
  have hpm := physicalActiveProfileIdeal_measurable (G := G) (B := B) (G × Option α)
    hLayer (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1)
    (fun a => R a.1) (fun a => hR a.1) δ
  have hqi := allocatedContinuousLongJetProxy_probability B U basis hR hσ S x u rows s hA hσ1
  have hqm : Measurable (allocatedContinuousLongJetProxy B U basis S x u rows s hA) :=
    (allocatedNormalizedLongJetDensity_measurable
    B U basis hR hσ S x u rows s hA hσ1).stronglyMeasurable.integral_prod_left'.measurable
  dsimp only
  have hL1 := density_l1_le_of_bounded_tests volume _ _ hpm hqm hpi.2.1 hqi.2.1
    (ε := ε) (fun f hf hb => by
      rw [physicalActiveProfileIdeal_test_integral]
      exact hcomp hσt (fun a => (block a : O a.val.1 → B a.val))
        (fun a => (block a).injective) s hA f hf hb)
  refine ⟨hL1, ?_⟩
  intro f hf hb
  exact (density_bounded_complex_test_error volume _ _ hpi.2.1 hqi.2.1 f hf hb).trans
    (by simpa only [one_mul] using hL1)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [∀ j, Nonempty (O j)]

local notation "hLayer" => layerSamplerDegree I n

theorem exists_allocated_proxy_l1_averaging
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
      (δ : ℝ) = booleanRegularizationRadius (B := B)
        (O := fun a : LayerSamplerAxis I n => O a.1) (α := α) hLayer
        (unitProfilePrincipalSize (B := B)) (fun d => 2 * unitProfilePrincipalSize (B := B) d)
        A T (ε / 2) ∧
      let t := booleanMassPerturbationScale (B := B)
        (O := fun a : LayerSamplerAxis I n => O a.1) (α := α)
        ((G × Option α) ⊕ (Σ d, SamplerCoefficientSlot G B hLayer d)) hLayer
        (unitProfilePrincipalSize (B := B)) (fun d => 2 * unitProfilePrincipalSize (B := B) d)
        A T m 1 (ε / 2)
      0 < t ∧ t ≤ 1 ∧
      ∀ {J : Fin m → Type*} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        {R : Fin m → ℝ} (hR : ∀ j, 0 < R j)
        {σ : Fin m → ℝ} (_hσ : ∀ j, 0 < σ j) (_hσt : ∀ j, σ j ≤ t)
        (S : LayerSamplerScale (G := G) B U basis R σ)
        (x : G → IntegerScalarCubeBox α S.value)
        (rows : ∀ j, O j → Finset α)
        (_hrows : ∀ j, Function.Injective (rows j))
        (_hcard : ∀ j o, (rows j o).card ≤ j.val + 1)
        (_block : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1 ↪ B a.val)
        (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
        {Ω : Type*} [Fintype Ω] (weights : FiniteProbabilityWeights Ω)
        (u : Ω → PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
          (allocatedPrincipalSides B U basis S)),
      let ideal := physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer
        (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1)
        (fun a => R a.1) (fun a => hR a.1) δ
      let proxy := fun a => allocatedContinuousLongJetProxy B U basis S x (u a) rows s hA
      weights.mean (fun a => ∫ v, |ideal v - proxy a v|) ≤ ε ∧
      ∀ f : Ω → ((Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1) → ℝ) → ℂ,
        (∀ a, Measurable (f a)) → (∀ a v, ‖f a v‖ ≤ 1) →
        ‖weights.complexMean (fun a => ∫ v, (ideal v : ℂ) * f a v) -
          weights.complexMean (fun a => ∫ v, (proxy a v : ℂ) * f a v)‖ ≤ ε := by
  obtain ⟨δ, hδ, hδ1, hδeq, ht, ht1, hpoint⟩ := exists_allocated_proxy_l1_comparison
    (G := G) (α := α) (O := O) B ψ hψ hrange hzero hone A T hLip hTransition hε
  refine ⟨δ, hδ, hδ1, hδeq, ht, ht1, ?_⟩
  intro J _ U basis R hR σ hσ hσt S x rows hrows hcard block s hA Ω _ weights u
  dsimp only
  have hp := fun a => hpoint U basis hR hσ hσt S x (u a) rows hrows hcard block s hA
  refine ⟨(weights.mean_mono (fun a => (hp a).1)).trans_eq (weights.mean_const ε), ?_⟩
  intro f hf hb
  exact (weights.norm_complexMean_sub_le _ _ (fun _ => ε)
    (fun a _ => (hp a).2 (f a) (hf a) (hb a))).trans_eq (weights.mean_const ε)

end Erdos3.VectorPolynomial

end

end OAI
