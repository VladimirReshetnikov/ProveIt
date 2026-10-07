/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Estimates.AllocatedTailProfileIdentity

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal

theorem exists_active_fixed_profile_comparison
    {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {degree : ℕ} (hdegree : ∀ d, h d ≤ degree) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
      (δ : ℝ) = booleanRegularizationRadius (B := B) (O := O) (α := α) h
        (unitProfilePrincipalSize (B := B)) (fun d => 2 * unitProfilePrincipalSize (B := B) d)
        A T (ε / 2) ∧
      let t := booleanMassPerturbationScale (B := B) (O := O) (α := α)
        (Z ⊕ (Σ d, SamplerCoefficientSlot G B h d)) h
        (unitProfilePrincipalSize (B := B)) (fun d => 2 * unitProfilePrincipalSize (B := B) d)
        A T degree 1 (ε / 2)
      0 < t ∧ t ≤ 1 ∧
      ∀ (P : D → Prop) [DecidablePred P],
      ∀ (extra : G → Option α → Z) (sets : ∀ d : {d // ¬P d}, O d.val → Finset α),
      (∀ d, Function.Injective (sets d)) → (∀ d o, (sets d o).card ≤ h d.val) →
      ∀ block : ∀ d : {d // ¬P d}, O d.val → B d.val,
      (∀ d, Function.Injective (block d)) →
      ∀ z : PartitionedProfileNoiseIndex G Z α B h P → ℝ,
      (∀ j, |z j| ≤ 1) → ∀ s : ℝ, |s| ≤ t →
      ∀ R : D → ℝ, ∀ f : ((Σ d : {d // ¬P d}, O d.val) → ℝ) → ℝ,
      Measurable f → (∀ v, ‖f v‖ ≤ 1) →
      |(∫ v, activeAveragedProfileIdeal (G := G) (B := B) Z h P sets δ v *
          f (fun o => R o.1.val * v o)) -
        ∫ p, f (partitionedAllocatedProfileJet h P extra sets R s
          (profileNoiseWithActive h P z p.1) p.2)
          ∂(unitCoefficientSource (ActiveProfileCoefficientIndex G B h P)).prod
            (jointBooleanSource (fun d : {d // ¬P d} => h d.val))| ≤ ε := by
  classical
  obtain ⟨δ, hδ, hδ1, hδeq, ht, ht1, _⟩ := exists_uniform_regularized_profile_comparison
    (Ω := Unit) (G := G) (Z := Z) (B := B) (O := O) (α := α)
    h hh ψ hψ hrange hzero hone A T hLip hTransition hdegree hε
  refine ⟨δ, hδ, hδ1, hδeq, ht, ht1, ?_⟩
  intro P instP extra sets hsets hcard block hblock z hz s hs R f hf hfb
  obtain ⟨δ', _, _, hδ'eq, _, _, hcomp⟩ := exists_uniform_regularized_profile_comparison
    (Ω := ActiveProfileCoefficientIndex G B h P → ℝ)
    (G := G) (Z := Z) (B := B) (O := O) (α := α)
    h hh ψ hψ hrange hzero hone A T hLip hTransition hdegree hε
  have hsame : δ' = δ := NNReal.coe_injective (hδ'eq.trans hδeq.symm)
  subst δ'
  let ζ := fun r : ActiveProfileCoefficientIndex G B h P → ℝ => profileNoiseWithActive h P z r
  have hζ (j : PartitionedProfileNoiseIndex G Z α B h P) : Measurable (fun r => ζ r j) :=
    profileNoiseWithActive_measurable h P (fun _ => z) id
      (fun _ => measurable_const) (fun i => measurable_pi_apply i) j
  have hζbox : ∀ᵐ r ∂unitCoefficientSource (ActiveProfileCoefficientIndex G B h P),
      ∀ j, |ζ r j| ≤ 1 := by
    filter_upwards [unitCoefficientSource_abs_le (ActiveProfileCoefficientIndex G B h P)] with r hr
    exact profileNoiseWithActive_abs_le h P z r hz hr
  have he := hcomp P extra sets hsets hcard block hblock ζ hζ s hs
    (unitCoefficientSource (ActiveProfileCoefficientIndex G B h P)) inferInstance hζbox R
    (fun p => f p.2) (hf.comp measurable_snd) (fun p => hfb p.2)
  simp only [ζ, partitionedRegularizedIdeal_withActive_eq] at he
  let Φ := fun v : (Σ d : {d // ¬P d}, O d.val) → ℝ => f (fun o => R o.1.val * v o)
  have hΦ : Measurable Φ := hf.comp (Measurable.of_eval (fun o =>
    measurable_const.mul (measurable_pi_apply o)))
  have hm := activeProfileIdeal_measurable (G := G) (B := B) Z h P sets δ
  have hprob := fun r : ActiveProfileCoefficientIndex G B h P → ℝ =>
    partitionedRegularizedIdeal_probability h P sets δ hδ
    (profileNoiseWithActive (Z := Z) (α := α) h P (fun _ => 0) r)
  have hD := densityMixture_joint_integrable
    (unitCoefficientSource (ActiveProfileCoefficientIndex G B h P)) volume
    (activeProfileIdeal Z h P sets δ) hm (Filter.Eventually.of_forall hprob)
  have hi : Integrable
      (fun p : (ActiveProfileCoefficientIndex G B h P → ℝ) × ((Σ d : {d // ¬P d}, O d.val) → ℝ) =>
        activeProfileIdeal Z h P sets δ p.1 p.2 * Φ p.2)
      ((unitCoefficientSource (ActiveProfileCoefficientIndex G B h P)).prod volume) :=
    hD.mul_bdd (hΦ.comp measurable_snd).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hfb (fun o => R o.1.val * p.2 o)))
  have havg :
      (∫ p : (ActiveProfileCoefficientIndex G B h P → ℝ) × ((Σ d : {d // ¬P d}, O d.val) → ℝ),
        activeProfileIdeal Z h P sets δ p.1 p.2 * Φ p.2
        ∂(unitCoefficientSource (ActiveProfileCoefficientIndex G B h P)).prod volume) =
      ∫ v, activeAveragedProfileIdeal (G := G) (B := B) Z h P sets δ v * Φ v := by
    rw [integral_prod _ hi]
    exact (densityMixture_test_integral
      (unitCoefficientSource (ActiveProfileCoefficientIndex G B h P)) volume
      (activeProfileIdeal Z h P sets δ) hD Φ hΦ
      (fun v => hfb (fun o => R o.1.val * v o))).symm
  change |(∫ p : (ActiveProfileCoefficientIndex G B h P → ℝ) × ((Σ d : {d // ¬P d}, O d.val) → ℝ),
      activeProfileIdeal Z h P sets δ p.1 p.2 * Φ p.2
      ∂(unitCoefficientSource (ActiveProfileCoefficientIndex G B h P)).prod volume) -
    ∫ p, f (partitionedAllocatedProfileJet h P extra sets R s
      (profileNoiseWithActive h P z p.1) p.2)
      ∂(unitCoefficientSource (ActiveProfileCoefficientIndex G B h P)).prod
        (jointBooleanSource (fun d : {d // ¬P d} => h d.val))| ≤ ε at he
  rw [havg] at he
  exact he

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "activeInput" => PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a)
local notation "activeCoefficient" => ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) grid
local notation "realOutput" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

include hR hσ in
theorem allocatedContinuousLongJetProxy_test_integral (hσ1 : ∀ j, σ j ≤ 1)
    (f : (realOutput → ℝ) → ℝ) (hf : Measurable f) :
    (∫ v, allocatedContinuousLongJetProxy B U basis S x u rows s hA v * f v) =
      ∫ p : (activeCoefficient → ℝ) × (activeInput → ℝ),
        f (allocatedNormalizedLongJetMap B U basis S x u rows p.2 p.1)
        ∂(unitCoefficientSource activeCoefficient).prod
          (jointBooleanSource (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val)) := by
  have hm := allocatedNormalizedLongJetMap_measurable B U basis S x u rows
  have hd : Measurable (allocatedContinuousLongJetProxy B U basis S x u rows s hA) :=
    (allocatedNormalizedLongJetDensity_measurable B U basis hR hσ S x u rows s hA hσ1).stronglyMeasurable.integral_prod_left'.measurable
  have hp := allocatedContinuousLongJetProxy_probability B U basis hR hσ S x u rows s hA hσ1
  have ht := mappedTest_eq_density
    ((jointBooleanSource (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val)).prod
      (unitCoefficientSource activeCoefficient)) volume
    (fun p => allocatedNormalizedLongJetMap B U basis S x u rows p.1 p.2) hm
    (allocatedContinuousLongJetProxy B U basis S x u rows s hA) hd hp.1
    (allocatedContinuousLongJetProxy_image_law B U basis hR hσ S x u rows s hA hσ1) f hf
  change (∫ p, f (allocatedNormalizedLongJetMap B U basis S x u rows p.1 p.2)
    ∂(jointBooleanSource (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val)).prod
      (unitCoefficientSource activeCoefficient)) = _ at ht
  exact ht.symm.trans (integral_prod_swap
    (fun p : (activeInput → ℝ) × (activeCoefficient → ℝ) =>
      f (allocatedNormalizedLongJetMap B U basis S x u rows p.1 p.2))).symm

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S

noncomputable def allocatedFrozenComparisonNoise :
    PartitionedProfileNoiseIndex G (G × Option α) α B (layerSamplerDegree I n) grid → ℝ :=
  Sum.elim
    (Sum.elim (fun ga => ((x ga.1 ga.2 : ℤ) : ℝ) / (S.value : ℝ))
      (principalTupleNormalized (principalAxisLength grid sides) u))
    (fun _ => 0)

omit [DecidableEq α] in
theorem allocatedFrozenComparisonNoise_abs_le
    (j : PartitionedProfileNoiseIndex G (G × Option α) α B (layerSamplerDegree I n) grid) :
    |allocatedFrozenComparisonNoise B U basis S x u j| ≤ 1 := by
  rcases j with (ga | a) | a
  · exact (norm_le_pi_norm (fun i => ((x ga.1 i : ℤ) : ℝ) / (S.value : ℝ)) ga.2).trans
      (integerScalarCubeBox_normalized_norm_le S.positive (x ga.1))
  · have hbound := principalTuple_normalized_norm_le
      (fun a : {a // grid a} => B a.val) (fun a => layerSamplerDegree I n a.val)
      (L := principalAxisLength grid sides)
      (fun j => allocatedPrincipalSides_pos B U basis S ⟨j.1.val, j.2⟩) u
    exact (norm_le_pi_norm (principalTupleNormalized (principalAxisLength grid sides) u) a).trans hbound
  · simp only [allocatedFrozenComparisonNoise, Sum.elim_inr, abs_zero, zero_le_one]

theorem allocatedNormalizedLongJetMap_partitioned
    {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    (rows : ∀ j, O j → Finset α) {t : ℝ} (hσ : σ = fun _ => t)
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ)
    (r : ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) grid → ℝ) :
    allocatedNormalizedLongJetMap B U basis S x u rows y r =
      partitionedAllocatedProfileJet (layerSamplerDegree I n) grid (fun g a => (g, a))
        (fun a => rows a.val.1) (fun a => R a.1) t
        (profileNoiseWithActive (layerSamplerDegree I n) grid
          (allocatedFrozenComparisonNoise B U basis S x u) r) y := by
  subst σ
  funext o
  rw [allocatedPartitionedProfileJet_eq]
  change booleanCoefficient (fun s => MvPolynomial.eval _
      (allocatedAxisProfilePolynomial B R (fun _ => t) o.1.val (fun e => r ⟨o.1, e⟩))) _ = _
  simp only [profileNoiseWithActive_active]
  rfl

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

theorem exists_allocated_continuous_proxy_comparison
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
      (δ : ℝ) = booleanRegularizationRadius (B := B) (O := (fun a : LayerSamplerAxis I n => O a.1)) (α := α) hLayer
        (unitProfilePrincipalSize (B := B)) (fun d => 2 * unitProfilePrincipalSize (B := B) d)
        A T (ε / 2) ∧
      let t := booleanMassPerturbationScale (B := B) (O := (fun a : LayerSamplerAxis I n => O a.1)) (α := α)
        ((G × Option α) ⊕ (Σ d, SamplerCoefficientSlot G B hLayer d)) hLayer
        (unitProfilePrincipalSize (B := B)) (fun d => 2 * unitProfilePrincipalSize (B := B) d)
        A T m 1 (ε / 2)
      0 < t ∧ t ≤ 1 ∧
      ∀ {J : Fin m → Type*} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        {R : Fin m → ℝ} (_hR : ∀ j, 0 < R j) {σ : ℝ} (_hσ : 0 < σ) (_hσt : σ ≤ t)
        (S : LayerSamplerScale (G := G) B U basis R (fun _ => σ))
        (x : G → IntegerScalarCubeBox α S.value)
        (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
          (allocatedPrincipalSides B U basis S))
        (rows : ∀ j, O j → Finset α)
        (_hrows : ∀ j, Function.Injective (rows j))
        (_hcard : ∀ j o, (rows j o).card ≤ j.val+1)
        (_block : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1 ↪ B a.val)
        (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
        (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1) → ℝ) → ℝ),
        Measurable f → (∀ v, ‖f v‖ ≤ 1) →
        |(∫ v, activeAveragedProfileIdeal (G := G) (B := B) (G × Option α) hLayer
            (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1) δ v *
            f (fun o => R o.1.val.1 * v o)) -
          ∫ v, allocatedContinuousLongJetProxy B U basis S x u rows s hA v * f v| ≤ ε := by
  obtain ⟨δ, hδ, hδ1, hδeq, ht, ht1, hcompare⟩ := exists_active_fixed_profile_comparison
    (G := G) (Z := G × Option α) (B := B) (O := (fun a : LayerSamplerAxis I n => O a.1)) (α := α)
    hLayer (fun _ => Nat.succ_pos _) ψ hψ hrange hzero hone A T hLip hTransition
    (degree := m) (fun a => Nat.succ_le_of_lt a.1.isLt) hε
  refine ⟨δ, hδ, hδ1, hδeq, ht, ht1, ?_⟩
  intro J _ U basis R hR σ hσ hσt S x u rows hrows hcard block s hA f hf hfb
  let P := allocatedGridAxis (I := I) U basis S.value
  have hσ1 : ∀ _j : Fin m, σ ≤ 1 := fun _ => hσt.trans ht1
  have hσabs := (abs_of_pos hσ).le.trans hσt
  have he := hcompare P (fun g a => (g, a)) (fun a => rows a.val.1)
    (fun a => hrows a.val.1) (fun a => hcard a.val.1)
    (fun a => (block a : O a.val.1 → B a.val)) (fun a => (block a).injective)
    (allocatedFrozenComparisonNoise B U basis S x u)
    (allocatedFrozenComparisonNoise_abs_le B U basis S x u) σ hσabs (fun a => R a.1) f hf hfb
  have hmap := allocatedNormalizedLongJetMap_partitioned B U basis S x u rows (t := σ) rfl
  dsimp only [P] at he
  simp_rw [← hmap] at he
  rw [← allocatedContinuousLongJetProxy_test_integral B U basis hR (fun _ => hσ)
    S x u rows s hA hσ1 f hf] at he
  exact he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [∀ j, Nonempty (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "activeInput" => PrincipalAxisParameter (B := B) (h := degree) (α := α) (fun a => ¬grid a)
local notation "activeCoefficient" => ActiveProfileCoefficientIndex G B degree grid
local notation "realOutput" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "sets" => (fun a : {a // ¬grid a} => rows (Sigma.fst (Subtype.val a)))

include hR hσ hrows hcard in
theorem exists_allocated_tail_test_comparison
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
      (δ : ℝ) = booleanRegularizationRadius (B := B) (O := fun a => O a.1) (α := α) degree
        (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
        A T (ε / 2) ∧
      let t := booleanMassPerturbationScale (B := B) (O := fun a => O a.1) (α := α)
        ((G × Option α) ⊕ (Σ a, SamplerCoefficientSlot G B degree a)) degree
        (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
        A T m 1 (ε / 2)
      0 < t ∧ t ≤ 1 ∧ ((∀ j, σ j ≤ t) →
      ∀ block : ∀ a : {a // ¬grid a}, O a.val.1 → B a.val,
      (∀ a, Function.Injective (block a)) →
      ∀ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0),
      ∀ f : (realOutput → ℝ) → ℝ, Measurable f → (∀ v, ‖f v‖ ≤ 1) →
      |(∫ v, activeAveragedProfileIdeal (G := G) (B := B) (G × Option α) degree grid sets δ v *
          f (fun o => R o.1.val.1 * v o)) -
        ∫ v, allocatedContinuousLongJetProxy B U basis S x u rows s hA v * f v| ≤ ε) := by
  have hh (a : LayerSamplerAxis I n) : 0 < degree a := Nat.zero_lt_succ _
  have hdeg (a : LayerSamplerAxis I n) : degree a ≤ m := Nat.succ_le_of_lt a.1.isLt
  obtain ⟨δ, hδ, hδ1, hδeq, ht, ht1, hcomp⟩ := exists_active_tail_profile_comparison
    (W := Unit) (G := G) (Z := G × Option α) (B := B) (O := fun a => O a.1) (α := α)
    degree hh ψ hψ hrange hzero hone A T hLip hTransition hdeg hε
  refine ⟨δ, hδ, hδ1, hδeq, ht, ht1, ?_⟩
  intro hsmall block hblock s hA f hf hfb
  let t := booleanMassPerturbationScale (B := B) (O := fun a => O a.1) (α := α)
    ((G × Option α) ⊕ (Σ a, SamplerCoefficientSlot G B degree a)) degree
    (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
    A T m 1 (ε / 2)
  let τ : LayerSamplerAxis I n → ℝ := fun a => σ a.1 / t
  have hτ (a : LayerSamplerAxis I n) : |τ a| ≤ 1 := by
    dsimp only [τ]
    rw [abs_div, abs_of_pos (hσ a.1), abs_of_pos ht]
    exact (div_le_one ht).mpr (hsmall a.1)
  let z := fun _ : Unit => allocatedProfileFrozenNoise B U basis S x u
  have hbox : ∀ᵐ a ∂Measure.dirac (), ∀ j, |z a j| ≤ 1 :=
    Filter.Eventually.of_forall (fun _ => allocatedProfileFrozenNoise_abs_le B U basis S x u)
  have herr := hcomp grid (fun g a => (g, a)) sets (fun a => hrows a.val.1)
    (fun a => hcard a.val.1) block hblock τ hτ z (fun _ => measurable_const)
    t (by rw [abs_of_pos ht]) (Measure.dirac ()) inferInstance hbox (fun a => R a.1)
    (fun p => f p.2) (hf.comp measurable_snd) (fun p => hfb p.2)
  have heq (p : (Unit × (activeCoefficient → ℝ)) × (activeInput → ℝ)) :
      (activeTailProfileSample degree grid (fun g a => (g, a)) sets (fun a => R a.1) t τ z p).2 =
        allocatedNormalizedLongJetMap B U basis S x u rows p.2 p.1.2 :=
    allocatedTailProfileJet_eq B U basis S x u rows ht.ne' p.1.2 p.2
  simp only [heq] at herr
  have hD := activeAveragedProfileIdeal_measurable (G := G) (B := B) (G × Option α) degree grid sets δ
  have hscale : Measurable (fun v : realOutput → ℝ => fun o => R o.1.val.1 * v o) :=
    Measurable.of_eval (fun o => measurable_const.mul (measurable_pi_apply o))
  have hfirst := integral_dirac_first volume ()
    (fun p : Unit × (realOutput → ℝ) =>
      activeAveragedProfileIdeal (G := G) (B := B) (G × Option α) degree grid sets δ p.2 *
        f (fun o => R o.1.val.1 * p.2 o))
    ((hD.comp measurable_snd).mul (hf.comp (hscale.comp measurable_snd)))
  have hmap : Measurable (fun p : (Unit × (activeCoefficient → ℝ)) × (activeInput → ℝ) =>
      allocatedNormalizedLongJetMap B U basis S x u rows p.2 p.1.2) :=
    (allocatedNormalizedLongJetMap_measurable B U basis S x u rows).comp
      (f := fun p : (Unit × (activeCoefficient → ℝ)) × (activeInput → ℝ) => (p.2, p.1.2))
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  have hsecond := integral_dirac_first_nested (unitCoefficientSource activeCoefficient)
    (jointBooleanSource (fun a : {a // ¬grid a} => degree a.val)) ()
    (fun p : (Unit × (activeCoefficient → ℝ)) × (activeInput → ℝ) =>
      f (allocatedNormalizedLongJetMap B U basis S x u rows p.2 p.1.2)) (hf.comp hmap)
  rw [hfirst, hsecond] at herr
  have hσ1 : ∀ j, σ j ≤ 1 := fun j => (hsmall j).trans ht1
  rw [← allocatedContinuousLongJetProxy_test_integral B U basis hR hσ S x u rows s hA hσ1 f hf] at herr
  exact herr

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

theorem exists_allocated_continuous_proxy_averaging
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
      (δ : ℝ) = booleanRegularizationRadius (B := B) (O := (fun a : LayerSamplerAxis I n => O a.1)) (α := α) hLayer
        (unitProfilePrincipalSize (B := B)) (fun d => 2 * unitProfilePrincipalSize (B := B) d)
        A T (ε / 2) ∧
      let t := booleanMassPerturbationScale (B := B) (O := (fun a : LayerSamplerAxis I n => O a.1)) (α := α)
        ((G × Option α) ⊕ (Σ d, SamplerCoefficientSlot G B hLayer d)) hLayer
        (unitProfilePrincipalSize (B := B)) (fun d => 2 * unitProfilePrincipalSize (B := B) d)
        A T m 1 (ε / 2)
      0 < t ∧ t ≤ 1 ∧
      ∀ {J : Fin m → Type*} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        {R : Fin m → ℝ} (_hR : ∀ j, 0 < R j) {σ : ℝ} (_hσ : 0 < σ) (_hσt : σ ≤ t)
        (S : LayerSamplerScale (G := G) B U basis R (fun _ => σ))
        (x : G → IntegerScalarCubeBox α S.value)
        (rows : ∀ j, O j → Finset α)
        (_hrows : ∀ j, Function.Injective (rows j))
        (_hcard : ∀ j o, (rows j o).card ≤ j.val+1)
        (_block : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1 ↪ B a.val)
        (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
        {Ω : Type*} [Fintype Ω] (weights : FiniteProbabilityWeights Ω)
        (u : Ω → PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
          (allocatedPrincipalSides B U basis S))
        (f : Ω → ((Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1) → ℝ) → ℝ),
        (∀ a, Measurable (f a)) → (∀ a v, ‖f a v‖ ≤ 1) →
        |weights.mean (fun a => ∫ v,
            activeAveragedProfileIdeal (G := G) (B := B) (G × Option α) hLayer
              (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1) δ v *
              f a (fun o => R o.1.val.1 * v o)) -
          weights.mean (fun a => ∫ v,
            allocatedContinuousLongJetProxy B U basis S x (u a) rows s hA v * f a v)| ≤ ε := by
  obtain ⟨δ, hδ, hδ1, hδeq, ht, ht1, hpoint⟩ :=
    exists_allocated_continuous_proxy_comparison (G := G) (α := α) (O := O)
      B ψ hψ hrange hzero hone A T hLip hTransition hε
  refine ⟨δ, hδ, hδ1, hδeq, ht, ht1, ?_⟩
  intro J _ U basis R hR σ hσ hσt S x rows hrows hcard block s hA Ω _ weights u f hf hfb
  rw [← weights.mean_sub]
  exact (weights.abs_mean_le_mean_abs _).trans
    ((weights.mean_mono (fun a =>
      hpoint U basis hR hσ hσt S x (u a) rows hrows hcard block s hA (f a) (hf a) (hfb a))).trans_eq
      (weights.mean_const ε))

end Erdos3.VectorPolynomial

end

end OAI
