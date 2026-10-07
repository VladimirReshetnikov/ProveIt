/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Estimates.ActiveTailSlicedProfileComparison
import OAI.Combinatorics.Progressions.Estimates.AllocatedContinuousProxyAveraging

namespace OAI

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

variable (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α)
  (fun a => ¬allocatedGridAxis (I := I) U basis S.value a) → ℝ)

noncomputable def allocatedAffineLongJetDensity (y : activeInput → ℝ) : (realOutput → ℝ) → ℝ := by
  exact allocatedNormalizedLongJetDensity B U basis S x u rows s hA (fun i => center i + width i * y i)

noncomputable def allocatedAffineLongJetProxy : (realOutput → ℝ) → ℝ :=
  densityMixture (jointBooleanSource (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val))
    (allocatedAffineLongJetDensity B U basis S x u rows s hA center width)

include hR hσ in
theorem allocatedAffineLongJetDensity_measurable (hσ1 : ∀ j, σ j ≤ 1) :
    Measurable (Function.uncurry (allocatedAffineLongJetDensity B U basis S x u rows s hA center width)) := by
  have hin : Measurable (fun p : (activeInput → ℝ) × (realOutput → ℝ) =>
      ((fun i => center i + width i * p.1 i), p.2)) := by
    apply Measurable.prodMk
    · apply Measurable.of_eval
      intro i
      exact measurable_const.add (measurable_const.mul ((measurable_pi_apply i).comp measurable_fst))
    · exact measurable_snd
  exact (allocatedNormalizedLongJetDensity_measurable B U basis hR hσ S x u rows s hA hσ1).comp
    (f := fun p : (activeInput → ℝ) × (realOutput → ℝ) => ((fun i => center i + width i * p.1 i), p.2)) hin

include hR hσ in
theorem allocatedAffineLongJetDensity_probability (hσ1 : ∀ j, σ j ≤ 1) (y : activeInput → ℝ) :
    (∀ v, 0 ≤ allocatedAffineLongJetDensity B U basis S x u rows s hA center width y v) ∧
    Integrable (allocatedAffineLongJetDensity B U basis S x u rows s hA center width y) ∧
    (∫ v, allocatedAffineLongJetDensity B U basis S x u rows s hA center width y v) = 1 :=
  allocatedNormalizedLongJetDensity_probability B U basis hR hσ S x u rows s hA hσ1 _

omit [∀ j, DecidableEq (O j)] in
theorem allocatedAffineLongJetMap_measurable :
    Measurable (fun p : (activeInput → ℝ) × (activeCoefficient → ℝ) =>
      allocatedNormalizedLongJetMap B U basis S x u rows (fun i => center i + width i * p.1 i) p.2) := by
  have hin : Measurable (fun p : (activeInput → ℝ) × (activeCoefficient → ℝ) =>
      ((fun i => center i + width i * p.1 i), p.2)) := by
    apply Measurable.prodMk
    · apply Measurable.of_eval
      intro i
      exact measurable_const.add (measurable_const.mul ((measurable_pi_apply i).comp measurable_fst))
    · exact measurable_snd
  exact (allocatedNormalizedLongJetMap_measurable B U basis S x u rows).comp
    (f := fun p : (activeInput → ℝ) × (activeCoefficient → ℝ) => ((fun i => center i + width i * p.1 i), p.2)) hin

include hR hσ in
theorem allocatedAffineLongJetProxy_image_law (hσ1 : ∀ j, σ j ≤ 1) :
    ((jointBooleanSource (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val)).prod
      (unitCoefficientSource activeCoefficient)).map
      (fun p => allocatedNormalizedLongJetMap B U basis S x u rows
        (fun i => center i + width i * p.1 i) p.2) =
      realDensityMeasure volume (allocatedAffineLongJetProxy B U basis S x u rows s hA center width) := by
  exact densityMixture_image_law _ _ volume _
    (allocatedAffineLongJetMap_measurable B U basis S x u rows center width) _
    (allocatedAffineLongJetDensity_measurable B U basis hR hσ S x u rows s hA center width hσ1)
    (allocatedAffineLongJetDensity_probability B U basis hR hσ S x u rows s hA center width hσ1)
    (by
      intro y
      change (unitCoefficientSource activeCoefficient).map
        (allocatedNormalizedLongJetMap B U basis S x u rows
          (fun i => center i + width i * y i)) =
        realDensityMeasure volume (allocatedNormalizedLongJetDensity B U basis S x u rows s hA
          (fun i => center i + width i * y i))
      exact allocatedNormalizedLongJetDensity_unit_law B U basis hR hσ S x u rows s hA hσ1 _)

include hR hσ in
theorem allocatedAffineLongJetProxy_probability (hσ1 : ∀ j, σ j ≤ 1) :
    (∀ v, 0 ≤ allocatedAffineLongJetProxy B U basis S x u rows s hA center width v) ∧
    Integrable (allocatedAffineLongJetProxy B U basis S x u rows s hA center width) ∧
    (∫ v, allocatedAffineLongJetProxy B U basis S x u rows s hA center width v) = 1 :=
  densityMixture_probability_density _ _ _
    (allocatedAffineLongJetDensity_measurable B U basis hR hσ S x u rows s hA center width hσ1)
    (Filter.Eventually.of_forall
      (allocatedAffineLongJetDensity_probability B U basis hR hσ S x u rows s hA center width hσ1))

include hR hσ in
theorem allocatedAffineLongJetProxy_test_integral (hσ1 : ∀ j, σ j ≤ 1)
    (f : (realOutput → ℝ) → ℝ) (hf : Measurable f) :
    (∫ v, allocatedAffineLongJetProxy B U basis S x u rows s hA center width v * f v) =
      ∫ p : (activeCoefficient → ℝ) × (activeInput → ℝ),
        f (allocatedNormalizedLongJetMap B U basis S x u rows (fun i => center i + width i * p.2 i) p.1)
        ∂(unitCoefficientSource activeCoefficient).prod
          (jointBooleanSource (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val)) := by
  have hm := allocatedAffineLongJetMap_measurable B U basis S x u rows center width
  have hd : Measurable (allocatedAffineLongJetProxy B U basis S x u rows s hA center width) :=
    (allocatedAffineLongJetDensity_measurable B U basis hR hσ S x u rows s hA center width hσ1).stronglyMeasurable.integral_prod_left'.measurable
  have hp := allocatedAffineLongJetProxy_probability B U basis hR hσ S x u rows s hA center width hσ1
  have ht := mappedTest_eq_density
    ((jointBooleanSource (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val)).prod
      (unitCoefficientSource activeCoefficient)) volume
    (fun p => allocatedNormalizedLongJetMap B U basis S x u rows (fun i => center i + width i * p.1 i) p.2) hm
    (allocatedAffineLongJetProxy B U basis S x u rows s hA center width) hd hp.1
    (allocatedAffineLongJetProxy_image_law B U basis hR hσ S x u rows s hA center width hσ1) f hf
  change (∫ p, f (allocatedNormalizedLongJetMap B U basis S x u rows (fun i => center i + width i * p.1 i) p.2)
    ∂(jointBooleanSource (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val)).prod
      (unitCoefficientSource activeCoefficient)) = _ at ht
  exact ht.symm.trans (integral_prod_swap
    (fun p : (activeInput → ℝ) × (activeCoefficient → ℝ) =>
      f (allocatedNormalizedLongJetMap B U basis S x u rows (fun i => center i + width i * p.1 i) p.2))).symm

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

include hσ hrows hcard in
omit [∀ j, DecidableEq (O j)] in
theorem exists_allocated_affine_tail_test_comparison
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (block : ∀ a : {a // ¬grid a}, O a.val.1 → B a.val)
    (hblock : ∀ a, Function.Injective (block a))
    {δ ε : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hε : 0 < ε) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧ ρ ≤ 1 ∧ ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      ((∀ j, σ j ≤ t) →
      ∀ (x : G → IntegerScalarCubeBox α S.value)
        (u : PrincipalAxisTuples (α := α) grid (allocatedPrincipalSides B U basis S))
        (center width : activeInput → ℝ),
      (∀ i, δ ≤ |width i|) → (∀ i, |center i| + |width i| ≤ 1) →
      ∀ f : (realOutput → ℝ) → ℝ, Measurable f → (∀ v, ‖f v‖ ≤ 1) →
      |(∫ v, activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
          degree grid sets ρ center width v * f (fun o => R o.1.val.1 * v o)) -
        ∫ p, f (allocatedNormalizedLongJetMap B U basis S x u rows
          (fun i => center i + width i * p.2 i) p.1)
          ∂(unitCoefficientSource activeCoefficient).prod
            (jointBooleanSource (B := fun a : {a // ¬grid a} => B a.val) (α := α) (fun a => degree a.val))| ≤ ε) := by
  have hh (a : LayerSamplerAxis I n) : 0 < degree a := Nat.zero_lt_succ _
  have hdeg (a : LayerSamplerAxis I n) : degree a ≤ m := Nat.succ_le_of_lt a.1.isLt
  obtain ⟨ρ, hρ, hρone, t, ht, htone, hcomp⟩ := exists_active_tail_sliced_profile_comparison
    (W := Unit) (G := G) (Z := G × Option α) degree hh grid (fun g a => (g, a)) sets (fun a => hrows a.val.1)
    (fun a => hcard a.val.1) block hblock ψ hψ hrange hzero hone A T hLip hTransition hdeg hδ hδone hε
  refine ⟨ρ, hρ, hρone, t, ht, htone, ?_⟩
  intro hsmall x u center width hwidth hcenter f hf hfb
  let τ : LayerSamplerAxis I n → ℝ := fun a => σ a.1 / t
  have hτ (a : LayerSamplerAxis I n) : |τ a| ≤ 1 := by
    dsimp only [τ]
    rw [abs_div, abs_of_pos (hσ a.1), abs_of_pos ht]
    exact (div_le_one ht).mpr (hsmall a.1)
  let z := fun _ : Unit => allocatedProfileFrozenNoise B U basis S x u
  have hbox : ∀ᵐ a ∂Measure.dirac (), ∀ j, |z a j| ≤ 1 :=
    Filter.Eventually.of_forall (fun _ => allocatedProfileFrozenNoise_abs_le B U basis S x u)
  have herr := hcomp τ hτ z (fun _ => measurable_const) center width hwidth hcenter
    (Measure.dirac ()) inferInstance hbox (fun a => R a.1)
    (fun p => f p.2) (hf.comp measurable_snd) (fun p => hfb p.2)
  have heq (p : (Unit × (activeCoefficient → ℝ)) × (activeInput → ℝ)) :
      partitionedAllocatedProfileJet degree grid (fun g a => (g, a)) sets (fun a => R a.1) t
        (profileNoiseWithActive degree grid (z p.1.1) (activeTailRescale degree grid τ p.1.2))
        (fun i => center i + width i * p.2 i) =
      allocatedNormalizedLongJetMap B U basis S x u rows
        (fun i => center i + width i * p.2 i) p.1.2 :=
    allocatedTailProfileJet_eq B U basis S x u rows ht.ne' p.1.2 _
  simp only [heq] at herr
  have hD : Measurable (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
      degree grid sets ρ center width) :=
    (activeAveragedSlicedProfileIdeal_spec (G × Option α) degree grid sets ρ hρ center width).2.1.continuous.measurable
  have hscale : Measurable (fun v : realOutput → ℝ => fun o => R o.1.val.1 * v o) :=
    Measurable.of_eval (fun o => measurable_const.mul (measurable_pi_apply o))
  have hfirst := integral_dirac_first volume ()
    (fun p : Unit × (realOutput → ℝ) =>
      activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α) degree grid sets ρ center width p.2 *
        f (fun o => R o.1.val.1 * p.2 o))
    ((hD.comp measurable_snd).mul (hf.comp (hscale.comp measurable_snd)))
  have hin : Measurable (fun p : (Unit × (activeCoefficient → ℝ)) × (activeInput → ℝ) =>
      ((fun i => center i + width i * p.2 i), p.1.2)) := by
    apply Measurable.prodMk
    · apply Measurable.of_eval
      intro i
      exact measurable_const.add (measurable_const.mul ((measurable_pi_apply i).comp measurable_snd))
    · exact measurable_snd.comp measurable_fst
  have hmap : Measurable (fun p : (Unit × (activeCoefficient → ℝ)) × (activeInput → ℝ) =>
      allocatedNormalizedLongJetMap B U basis S x u rows
        (fun i => center i + width i * p.2 i) p.1.2) :=
    (allocatedNormalizedLongJetMap_measurable B U basis S x u rows).comp
      (f := fun p : (Unit × (activeCoefficient → ℝ)) × (activeInput → ℝ) =>
        ((fun i => center i + width i * p.2 i), p.1.2)) hin
  have hsecond := integral_dirac_first_nested (unitCoefficientSource activeCoefficient)
    (jointBooleanSource (B := fun a : {a // ¬grid a} => B a.val) (α := α) (fun a => degree a.val)) ()
    (fun p : (Unit × (activeCoefficient → ℝ)) × (activeInput → ℝ) =>
      f (allocatedNormalizedLongJetMap B U basis S x u rows
        (fun i => center i + width i * p.2 i) p.1.2)) (hf.comp hmap)
  rw [hfirst, hsecond] at herr
  exact herr

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
theorem exists_allocated_affine_proxy_comparison
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (block : ∀ a : {a // ¬grid a}, O a.val.1 → B a.val)
    (hblock : ∀ a, Function.Injective (block a))
    {δ ε : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hε : 0 < ε) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧ ρ ≤ 1 ∧ ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      ((∀ j, σ j ≤ t) →
      ∀ (x : G → IntegerScalarCubeBox α S.value)
        (u : PrincipalAxisTuples (α := α) grid (allocatedPrincipalSides B U basis S))
        (center width : activeInput → ℝ),
      (∀ i, δ ≤ |width i|) → (∀ i, |center i| + |width i| ≤ 1) →
      ∀ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0),
      ∀ f : (realOutput → ℝ) → ℝ, Measurable f → (∀ v, ‖f v‖ ≤ 1) →
      |(∫ v, activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
          degree grid sets ρ center width v * f (fun o => R o.1.val.1 * v o)) -
        ∫ v, allocatedAffineLongJetProxy B U basis S x u rows s hA center width v * f v| ≤ ε) := by
  obtain ⟨ρ, hρ, hρone, t, ht, htone, hs⟩ := exists_allocated_affine_tail_test_comparison
    B U basis hσ S rows hrows hcard ψ hψ hrange hzero hone A T hLip hTransition
    block hblock hδ hδone hε
  refine ⟨ρ, hρ, hρone, t, ht, htone, ?_⟩
  intro hsmall x u center width hwidth hcenter s hA f hf hfb
  have he := hs hsmall x u center width hwidth hcenter f hf hfb
  rw [← allocatedAffineLongJetProxy_test_integral B U basis hR hσ S x u rows s hA
    center width (fun j => (hsmall j).trans htone) f hf] at he
  exact he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

noncomputable def allocatedAffineSourceTolerance (A T : ℝ≥0) (δ ε : ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun P : LayerSamplerAxis I n → Prop =>
    partitionedAffineSourceTolerance (G := G) (Z := G × Option α) (B := B)
      (O := fun a : {a // ¬P a} => O a.val.1) (α := α) (layerSamplerDegree I n) P A T m δ ε)

include hrows hcard in
theorem exists_early_allocated_affine_tail_test_comparison_with_scales
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (block : ∀ a : LayerSamplerAxis I n, O a.1 → B a)
    (hblock : ∀ a, Function.Injective (block a))
    {δ ε : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hε : 0 < ε) :
    ∃ ρmin : ℝ≥0, 0 < ρmin ∧ ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
      (∀ P, ρmin ≤ ρ P ∧ ρ P ≤ 1) ∧
      (∀ P, (ρ P : ℝ) = partitionedAffineSourceRadius (B := B)
        (O := fun a : {a // ¬P a} => O a.val.1) (α := α) (layerSamplerDegree I n) P A T δ ε) ∧
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      t = allocatedAffineSourceTolerance (G := G) (O := O) (α := α) B A T δ ε ∧
      ∀ {J : Fin m → Type*} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        {R σ : Fin m → ℝ} (_hσ : ∀ j, 0 < σ j)
        (S : LayerSamplerScale (G := G) B U basis R σ),
      (∀ j, σ j ≤ t) →
      ∀ (x : G → IntegerScalarCubeBox α S.value)
        (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))
        (center width : (PrincipalAxisParameter (B := B) (h := (layerSamplerDegree I n)) (α := α) (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a)) → ℝ),
      (∀ i, δ ≤ |width i|) → (∀ i, |center i| + |width i| ≤ 1) →
      ∀ f : ((Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O (Sigma.fst (Subtype.val a))) → ℝ) → ℝ, Measurable f → (∀ v, ‖f v‖ ≤ 1) →
      |(∫ v, activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
          (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => rows (Sigma.fst (Subtype.val a))) (ρ (allocatedGridAxis (I := I) U basis S.value)) center width v * f (fun o => R o.1.val.1 * v o)) -
        ∫ p, f (allocatedNormalizedLongJetMap B U basis S x u rows
          (fun i => center i + width i * p.2 i) p.1)
          ∂(unitCoefficientSource (ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value))).prod
            (jointBooleanSource (B := fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (α := α) (fun a => (layerSamplerDegree I n) a.val))| ≤ ε := by
  have hh (a : LayerSamplerAxis I n) : 0 < (layerSamplerDegree I n) a := Nat.zero_lt_succ _
  have hdeg (a : LayerSamplerAxis I n) : (layerSamplerDegree I n) a ≤ m := Nat.succ_le_of_lt a.1.isLt
  have hall (P : LayerSamplerAxis I n → Prop) := exists_active_tail_sliced_profile_comparison_with_scales
    (W := Unit) (G := G) (Z := G × Option α) (layerSamplerDegree I n) hh P (fun g a => (g, a))
    (fun a : {a // ¬P a} => rows a.val.1) (fun a => hrows a.val.1)
    (fun a => hcard a.val.1) (fun a => block a.val) (fun a => hblock a.val)
    ψ hψ hrange hzero hone A T hLip hTransition hdeg hδ hδone hε
  choose ρ hρ hρone hρeq tp htp htpone htpeq hcomp using hall
  let t := Finset.univ.inf' Finset.univ_nonempty tp
  have ht : 0 < t := (Finset.lt_inf'_iff _).mpr (fun P _ => htp P)
  have htP (P) : t ≤ tp P := Finset.inf'_le _ (Finset.mem_univ P)
  let ρmin := Finset.univ.inf' Finset.univ_nonempty ρ
  have hρmin : 0 < ρmin := (Finset.lt_inf'_iff _).mpr (fun P _ => hρ P)
  refine ⟨ρmin, hρmin, ρ, (fun P => ⟨Finset.inf'_le _ (Finset.mem_univ P), hρone P⟩),
    hρeq, t, ht, (htP (fun _ => False)).trans (htpone _), ?_, ?_⟩
  · change Finset.univ.inf' Finset.univ_nonempty tp = _
    simp only [htpeq]
    rfl
  intro J _ U basis R σ hσ S hsmall x u center width hwidth hcenter f hf hfb
  let τ : LayerSamplerAxis I n → ℝ := fun a => σ a.1 / tp (allocatedGridAxis (I := I) U basis S.value)
  have hτ (a : LayerSamplerAxis I n) : |τ a| ≤ 1 := by
    dsimp only [τ]
    rw [abs_div, abs_of_pos (hσ a.1), abs_of_pos (htp (allocatedGridAxis (I := I) U basis S.value))]
    exact (div_le_one (htp (allocatedGridAxis (I := I) U basis S.value))).mpr ((hsmall a.1).trans (htP (allocatedGridAxis (I := I) U basis S.value)))
  let z := fun _ : Unit => allocatedProfileFrozenNoise B U basis S x u
  have hbox : ∀ᵐ a ∂Measure.dirac (), ∀ j, |z a j| ≤ 1 :=
    Filter.Eventually.of_forall (fun _ => allocatedProfileFrozenNoise_abs_le B U basis S x u)
  have herr := hcomp (allocatedGridAxis (I := I) U basis S.value) τ hτ z (fun _ => measurable_const) center width hwidth hcenter
    (Measure.dirac ()) inferInstance hbox (fun a => R a.1)
    (fun p => f p.2) (hf.comp measurable_snd) (fun p => hfb p.2)
  have heq (p : (Unit × ((ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value)) → ℝ)) × ((PrincipalAxisParameter (B := B) (h := (layerSamplerDegree I n)) (α := α) (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a)) → ℝ)) :
      partitionedAllocatedProfileJet (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value) (fun g a => (g, a)) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => rows (Sigma.fst (Subtype.val a))) (fun a => R a.1) (tp (allocatedGridAxis (I := I) U basis S.value))
        (profileNoiseWithActive (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value) (z p.1.1) (activeTailRescale (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value) τ p.1.2))
        (fun i => center i + width i * p.2 i) =
      allocatedNormalizedLongJetMap B U basis S x u rows
        (fun i => center i + width i * p.2 i) p.1.2 :=
    allocatedTailProfileJet_eq B U basis S x u rows (htp (allocatedGridAxis (I := I) U basis S.value)).ne' p.1.2 _
  simp only [heq] at herr
  have hD : Measurable (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
      (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => rows (Sigma.fst (Subtype.val a))) (ρ (allocatedGridAxis (I := I) U basis S.value)) center width) :=
    (activeAveragedSlicedProfileIdeal_spec (G × Option α) (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => rows (Sigma.fst (Subtype.val a))) (ρ (allocatedGridAxis (I := I) U basis S.value)) (hρ (allocatedGridAxis (I := I) U basis S.value)) center width).2.1.continuous.measurable
  have hscale : Measurable (fun v : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O (Sigma.fst (Subtype.val a))) → ℝ => fun o => R o.1.val.1 * v o) :=
    Measurable.of_eval (fun o => measurable_const.mul (measurable_pi_apply o))
  have hfirst := integral_dirac_first volume ()
    (fun p : Unit × ((Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O (Sigma.fst (Subtype.val a))) → ℝ) =>
      activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α) (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => rows (Sigma.fst (Subtype.val a))) (ρ (allocatedGridAxis (I := I) U basis S.value)) center width p.2 *
        f (fun o => R o.1.val.1 * p.2 o))
    ((hD.comp measurable_snd).mul (hf.comp (hscale.comp measurable_snd)))
  have hin : Measurable (fun p : (Unit × ((ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value)) → ℝ)) × ((PrincipalAxisParameter (B := B) (h := (layerSamplerDegree I n)) (α := α) (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a)) → ℝ) =>
      ((fun i => center i + width i * p.2 i), p.1.2)) := by
    apply Measurable.prodMk
    · apply Measurable.of_eval
      intro i
      exact measurable_const.add (measurable_const.mul ((measurable_pi_apply i).comp measurable_snd))
    · exact measurable_snd.comp measurable_fst
  have hmap : Measurable (fun p : (Unit × ((ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value)) → ℝ)) × ((PrincipalAxisParameter (B := B) (h := (layerSamplerDegree I n)) (α := α) (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a)) → ℝ) =>
      allocatedNormalizedLongJetMap B U basis S x u rows
        (fun i => center i + width i * p.2 i) p.1.2) :=
    (allocatedNormalizedLongJetMap_measurable B U basis S x u rows).comp
      (f := fun p : (Unit × ((ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value)) → ℝ)) × ((PrincipalAxisParameter (B := B) (h := (layerSamplerDegree I n)) (α := α) (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a)) → ℝ) =>
        ((fun i => center i + width i * p.2 i), p.1.2)) hin
  have hsecond := integral_dirac_first_nested (unitCoefficientSource (ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value)))
    (jointBooleanSource (B := fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (α := α) (fun a => (layerSamplerDegree I n) a.val)) ()
    (fun p : (Unit × ((ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value)) → ℝ)) × ((PrincipalAxisParameter (B := B) (h := (layerSamplerDegree I n)) (α := α) (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a)) → ℝ) =>
      f (allocatedNormalizedLongJetMap B U basis S x u rows
        (fun i => center i + width i * p.2 i) p.1.2)) (hf.comp hmap)
  rw [hfirst, hsecond] at herr
  exact herr

include hrows hcard in
theorem exists_early_allocated_affine_tail_test_comparison
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (block : ∀ a : LayerSamplerAxis I n, O a.1 → B a)
    (hblock : ∀ a, Function.Injective (block a))
    {δ ε : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hε : 0 < ε) :
    ∃ ρmin : ℝ≥0, 0 < ρmin ∧ ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
      (∀ P, ρmin ≤ ρ P ∧ ρ P ≤ 1) ∧ ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      ∀ {J : Fin m → Type*} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        {R σ : Fin m → ℝ} (_hσ : ∀ j, 0 < σ j)
        (S : LayerSamplerScale (G := G) B U basis R σ),
      (∀ j, σ j ≤ t) →
      ∀ (x : G → IntegerScalarCubeBox α S.value)
        (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))
        (center width : (PrincipalAxisParameter (B := B) (h := (layerSamplerDegree I n)) (α := α) (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a)) → ℝ),
      (∀ i, δ ≤ |width i|) → (∀ i, |center i| + |width i| ≤ 1) →
      ∀ f : ((Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O (Sigma.fst (Subtype.val a))) → ℝ) → ℝ, Measurable f → (∀ v, ‖f v‖ ≤ 1) →
      |(∫ v, activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
          (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => rows (Sigma.fst (Subtype.val a))) (ρ (allocatedGridAxis (I := I) U basis S.value)) center width v * f (fun o => R o.1.val.1 * v o)) -
        ∫ p, f (allocatedNormalizedLongJetMap B U basis S x u rows
          (fun i => center i + width i * p.2 i) p.1)
          ∂(unitCoefficientSource (ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value))).prod
            (jointBooleanSource (B := fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (α := α) (fun a => (layerSamplerDegree I n) a.val))| ≤ ε := by
  obtain ⟨ρmin, hρmin, ρ, hρ, _, t, ht, htone, _, hs⟩ :=
    exists_early_allocated_affine_tail_test_comparison_with_scales (G := G) B rows hrows hcard
      ψ hψ hrange hzero hone A T hLip hTransition block hblock hδ hδone hε
  exact ⟨ρmin, hρmin, ρ, hρ, t, ht, htone, hs⟩

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
theorem exists_allocated_affine_proxy_l1
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (block : ∀ a : {a // ¬grid a}, O a.val.1 → B a.val)
    (hblock : ∀ a, Function.Injective (block a))
    {δ ε : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hε : 0 < ε) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧ ρ ≤ 1 ∧ ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      ((∀ j, σ j ≤ t) →
      ∀ (x : G → IntegerScalarCubeBox α S.value)
        (u : PrincipalAxisTuples (α := α) grid (allocatedPrincipalSides B U basis S))
        (center width : activeInput → ℝ),
      (∀ i, δ ≤ |width i|) → (∀ i, |center i| + |width i| ≤ 1) →
      ∀ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0),
      (∫ v, |diagonalImageDensity (fun o : realOutput => R o.1.val.1)
          (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
            degree grid sets ρ center width) v -
        allocatedAffineLongJetProxy B U basis S x u rows s hA center width v|) ≤ ε) := by
  obtain ⟨ρ, hρ, hρone, t, ht, htone, hs⟩ := exists_allocated_affine_proxy_comparison
    B U basis hR hσ S rows hrows hcard ψ hψ hrange hzero hone A T hLip hTransition
    block hblock hδ hδone hε
  refine ⟨ρ, hρ, hρone, t, ht, htone, ?_⟩
  intro hsmall x u center width hwidth hcenter s hA
  have hσ1 : ∀ j, σ j ≤ 1 := fun j => (hsmall j).trans htone
  have hi := activeAveragedSlicedProfileIdeal_spec (G := G) (B := B)
    (G × Option α) degree grid sets ρ hρ center width
  have hp := allocatedAffineLongJetProxy_probability B U basis hR hσ S x u rows s hA
    center width hσ1
  have hm : Measurable (allocatedAffineLongJetProxy B U basis S x u rows s hA center width) :=
    (allocatedAffineLongJetDensity_measurable B U basis hR hσ S x u rows s hA
      center width hσ1).stronglyMeasurable.integral_prod_left'.measurable
  exact diagonalImageDensity_l1_le_of_tests (fun o : realOutput => R o.1.val.1)
    (fun o => (hR o.1.val.1).ne') _ _ hi.2.1.continuous.measurable hm hi.2.2.1 hp.2.1
    (hs hsmall x u center width hwidth hcenter s hA)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped NNReal BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
  {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  {α : Type*} [Fintype α] [DecidableEq α]
  {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)]

noncomputable def allocatedAffinePartitionLog (A T : ℝ≥0) (E F : ℝ)
    (P : LayerSamplerAxis I n → Prop) : ℝ :=
  let Clog := unitProfileCoefficientLog (B := B) A T
  let Elog := E + Fintype.card {a // ¬P a} + 4
  let Qlog := jointAffineSourceInputLog (B := fun a : {a // ¬P a} => B a.val)
    (O := fun a : {a // ¬P a} => O a.val.1) (α := α)
    (fun a => layerSamplerDegree I n a.val) Clog Elog F
  Real.log 16 + 6 * Qlog +
    booleanToleranceC2Log (B := fun a : {a // ¬P a} => B a.val) (α := α)
      (PartitionedProfileNoiseIndex G (G × Option α) α B (layerSamplerDegree I n) P)
      (fun a => layerSamplerDegree I n a.val) m Clog + 1

noncomputable def allocatedAffineToleranceLog (A T : ℝ≥0) (E F : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (allocatedAffinePartitionLog (G := G) (O := O) (α := α) B A T E F)

 theorem allocatedAffineSourceTolerance_log_bound (A T : ℝ≥0) {δ ε E F : ℝ}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hε : 0 < ε) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hεE : ε⁻¹ ≤ Real.exp E) (hδF : δ⁻¹ ≤ Real.exp F) :
    Real.log (allocatedAffineSourceTolerance (G := G) (O := O) (α := α) B A T δ ε)⁻¹ ≤
      allocatedAffineToleranceLog (G := G) (O := O) (α := α) B A T E F := by
  let t := fun P : LayerSamplerAxis I n → Prop =>
    partitionedAffineSourceTolerance (G := G) (Z := G × Option α) (B := B)
      (O := fun a : {a // ¬P a} => O a.val.1) (α := α) (layerSamplerDegree I n) P A T m δ ε
  obtain ⟨P, hP, heq⟩ := Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset (LayerSamplerAxis I n → Prop)))
    Finset.univ_nonempty t
  change Real.log (Finset.univ.inf' Finset.univ_nonempty t)⁻¹ ≤ _
  rw [heq]
  have hb := (partitionedAffineSource_scales_log_bounds (G := G) (Z := G × Option α)
    (B := B) (O := fun a : {a // ¬P a} => O a.val.1) (α := α) (layerSamplerDegree I n) P
    (fun _ => Nat.zero_lt_succ _) A T m hδ hδone hε hE hF hεE hδF).2
  exact hb.trans (Finset.le_sup' (allocatedAffinePartitionLog (G := G) (O := O) (α := α) B A T E F) hP)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped NNReal BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
  {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  {α : Type*} [Fintype α] [DecidableEq α]
  {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)]

noncomputable def allocatedAffinePartitionRadiusLog (A T : ℝ≥0) (E F : ℝ)
    (P : LayerSamplerAxis I n → Prop) : ℝ :=
  2 * jointAffineSourceInputLog (B := fun a : {a // ¬P a} => B a.val)
    (O := fun a : {a // ¬P a} => O a.val.1) (α := α)
    (fun a => layerSamplerDegree I n a.val) (unitProfileCoefficientLog (B := B) A T)
    (E + Fintype.card {a // ¬P a} + 4) F + 2

noncomputable def allocatedAffineRadiusLog (A T : ℝ≥0) (E F : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (allocatedAffinePartitionRadiusLog (O := O) (α := α) B A T E F)

 theorem allocatedAffineSourceRadius_inverse_bound (A T : ℝ≥0) {δ ε E F : ℝ}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hε : 0 < ε) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hεE : ε⁻¹ ≤ Real.exp E) (hδF : δ⁻¹ ≤ Real.exp F)
    (P : LayerSamplerAxis I n → Prop) :
    (partitionedAffineSourceRadius (B := B) (O := fun a : {a // ¬P a} => O a.val.1)
      (α := α) (layerSamplerDegree I n) P A T δ ε)⁻¹ ≤
        Real.exp (allocatedAffineRadiusLog (O := O) (α := α) B A T E F) := by
  have h := (partitionedAffineSource_scales_log_bounds (G := Unit) (Z := Unit)
    (B := B) (O := fun a : {a // ¬P a} => O a.val.1) (α := α) (layerSamplerDegree I n) P
    (fun _ => Nat.zero_lt_succ _) A T m hδ hδone hε hE hF hεE hδF).1
  apply h.trans
  apply Real.exp_le_exp.mpr
  exact Finset.le_sup' (allocatedAffinePartitionRadiusLog (O := O) (α := α) B A T E F)
    (Finset.mem_univ P)

 theorem allocatedAffineSourceRadius_uniform_floor (A T : ℝ≥0) {δ ε E F : ℝ}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hε : 0 < ε) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hεE : ε⁻¹ ≤ Real.exp E) (hδF : δ⁻¹ ≤ Real.exp F)
    (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0)
    (hρ : ∀ P, 0 < ρ P)
    (hρeq : ∀ P, (ρ P : ℝ) = partitionedAffineSourceRadius (B := B)
      (O := fun a : {a // ¬P a} => O a.val.1) (α := α) (layerSamplerDegree I n) P A T δ ε) :
    ∀ P, Real.exp (-allocatedAffineRadiusLog (O := O) (α := α) B A T E F) ≤ ρ P := by
  intro P
  have hi := allocatedAffineSourceRadius_inverse_bound (O := O) (α := α)
    B A T hδ hδone hε hE hF hεE hδF P
  rw [← hρeq P] at hi
  rw [Real.exp_neg]
  exact (inv_le_comm₀ (Real.exp_pos _) (show 0 < (ρ P : ℝ) from hρ P)).mpr hi

end Erdos3.VectorPolynomial

end

end OAI
