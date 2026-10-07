import OAI.Combinatorics.Progressions.Estimates.OneCubePrincipalSliceRiemann
import OAI.Combinatorics.Progressions.Geometry.AllocatedProxyOutputSupport
import OAI.Combinatorics.Progressions.Lattices.AllocatedAffineRadiusLog

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

include hrows hcard in
theorem exists_early_allocated_affine_proxy_l1_with_scales
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
        {R σ : Fin m → ℝ} (_hR : ∀ j, 0 < R j) (_hσ : ∀ j, 0 < σ j)
        (S : LayerSamplerScale (G := G) B U basis R σ),
      (∀ j, σ j ≤ t) →
      ∀ (x : G → IntegerScalarCubeBox α S.value)
        (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))
        (center width : (PrincipalAxisParameter (B := B) (h := (layerSamplerDegree I n)) (α := α) (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a)) → ℝ),
      (∀ i, δ ≤ |width i|) → (∀ i, |center i| + |width i| ≤ 1) →
      ∀ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0),
      (∫ v, |diagonalImageDensity
          (fun o : (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1) => R o.1.val.1)
          (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
            (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value)
            (fun a => rows a.val.1) (ρ (allocatedGridAxis (I := I) U basis S.value)) center width) v -
        allocatedAffineLongJetProxy B U basis S x u rows s hA center width v|) ≤ ε := by
  obtain ⟨ρmin, hρmin, ρ, hρ, hρeq, t, ht, htone, hteq, hs⟩ :=
    exists_early_allocated_affine_tail_test_comparison_with_scales (G := G) B rows hrows hcard
      ψ hψ hrange hzero hone A T hLip hTransition block hblock hδ hδone hε
  refine ⟨ρmin, hρmin, ρ, hρ, hρeq, t, ht, htone, hteq, ?_⟩
  intro J _ U basis R σ hR hσ S hsmall x u center width hwidth hcenter s hA
  let P := allocatedGridAxis (I := I) U basis S.value
  have hρpos : 0 < ρ P := hρmin.trans_le (hρ P).1
  have hσ1 : ∀ j, σ j ≤ 1 := fun j => (hsmall j).trans htone
  have hi := activeAveragedSlicedProfileIdeal_spec (G := G) (B := B)
    (G × Option α) (layerSamplerDegree I n) P (fun a => rows a.val.1) (ρ P) hρpos center width
  have hp := allocatedAffineLongJetProxy_probability B U basis hR hσ S x u rows s hA
    center width hσ1
  have hm : Measurable (allocatedAffineLongJetProxy B U basis S x u rows s hA center width) :=
    (allocatedAffineLongJetDensity_measurable B U basis hR hσ S x u rows s hA
      center width hσ1).stronglyMeasurable.integral_prod_left'.measurable
  apply diagonalImageDensity_l1_le_of_tests _ (fun o => (hR o.1.val.1).ne') _ _
    hi.2.1.continuous.measurable hm hi.2.2.1 hp.2.1
  intro f hf hfb
  rw [allocatedAffineLongJetProxy_test_integral B U basis hR hσ S x u rows s hA center width hσ1 f hf]
  exact hs U basis hσ S hsmall x u center width hwidth hcenter f hf hfb

include hrows hcard in
theorem exists_early_allocated_affine_proxy_l1
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
        {R σ : Fin m → ℝ} (_hR : ∀ j, 0 < R j) (_hσ : ∀ j, 0 < σ j)
        (S : LayerSamplerScale (G := G) B U basis R σ),
      (∀ j, σ j ≤ t) →
      ∀ (x : G → IntegerScalarCubeBox α S.value)
        (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))
        (center width : (PrincipalAxisParameter (B := B) (h := (layerSamplerDegree I n)) (α := α) (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a)) → ℝ),
      (∀ i, δ ≤ |width i|) → (∀ i, |center i| + |width i| ≤ 1) →
      ∀ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0),
      (∫ v, |diagonalImageDensity
          (fun o : (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1) => R o.1.val.1)
          (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
            (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value)
            (fun a => rows a.val.1) (ρ (allocatedGridAxis (I := I) U basis S.value)) center width) v -
        allocatedAffineLongJetProxy B U basis S x u rows s hA center width v|) ≤ ε := by
  obtain ⟨ρmin, hρmin, ρ, hρ, _, t, ht, htone, _, hs⟩ :=
    exists_early_allocated_affine_proxy_l1_with_scales (G := G) B rows hrows hcard
      ψ hψ hrange hzero hone A T hLip hTransition block hblock hδ hδone hε
  exact ⟨ρmin, hρmin, ρ, hρ, t, ht, htone, hs⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
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
variable (s : ∀ j : Fin m, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := O j)
  S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (Mk : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "Jet" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "bound" => NNReal.mk
  (Real.exp (allocatedDensityLog (G := G) B α O P)) (Real.exp_nonneg _)
local notation "cap" => bound ^ Fintype.card (LayerSamplerAxis I n)
local notation "lip" => (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound * cap

include hR hσ hMk hi hP hMkP hRP hRi hσi hcount in
theorem allocatedAffineLongJetProxy_residue_error (hσ1 : ∀ j, σ j ≤ 1)
    (L step H M : Tuple → ℕ) (c : Tuple → ℤ)
    (hL : ∀ j, 0 < L j) (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
    (hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (modulus : Tuple → Option α → ℕ) (residue : ∀ j i, ZMod (modulus j i))
    (hm : ∀ j i, 0 < modulus j i) (hmM : ∀ j i, modulus j i ≤ M j)
    (hsize : ∀ j, (Fintype.card α + 1) * M j ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((M j : ℝ) / H j) <
      volume.real (scalarCubeDomain α))
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / L j ≤ ε) (z : Jet → ℝ) :
    |(FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α (H j) (M j)
        (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j) (hsize j))).mean
        (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA
          (principalTupleFlatten (fun a : {a // ¬grid a} => B a.val) (fun a => degree a.val) α
            (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / L j)) z) -
      allocatedAffineLongJetProxy B U basis S x u rows s hA
        (principalProgressionSliceCenter (α := α) (fun a : {a // ¬grid a} => B a.val)
          (fun a => degree a.val) L c)
        (principalProgressionSliceWidth (α := α) (fun a : {a // ¬grid a} => B a.val)
          (fun a => degree a.val) L H step) z| ≤
      (2 * (cap : ℝ) * scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) +
        (lip : ℝ) * 2) * ∑ j, (M j : ℝ) / H j + (lip : ℝ) * ε := by
  have hb := allocatedNormalizedLongJetDensity_parameter_bounds B U basis hR hσ S x
    rows s hA hMk hi hP hMkP hRP hRi hσi hcount u hσ1 z
  exact principalProgressionSlice_residue_riemann
    (fun a : {a // ¬grid a} => B a.val) (fun a => degree a.val)
    L step H M c hL hstep hH hδ hsubset hdense modulus residue hm hmM hsize hsmall hε hmesh
    (fun y => allocatedNormalizedLongJetDensity B U basis S x u rows s hA y z)
    hb.2 (NNReal.coe_nonneg cap) (fun y _ => hb.1 y)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [dG : DecidableEq G]
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
local notation "radius" => Real.exp (allocatedJetSupportLog (G := G) B α O P)
local notation "input" => PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := α) (fun a => ¬grid a)
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

include hR hσ hM hi hP hMP hRP hRi hσi hcount

theorem allocatedAffineLongJetProxy_output_bounds (hσ1 : ∀ j, σ j ≤ 1)
    (center width : input → ℝ) :
    let bound : ℝ≥0 := ⟨Real.exp (allocatedDensityLog (G := G) B α O P), Real.exp_nonneg _⟩
    let cap := bound ^ Fintype.card (LayerSamplerAxis I n)
    let lip := (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound * cap
    (∀ z, allocatedAffineLongJetProxy B U basis S x u rows s hA center width z ∈ Set.Icc (0 : ℝ) cap) ∧
      LipschitzWith lip (allocatedAffineLongJetProxy B U basis S x u rows s hA center width) := by
  intro bound cap lip
  have hm := allocatedAffineLongJetDensity_measurable B U basis hR hσ S x u rows s hA center width hσ1
  have hb (y : input → ℝ) := allocatedNormalizedLongJetDensity_output_bounds
    B U basis hR hσ S x rows s hA hM hi hP hMP hRP hRi hσi hcount u hσ1
      (fun i => center i + width i * y i)
  exact densityMixture_uniform_bound (jointBooleanSource (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val))
    (allocatedAffineLongJetDensity B U basis S x u rows s hA center width) cap lip
    (fun z => (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    (Filter.Eventually.of_forall hb)

theorem allocatedAffineLongJetProxy_zero_off_ball (hσ1 : ∀ j, σ j ≤ 1)
    (center width : input → ℝ) (hw : ∀ i, |center i| + |width i| ≤ 1)
    (v : output → ℝ) (hv : radius < ‖v‖) :
    allocatedAffineLongJetProxy B U basis S x u rows s hA center width v = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [jointBooleanSource_ae_closedBall (fun a : {a // ¬grid a} => B a.val)
    (fun a => layerSamplerDegree I n a.val)] with y hy
  have hy' : ‖y‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hy
  have hs : ‖fun i => center i + width i * y i‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    have hiy : |y i| ≤ 1 := (norm_le_pi_norm y i).trans hy'
    calc
      ‖center i + width i * y i‖ ≤ |center i| + |width i| * |y i| := by
        simpa only [Real.norm_eq_abs, abs_mul] using norm_add_le (center i) (width i * y i)
      _ ≤ |center i| + |width i| := add_le_add le_rfl
        (by simpa using mul_le_mul_of_nonneg_left hiy (abs_nonneg (width i)))
      _ ≤ 1 := hw i
  exact allocatedNormalizedLongJetDensity_zero_off_ball B U basis hR hσ S x rows s hA
    hM hi hP hMP hRP hRi hσi hcount u hσ1 _ hs v hv

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
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
variable (s : ∀ j : Fin m, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := O j)
  S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (Mk : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "Jet" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "bound" => NNReal.mk
  (Real.exp (allocatedDensityLog (G := G) B α O P)) (Real.exp_nonneg _)
local notation "cap" => bound ^ Fintype.card (LayerSamplerAxis I n)
local notation "lip" => (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound * cap

include hR hσ hMk hi hP hMkP hRP hRi hσi hcount in
theorem allocatedAffineLongJetProxy_residue_l1 (hσ1 : ∀ j, σ j ≤ 1)
    (L step H M : Tuple → ℕ) (c : Tuple → ℤ)
    (hL : ∀ j, 0 < L j) (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
    (hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (modulus : Tuple → Option α → ℕ) (residue : ∀ j i, ZMod (modulus j i))
    (hm : ∀ j i, 0 < modulus j i) (hmM : ∀ j i, modulus j i ≤ M j)
    (hsize : ∀ j, (Fintype.card α + 1) * M j ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((M j : ℝ) / H j) <
      volume.real (scalarCubeDomain α))
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / L j ≤ ε) :
    let Δ := fun z : Jet → ℝ => (FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α (H j) (M j)
        (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j) (hsize j))).mean
        (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA
          (principalTupleFlatten (fun a : {a // ¬grid a} => B a.val) (fun a => degree a.val) α
            (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / L j)) z) -
      allocatedAffineLongJetProxy B U basis S x u rows s hA
        (principalProgressionSliceCenter (α := α) (fun a : {a // ¬grid a} => B a.val)
          (fun a => degree a.val) L c)
        (principalProgressionSliceWidth (α := α) (fun a : {a // ¬grid a} => B a.val)
          (fun a => degree a.val) L H step) z
    Integrable Δ ∧ (∫ z, |Δ z|) ≤
      ((2 * (cap : ℝ) * scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) +
        (lip : ℝ) * 2) * ∑ j, (M j : ℝ) / H j + (lip : ℝ) * ε) *
        (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P)) ^ Fintype.card Jet := by
  intro Δ
  let weights := FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α (H j) (M j)
    (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j) (hsize j))
  let tupleLower := fun (a : {a // ¬grid a}) (p : B a.val × Fin (degree a.val)) => (c ⟨a,p⟩ : ℝ) / L ⟨a,p⟩
  let tupleWidth := fun (a : {a // ¬grid a}) (p : B a.val × Fin (degree a.val)) =>
    (step ⟨a,p⟩ : ℝ) * ((H ⟨a,p⟩ : ℝ) - 1) / L ⟨a,p⟩
  let F := fun (v : ∀ j, IntegerScalarCubeBox α (H j)) =>
    principalTupleFlatten (fun a : {a // ¬grid a} => B a.val) (fun a => degree a.val) α
      (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / L j)
  let center := principalProgressionSliceCenter (α := α) (fun a : {a // ¬grid a} => B a.val)
    (fun a => degree a.val) L c
  let width := principalProgressionSliceWidth (α := α) (fun a : {a // ¬grid a} => B a.val)
    (fun a => degree a.val) L H step
  let proxy := allocatedAffineLongJetProxy B U basis S x u rows s hA center width
  let density := allocatedNormalizedLongJetDensity B U basis S x u rows s hA
  let radius := Real.exp (allocatedJetSupportLog (G := G) B α O P)
  have hw (a) (p) : |tupleLower a p| + |tupleWidth a p| ≤ 1 :=
    (progression_slice_endpoint_geometry (c ⟨a,p⟩) (hL _) (hstep _) (hH _) hδ
      (hsubset _) (hdense _)).2.2.1
  have hF (v) (hv : 0 < weights.weight v) : ‖F v‖ ≤ 1 := by
    apply (principalTupleFlatten_norm_apply_le _ _ _ _).trans
    apply progressionTuple_norm_le L step H c hH (fun j => hw j.1 j.2) v
    intro j
    exact scalarCubeResidueWeights_cube_support α (H j) (M j) (by have := hH j; omega)
      (modulus j) (residue j) (hm j) (hmM j) (hsize j) (v j)
      (FiniteProbabilityWeights.pi_weight_pos_component _ v hv j)
  have hs (z : Jet → ℝ) (hz : radius < ‖z‖) : Δ z = 0 := by
    have hp : proxy z = 0 := allocatedAffineLongJetProxy_zero_off_ball B U basis hR hσ S x rows s hA
      hMk hi hP hMkP hRP hRi hσi hcount u hσ1 center width
      (fun i => (principalProgressionSlice_parameters (α := α)
        (fun a : {a // ¬grid a} => B a.val) (fun a => degree a.val)
        L H step c hL hstep hH hδ hsubset hdense i).2.2) z hz
    have hd : weights.mean (fun v => density (F v) z) = 0 := by
      apply Finset.sum_eq_zero
      intro v _
      by_cases hv : weights.weight v = 0
      · simp only [hv, zero_mul]
      · have hf := allocatedNormalizedLongJetDensity_zero_off_ball B U basis hR hσ S x
          rows s hA hMk hi hP hMkP hRP hRi hσi hcount u hσ1 (F v)
          (hF v (lt_of_le_of_ne (weights.nonneg v) (Ne.symm hv))) z hz
        exact mul_eq_zero_of_right _ hf
    exact sub_eq_zero.mpr (hd.trans hp.symm)
  have hint : Integrable (fun z => weights.mean (fun v => density (F v) z)) := by
    apply integrable_finsetSum
    intro v _
    exact ((allocatedNormalizedLongJetDensity_probability B U basis hR hσ S x u
      rows s hA hσ1 (F v)).2.1).const_mul (weights.weight v)
  have hip := (allocatedAffineLongJetProxy_probability B U basis hR hσ S x u rows s hA
    center width hσ1).2.1
  refine ⟨hint.sub hip, ?_⟩
  apply integral_norm_le_box Δ (Real.exp_nonneg _) hs
  intro z _
  exact allocatedAffineLongJetProxy_residue_error B U basis hR hσ S x u rows s hA hMk hi hP hMkP
    hRP hRi hσi hcount hσ1 L step H M c hL hstep hH hδ hsubset hdense
    modulus residue hm hmM hsize hsmall hε hmesh z

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

include hrows hcard in
theorem exists_early_allocated_affine_residue_source_with_scales
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (block : ∀ a : LayerSamplerAxis I n, O a.1 → B a)
    (hblock : ∀ a, Function.Injective (block a))
    {δ η : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η) :
    ∃ ρmin : ℝ≥0, 0 < ρmin ∧ ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
      (∀ P, ρmin ≤ ρ P ∧ ρ P ≤ 1) ∧
      (∀ P, (ρ P : ℝ) = partitionedAffineSourceRadius (B := B)
        (O := fun a : {a // ¬P a} => O a.val.1) (α := α) (layerSamplerDegree I n) P A T (δ / 2) η) ∧
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      t = allocatedAffineSourceTolerance (G := G) (O := O) (α := α) B A T (δ / 2) η ∧
      ∀ {J : Fin m → Type*} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        {R σ : Fin m → ℝ} (_hR : ∀ j, 0 < R j) (_hσ : ∀ j, 0 < σ j)
        (S : LayerSamplerScale (G := G) B U basis R σ),
      (∀ j, σ j ≤ t) →
      ∀ (x : G → IntegerScalarCubeBox α S.value)
        (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)),
      ∀ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0),
      ∀ {Mk : ℕ} (_ : 0 < Mk)
        (_ : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j)
          (s j) (hA j) (1 / (Mk : ℝ)))
        {P : ℝ} (_ : 0 ≤ P) (_ : (Mk : ℝ) ≤ Real.exp P)
        (_ : ∀ j, R j ≤ Real.exp P) (_ : ∀ j, (R j)⁻¹ ≤ Real.exp P)
        (_ : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
        (_ : ∀ j : Fin m, (Fintype.card
          (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P),
      ∀ (L step H M : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → ℕ) (c : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → ℤ)
        (_ : ∀ j, 0 < L j) (_ : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
        (_ : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
        (_ : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
        (modulus : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → Option α → ℕ) (residue : ∀ j i, ZMod (modulus j i))
        (hm : ∀ j i, 0 < modulus j i) (hmM : ∀ j i, modulus j i ≤ M j)
        (hsize : ∀ j, (Fintype.card α + 1) * M j ≤ H j)
        (_ : ∀ j, scalarCubeGridBoundaryConstant α * ((M j : ℝ) / H j) < volume.real (scalarCubeDomain α))
        {ε : ℝ} (_ : 0 ≤ ε) (_ : ∀ j, (step j : ℝ) / L j ≤ ε),
      let center := principalProgressionSliceCenter (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L c
      let width := principalProgressionSliceWidth (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step
      let ideal := diagonalImageDensity (fun o : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) => R o.1.val.1)
        (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
          (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1) (ρ (allocatedGridAxis (I := I) U basis S.value)) center width)
      let discrete := fun z : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) → ℝ =>
        (FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α (H j) (M j)
          (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j) (hsize j))).mean
          (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA
            (principalTupleFlatten (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) α
              (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / L j)) z)
      let bound : ℝ≥0 := ⟨Real.exp (allocatedDensityLog (G := G) B α O P), Real.exp_nonneg _⟩
      let cap := bound ^ Fintype.card (LayerSamplerAxis I n)
      let lip := (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound * cap
      (∫ z, |ideal z - discrete z|) ≤ η +
        ((2 * (cap : ℝ) * scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) +
          (lip : ℝ) * 2) * ∑ j, (M j : ℝ) / H j + (lip : ℝ) * ε) *
          (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P)) ^ Fintype.card (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) := by
  have hδhalf1 : δ / 2 ≤ 1 := by linarith
  obtain ⟨ρmin, hρmin, ρ, hρ, hρeq, t, ht, htone, hteq, hs⟩ :=
    exists_early_allocated_affine_proxy_l1_with_scales (G := G) B rows hrows hcard
      ψ hψ hrange hzero hone A T hLip hTransition block hblock (half_pos hδ) hδhalf1 hη
  refine ⟨ρmin, hρmin, ρ, hρ, hρeq, t, ht, htone, hteq, ?_⟩
  intro J _ U basis R σ hR hσ S hσsmall x u s hA Mk hMk hi P hP hMkP hRP hRi hσi hcount
    L step H M c hL hstep hH hsubset hdense modulus residue hm hmM hsize hsmall ε hε hmesh
    center width ideal discrete bound cap lip
  have hσ1 : ∀ j, σ j ≤ 1 := fun j => (hσsmall j).trans htone
  have hg := principalProgressionSlice_parameters (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)
    L H step c hL hstep hH hδ hsubset hdense
  have hcont := hs U basis hR hσ S hσsmall x u center width
    (fun i => (hg i).2.1) (fun i => (hg i).2.2) s hA
  have hdisc := allocatedAffineLongJetProxy_residue_l1 B U basis hR hσ S x u rows s hA
    hMk hi hP hMkP hRP hRi hσi hcount hσ1 L step H M c hL hstep hH hδ hsubset hdense
    modulus residue hm hmM hsize hsmall hε hmesh
  let proxy := allocatedAffineLongJetProxy B U basis S x u rows s hA center width
  have hρpos : 0 < ρ (allocatedGridAxis (I := I) U basis S.value) := hρmin.trans_le (hρ (allocatedGridAxis (I := I) U basis S.value)).1
  have hideal := activeAveragedSlicedProfileIdeal_spec (G := G) (B := B)
    (G × Option α) (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1) (ρ (allocatedGridAxis (I := I) U basis S.value)) hρpos center width
  have hIi : Integrable ideal := diagonalImageDensity_integrable
    (fun o : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) => R o.1.val.1) (fun o => (hR o.1.val.1).ne') hideal.2.2.1
  have hp := (allocatedAffineLongJetProxy_probability B U basis hR hσ S x u rows s hA center width hσ1).2.1
  have hdiff : Integrable (fun z => ideal z - proxy z) := hIi.sub hp
  calc
    _ ≤ ∫ z, (|ideal z - proxy z| + |discrete z - proxy z|) := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => abs_nonneg _))
        (hdiff.abs.add hdisc.1.abs)
      apply Filter.Eventually.of_forall
      intro z
      change |ideal z - discrete z| ≤ |ideal z - proxy z| + |discrete z - proxy z|
      simpa only [abs_sub_comm (proxy z) (discrete z)] using abs_sub_le (ideal z) (proxy z) (discrete z)
    _ = (∫ z, |ideal z - proxy z|) + ∫ z, |discrete z - proxy z| := integral_add hdiff.abs hdisc.1.abs
    _ ≤ _ := add_le_add hcont hdisc.2

include hrows hcard in
theorem exists_early_allocated_affine_residue_source
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (block : ∀ a : LayerSamplerAxis I n, O a.1 → B a)
    (hblock : ∀ a, Function.Injective (block a))
    {δ η : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η) :
    ∃ ρmin : ℝ≥0, 0 < ρmin ∧ ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
      (∀ P, ρmin ≤ ρ P ∧ ρ P ≤ 1) ∧ ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      ∀ {J : Fin m → Type*} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        {R σ : Fin m → ℝ} (_hR : ∀ j, 0 < R j) (_hσ : ∀ j, 0 < σ j)
        (S : LayerSamplerScale (G := G) B U basis R σ),
      (∀ j, σ j ≤ t) →
      ∀ (x : G → IntegerScalarCubeBox α S.value)
        (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)),
      ∀ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0),
      ∀ {Mk : ℕ} (_ : 0 < Mk)
        (_ : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j)
          (s j) (hA j) (1 / (Mk : ℝ)))
        {P : ℝ} (_ : 0 ≤ P) (_ : (Mk : ℝ) ≤ Real.exp P)
        (_ : ∀ j, R j ≤ Real.exp P) (_ : ∀ j, (R j)⁻¹ ≤ Real.exp P)
        (_ : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
        (_ : ∀ j : Fin m, (Fintype.card
          (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P),
      ∀ (L step H M : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → ℕ) (c : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → ℤ)
        (_ : ∀ j, 0 < L j) (_ : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
        (_ : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
        (_ : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
        (modulus : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → Option α → ℕ) (residue : ∀ j i, ZMod (modulus j i))
        (hm : ∀ j i, 0 < modulus j i) (hmM : ∀ j i, modulus j i ≤ M j)
        (hsize : ∀ j, (Fintype.card α + 1) * M j ≤ H j)
        (_ : ∀ j, scalarCubeGridBoundaryConstant α * ((M j : ℝ) / H j) < volume.real (scalarCubeDomain α))
        {ε : ℝ} (_ : 0 ≤ ε) (_ : ∀ j, (step j : ℝ) / L j ≤ ε),
      let center := principalProgressionSliceCenter (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L c
      let width := principalProgressionSliceWidth (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step
      let ideal := diagonalImageDensity (fun o : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) => R o.1.val.1)
        (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
          (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1) (ρ (allocatedGridAxis (I := I) U basis S.value)) center width)
      let discrete := fun z : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) → ℝ =>
        (FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α (H j) (M j)
          (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j) (hsize j))).mean
          (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA
            (principalTupleFlatten (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) α
              (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / L j)) z)
      let bound : ℝ≥0 := ⟨Real.exp (allocatedDensityLog (G := G) B α O P), Real.exp_nonneg _⟩
      let cap := bound ^ Fintype.card (LayerSamplerAxis I n)
      let lip := (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound * cap
      (∫ z, |ideal z - discrete z|) ≤ η +
        ((2 * (cap : ℝ) * scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) +
          (lip : ℝ) * 2) * ∑ j, (M j : ℝ) / H j + (lip : ℝ) * ε) *
          (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P)) ^ Fintype.card (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) := by
  obtain ⟨ρmin, hρmin, ρ, hρ, _, t, ht, htone, _, hs⟩ :=
    exists_early_allocated_affine_residue_source_with_scales (G := G) B rows hrows hcard
      ψ hψ hrange hzero hone A T hLip hTransition block hblock hδ hδone hη
  exact ⟨ρmin, hρmin, ρ, hρ, t, ht, htone, hs⟩

end Erdos3.VectorPolynomial

end

end OAI
