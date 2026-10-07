import OAI.Combinatorics.Progressions.Estimates.AllocatedCoveredSiteExpansion
import OAI.Combinatorics.Progressions.Estimates.AllocatedFiniteProxyRegularity
import OAI.Combinatorics.Progressions.Estimates.AllocatedSlicedDiscreteIdeal
import OAI.Combinatorics.Progressions.Probability.DensityComparisonComposition

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {α : Type*} [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value) (rows : ∀ j, O j → Finset α)
variable (modulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "integerOutput" => {q : output // allocatedLongIntegerCoordinate B U b S q}
local notation "realOutput" => UnselectedColumn (allocatedLongIntegerSelect B U b S (O := O))
local notation "reference" => allocatedLongJetReference B U b S O
local notation "density" => allocatedLongProfileDensity B U b S x rows modulus residue

theorem allocatedLongReference_l1_comparison
    (f g : (output → ℝ) → ℝ) {Kf Kg : ℝ≥0} (Ro : ℝ≥0)
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hfs : ∀ v, (Ro : ℝ) < ‖v‖ → f v = 0)
    (hgs : ∀ v, (Ro : ℝ) < ‖v‖ → g v = 0)
    {Cf Cg : ℝ} (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hfb : ∀ v, |f v| ≤ Cf) (hgb : ∀ v, |g v| ≤ Cg)
    (hfg : Integrable (fun v => f v - g v)) {ε : ℝ}
    (he : (∫ v, |f v - g v|) ≤ ε)
    {mesh C : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
    (hmesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
    (hC : 1 ≤ C)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x rows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U b S x rows j modulus (residue j) z ≤ C) :
    (∫ z, |density f z - density g z| ∂reference) ≤
      C ^ Fintype.card (LayerSamplerAxis I n) *
        (ε + (2 * (Ro : ℝ)) ^ Fintype.card realOutput *
          ((2 * (Ro : ℝ) + 2) ^ Fintype.card integerOutput * ((Kf : ℝ) + Kg) * mesh)) := by
  apply density_l1_le_of_complex_tests reference (density f) (density g)
    (allocatedLongProfileDensity_measurable B U b S x rows modulus residue f hf.continuous.measurable)
    (allocatedLongProfileDensity_measurable B U b S x rows modulus residue g hg.continuous.measurable)
    (allocatedLongProfileDensity_integrable B U b S x rows modulus residue f
      hf.continuous.measurable Ro.coe_nonneg hfs hC hCf hfb hm)
    (allocatedLongProfileDensity_integrable B U b S x rows modulus residue g
      hg.continuous.measurable Ro.coe_nonneg hgs hC hCg hgb hm)
  intro φ hφ hφb
  have h := allocatedLongReference_test_comparison B U b S x rows modulus residue
    f g Ro hf hg hfs hgs hCf hCg hfb hgb hfg he hmesh0 hmesh1 hmesh hC hm φ hφ hφb
  simpa only [allocatedLongProfileDensity, Complex.ofReal_div, div_mul_eq_mul_div] using h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "integerOutput" => {q : output // allocatedLongIntegerCoordinate B U b S q}
local notation "realOutput" => UnselectedColumn (allocatedLongIntegerSelect B U b S (O := O))
local notation "reference" => allocatedLongJetReference B U b S O
local notation "frozenSource" => allocatedFrozenCoefficientSource B U b hR hσ S
local notation "test" => allocatedCoveredFixedTest B U b S x u v₀ rows Q hb o bW d

theorem allocatedCoveredProfile_test_comparison
    (f g : AllocatedLongJetRows B U b S O → ℝ)
    (hf : Integrable f reference) (hg : Integrable g reference)
    {ε : ℝ} (he : (∫ z, |f z - g z| ∂reference) ≤ ε)
    (F : AllocatedFrozenCoefficients B U b S × EuclideanJetLayers U O → ℂ)
    (hF : Measurable F) (hFb : ∀ p, ‖F p‖ ≤ 1) :
    ‖(∫ a₀, ∫ z, (f z : ℂ) * test F a₀ z ∂reference ∂frozenSource) -
      (∫ a₀, ∫ z, (g z : ℂ) * test F a₀ z ∂reference ∂frozenSource)‖ ≤ ε := by
  let : IsProbabilityMeasure frozenSource := allocatedFrozenCoefficientSource_probability B U b hR hσ S
  have h := retained_density_nested_test_error frozenSource reference f g hf hg
    (fun p => test F p.1 p.2)
    (allocatedCoveredFixedTest_measurable B U b S x u v₀ rows Q hb o bW d F hF)
    (fun p => allocatedCoveredFixedTest_norm_le B U b S x u v₀ rows Q hb o bW d F hFb p.1 p.2)
  exact h.trans (by simpa only [one_mul] using he)

theorem allocatedCoveredLongProfile_test_comparison
    (modulus : ℕ)
    (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (f g : (output → ℝ) → ℝ) {Kf Kg : ℝ≥0} (Ro : ℝ≥0)
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hfs : ∀ v, (Ro : ℝ) < ‖v‖ → f v = 0)
    (hgs : ∀ v, (Ro : ℝ) < ‖v‖ → g v = 0)
    {Cf Cg : ℝ} (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hfb : ∀ v, |f v| ≤ Cf) (hgb : ∀ v, |g v| ≤ Cg)
    (hfg : Integrable (fun v => f v - g v)) {ε : ℝ}
    (he : (∫ v, |f v - g v|) ≤ ε)
    {mesh C : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
    (hmesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
    (hC : 1 ≤ C)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x rows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U b S x rows j modulus (residue j) z ≤ C)
    (F : AllocatedFrozenCoefficients B U b S × EuclideanJetLayers U O → ℂ)
    (hF : Measurable F) (hFb : ∀ p, ‖F p‖ ≤ 1) :
    ‖(∫ a₀, ∫ z, (allocatedLongProfileDensity B U b S x rows modulus residue f z : ℂ) *
        test F a₀ z ∂reference ∂frozenSource) -
      (∫ a₀, ∫ z, (allocatedLongProfileDensity B U b S x rows modulus residue g z : ℂ) *
        test F a₀ z ∂reference ∂frozenSource)‖ ≤
      C ^ Fintype.card (LayerSamplerAxis I n) *
        (ε + (2 * (Ro : ℝ)) ^ Fintype.card realOutput *
          ((2 * (Ro : ℝ) + 2) ^ Fintype.card integerOutput * ((Kf : ℝ) + Kg) * mesh)) := by
  apply allocatedCoveredProfile_test_comparison B U b hR hσ S x u v₀ rows Q hb o bW d
    _ _
    (allocatedLongProfileDensity_integrable B U b S x rows modulus residue f
      hf.continuous.measurable Ro.coe_nonneg hfs hC hCf hfb hm)
    (allocatedLongProfileDensity_integrable B U b S x rows modulus residue g
      hg.continuous.measurable Ro.coe_nonneg hgs hC hCg hgb hm)
    _ F hF hFb
  exact allocatedLongReference_l1_comparison B U b S x rows modulus residue f g Ro
    hf hg hfs hgs hCf hCg hfb hgb hfg he hmesh0 hmesh1 hmesh hC hm

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped ContDiff NNReal Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [∀ j, Nonempty (O j)]

local notation "hLayer" => layerSamplerDegree I n

theorem exists_allocated_long_actual_l1
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
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
        {M : ℕ} (_hM : 0 < M)
        (_hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (M : ℝ)))
        {P : ℝ} (_hP : 0 ≤ P) (_hMP : (M : ℝ) ≤ Real.exp P)
        (_hRP : ∀ j, R j ≤ Real.exp P) (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
        (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
        (_hcount : ∀ j : Fin m, (Fintype.card
          (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)
        (modulus : ℕ)
        (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
        {mesh C : ℝ} (_hmesh0 : 0 ≤ mesh) (_hmesh1 : mesh ≤ 1)
        (_hmesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh) (_hC : 1 ≤ C)
        (_hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ∧
          allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ≤ C),
      let ideal := physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer
        (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1)
        (fun a => R a.1) (fun a => hR a.1) δ
      let Q := {q : (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1) //
        allocatedLongIntegerCoordinate B U basis S q}
      let select := allocatedLongIntegerSelect B U basis S (O := O)
      let bound : ℝ≥0 := ⟨Real.exp (allocatedDensityLog (G := G) B α O P), (Real.exp_pos _).le⟩
      let Kp : ℝ≥0 := (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound *
        bound ^ Fintype.card (LayerSamplerAxis I n)
      let Ki : ℝ≥0 := ‖(∏ q : (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1),
        R q.1.val.1)⁻¹‖₊ *
        (affineProductProfileLip (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1) δ *
          (NNReal.mk (Real.exp P) (Real.exp_pos P).le))
      let Ro := Real.toNNReal (max (Real.exp (allocatedJetSupportLog (G := G) B α O P))
        (Real.exp P * (partitionedIdealRadius α m + 1)))
      let proxy := allocatedLongProfileDensity B U basis S x rows modulus residue
        (allocatedContinuousLongJetProxy B U basis S x u rows s hA)
      let target := allocatedLongProfileDensity B U basis S x rows modulus residue ideal
      Integrable proxy (allocatedLongJetReference B U basis S O) ∧
        Integrable target (allocatedLongJetReference B U basis S O) ∧
        (∫ z, |proxy z - target z| ∂allocatedLongJetReference B U basis S O) ≤
        C ^ Fintype.card (LayerSamplerAxis I n) *
          (ε + (2 * (Ro : ℝ)) ^ Fintype.card (UnselectedColumn select) *
            ((2 * (Ro : ℝ) + 2) ^ Fintype.card Q * ((Kp : ℝ) + Ki) * mesh)) := by
  obtain ⟨δ, hδ, hδ1, hδeq, ht, ht1, hcompare⟩ := exists_allocated_proxy_l1_comparison
    (G := G) (α := α) (O := O) B ψ hψ hrange hzero hone A T hLip hTransition hε
  refine ⟨δ, hδ, hδ1, hδeq, ht, ht1, ?_⟩
  intro J _ U basis R hR σ hσ hσt S x u rows hrows hcard block s hA
    M hM hi P hP hMP hRP hRi hσi hcount modulus residue mesh C hmesh0 hmesh1 hmesh hC hm
  dsimp only
  have hσ1 : ∀ j, σ j ≤ 1 := fun j => (hσt j).trans ht1
  have hL1 := (hcompare U basis hR hσ hσt S x u rows hrows hcard block s hA).1
  have hp := allocatedContinuousLongJetProxy_output_bounds B U basis hR hσ S x rows s hA
    hM hi hP hMP hRP hRi hσi hcount u hσ1
  have hip := physicalActiveProfileIdeal_probability (G := G) (B := B) (G × Option α)
    hLayer (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1)
    (fun a => R a.1) (fun a => hR a.1) δ hδ
  have hpp := allocatedContinuousLongJetProxy_probability B U basis hR hσ S x u rows s hA hσ1
  have hil := physicalActiveProfileIdeal_lipschitz (G := G) (B := B) (G × Option α)
    hLayer (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1)
    (fun a => R a.1) (fun a => hR a.1) δ hδ ⟨Real.exp P, (Real.exp_pos P).le⟩ (fun a => hRi a.1)
  let Ro := Real.toNNReal (max (Real.exp (allocatedJetSupportLog (G := G) B α O P))
    (Real.exp P * (partitionedIdealRadius α m + 1)))
  have hRoP : Real.exp (allocatedJetSupportLog (G := G) B α O P) ≤ (Ro : ℝ) :=
    (le_max_left _ _).trans (Real.le_coe_toNNReal _)
  have hRoI : Real.exp P * (partitionedIdealRadius α m + 1) ≤ (Ro : ℝ) :=
    (le_max_right _ _).trans (Real.le_coe_toNNReal _)
  have hib := physicalActiveProfileIdeal_bound (G := G) (B := B) (G × Option α)
    hLayer (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1)
    (fun a => R a.1) (fun a => hR a.1) δ hδ
  have hps : ∀ v, (Ro : ℝ) < ‖v‖ →
      allocatedContinuousLongJetProxy B U basis S x u rows s hA v = 0 := fun v hv =>
    allocatedContinuousLongJetProxy_zero_off_ball B U basis hR hσ S x rows s hA
      hM hi hP hMP hRP hRi hσi hcount u hσ1 v (hRoP.trans_lt hv)
  have his : ∀ v, (Ro : ℝ) < ‖v‖ →
      physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer
        (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1)
        (fun a => R a.1) (fun a => hR a.1) δ v = 0 := fun v hv =>
    physicalActiveProfileIdeal_zero_outside (G := G) (B := B) (G × Option α)
      hLayer (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1)
      (fun a => R a.1) (fun a => hR a.1) (fun a => Nat.succ_le_of_lt a.1.isLt) δ hδ hδ1
      ⟨Real.exp P, (Real.exp_pos P).le⟩ (fun a => hRP a.1) v (hRoI.trans_lt hv)
  have hpb : ∀ v, |allocatedContinuousLongJetProxy B U basis S x u rows s hA v| ≤
      (Real.exp (allocatedDensityLog (G := G) B α O P)) ^ Fintype.card (LayerSamplerAxis I n) := by
    intro v
    rw [abs_of_nonneg (hp.1 v).1]
    exact (hp.1 v).2
  have hpi := allocatedLongProfileDensity_integrable B U basis S x rows modulus residue
    _ hp.2.continuous.measurable Ro.coe_nonneg hps hC ((abs_nonneg _).trans (hpb 0)) hpb hm
  have hii := allocatedLongProfileDensity_integrable B U basis S x rows modulus residue
    _ hil.continuous.measurable Ro.coe_nonneg his hC ((abs_nonneg _).trans (hib 0)) hib hm
  refine ⟨hpi, hii, ?_⟩
  apply allocatedLongReference_l1_comparison B U basis S x rows modulus residue
    _ _ Ro hp.2 hil hps his ((abs_nonneg _).trans (hpb 0)) ((abs_nonneg _).trans (hib 0))
    hpb hib (hpp.2.1.sub hip.2.1) _ hmesh0 hmesh1 hmesh hC hm
  simpa only [abs_sub_comm] using hL1

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
variable (x : G → IntegerScalarCubeBox (Fin 1) S.value)
variable (u : PrincipalAxisTuples (α := Fin 1) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (s : ∀ j : Fin m, Finset (Fin 1) ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) id).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := Finset (Fin 1))
  S.positive x (j.val + 1) id (s j) (hA j) (1 / (Mk : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "Jet" => (Σ _a : {a // ¬grid a}, Finset (Fin 1))
local notation "bound" => NNReal.mk
  (Real.exp (allocatedDensityLog (G := G) B (Fin 1) (fun _ => Finset (Fin 1)) P)) (Real.exp_nonneg _)
local notation "cap" => bound ^ Fintype.card (LayerSamplerAxis I n)
local notation "lip" => (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound * cap

local notation "Endpoint" => OneCubeActiveEndpoint (B := B) degree grid
local notation "Row" => OneCubeActiveRow grid

local notation "Output" => (Σ _e : Row, Unit)
local notation "jetRows" => (fun _ : Fin m => Finset (Fin 1))

include hR hσ hMk hi hP hMkP hRP hRi hσi hcount in
theorem allocatedSlicedDiscreteIdeal_reference_l1
    (L step H M : Tuple → ℕ) (c : Tuple → ℤ)
    (hL : ∀ j, 0 < L j) (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
    (hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (modulus : Tuple → Option (Fin 1) → ℕ) (residue : ∀ j i, ZMod (modulus j i))
    (hm : ∀ j i, 0 < modulus j i) (hmM : ∀ j i, modulus j i ≤ M j)
    (hsize : ∀ j, (Fintype.card (Fin 1) + 1) * M j ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant (Fin 1) * ((M j : ℝ) / H j) <
      volume.real (scalarCubeDomain (Fin 1)))
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / L j ≤ ε)
    (N O : ℕ) (hN : Fintype.card Endpoint ≤ N) (hO : Fintype.card Row ≤ O)
    (hB : ∀ a : {a // ¬grid a}, 4 ≤ Fintype.card (B a.val))
    (hx : ∀ g, IntegerScalarCube S.value (fun i => (x g i : ℤ)))
    (hu : ∀ j, IntegerScalarCube (principalAxisLength grid (allocatedPrincipalSides B U basis S) j)
      (fun i => (u j i : ℤ)))
    {a η : ℝ} (ha : 0 < a) (hδone : δ ≤ 1) (hη : 0 < η)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (A : ℝ≥0) (hTransition : LipschitzWith A Real.smoothTransition)
    (hσsmall : ∀ j, |σ j| ≤ slicedPolynomialScale N O N m m 1 1 a (δ / 2) A η)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : (δ / 2)⁻¹ ≤ Real.exp P)
    (outputModulus : ℕ)
    (outputResidue : ∀ j, Matrix (Finset (Fin 1)) (AllocatedNonkernelCoefficient (G := G) B j)
      (ZMod outputModulus))
    {mesh Cmask : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
    (hscaleMesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
    (hCmask : 1 ≤ Cmask)
    (hmask : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x (fun _ => id) j
      outputModulus (outputResidue j) z ∧ allocatedIntegerKernelMask B U basis S x (fun _ => id) j
      outputModulus (outputResidue j) z ≤ Cmask) :
    let lower := fun (a : {a // ¬grid a}) (p : B a.val × Fin (degree a.val)) => (c ⟨a,p⟩ : ℝ) / L ⟨a,p⟩
    let width := fun (a : {a // ¬grid a}) (p : B a.val × Fin (degree a.val)) =>
      (step ⟨a,p⟩ : ℝ) * ((H ⟨a,p⟩ : ℝ) - 1) / L ⟨a,p⟩
    let ideal := allocatedSlicedPhysicalJetIdeal B U basis S hR hB lower width
    let discrete := fun z =>
      (FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights (Fin 1) (H j) (M j)
        (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j) (hsize j))).mean
        (fun v => allocatedNormalizedLongJetDensity B U basis S x u (fun _ => id) s hA
          (principalTupleFlatten (fun a : {a // ¬grid a} => B a.val) (fun a => degree a.val) (Fin 1)
            (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / L j)) z)
    let radius := max (4 * Real.exp P) (Real.exp (allocatedJetSupportLog (G := G) B (Fin 1) jetRows P))
    let Ki : ℝ≥0 := (‖(∏ o : Output, R o.1.2.val.1)⁻¹‖₊ *
      (NNReal.mk (Real.exp (slicedJointDensityLogBudget O m P)) (Real.exp_nonneg _) *
        NNReal.mk (Real.exp P) (Real.exp_nonneg _))) * 2
    let select := allocatedLongIntegerSelect B U basis S (O := jetRows)
    (∫ z, |allocatedLongProfileDensity B U basis S x (fun _ => id) outputModulus outputResidue ideal z -
      allocatedLongProfileDensity B U basis S x (fun _ => id) outputModulus outputResidue discrete z|
      ∂allocatedLongJetReference B U basis S jetRows) ≤
      Cmask ^ Fintype.card (LayerSamplerAxis I n) *
        (η +
      ((2 * (cap : ℝ) * scalarCubeGridBoundaryConstant (Fin 1) / volume.real (scalarCubeDomain (Fin 1)) +
        (lip : ℝ) * 2) * ∑ j, (M j : ℝ) / H j + (lip : ℝ) * ε) *
        (2 * Real.exp (allocatedJetSupportLog (G := G) B (Fin 1) (fun _ => Finset (Fin 1)) P)) ^ Fintype.card Jet + (2 * radius) ^ Fintype.card (UnselectedColumn select) *
          ((2 * radius + 2) ^ Fintype.card {o : Jet // allocatedLongIntegerCoordinate B U basis S (O := jetRows) o} *
            ((Ki : ℝ) + lip) * mesh)) := by
  intro lower width ideal discrete radius Ki select
  have hδhalf : 0 < δ / 2 := half_pos hδ
  have ht := slicedEndpointUniformScale_spec N O m ha hδhalf A.coe_nonneg hη
  have hσ1 (j) : σ j ≤ 1 := (le_abs_self _).trans ((hσsmall j).trans ht.2.1)
  have hg (a) (p) := progression_slice_endpoint_geometry (c ⟨a,p⟩)
    (hL _) (hstep _) (hH _) hδ (hsubset _) (hdense _)
  have hw (a) (p) : |lower a p| + |width a p| ≤ 1 := (hg a p).2.2.1
  have hl (a) (p) : 0 ≤ lower a p := (hg a p).1
  have hwδ (a) (p) : δ / 2 ≤ width a p := (hg a p).2.1
  let weights := FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights (Fin 1) (H j) (M j)
    (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j) (hsize j))
  let F := fun (v : ∀ j, IntegerScalarCubeBox (Fin 1) (H j)) =>
    principalTupleFlatten (fun a : {a // ¬grid a} => B a.val) (fun a => degree a.val) (Fin 1)
      (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / L j)
  have hF (v) (hv : weights.weight v ≠ 0) : ‖F v‖ ≤ 1 := by
    apply (principalTupleFlatten_norm_apply_le _ _ _ _).trans
    apply progressionTuple_norm_le L step H c hH (fun j => hw j.1 j.2) v
    intro j
    exact scalarCubeResidueWeights_cube_support (Fin 1) (H j) (M j) (by have := hH j; omega)
      (modulus j) (residue j) (hm j) (hmM j) (hsize j) (v j)
      (FiniteProbabilityWeights.pi_weight_pos_component _ v
        (lt_of_le_of_ne (weights.nonneg v) (Ne.symm hv)) j)
  have hreg := allocatedFiniteLongJetDensity_regularity B U basis hR hσ S x (fun _ => id) s hA
    hMk hi hP hMkP hRP hRi hσi hcount u hσ1 weights F hF
  have hIb := allocatedSlicedPhysicalJetIdeal_uniform_bounds B U basis S hR hB lower width
    O hO ha hδhalf hP haP hδP hprincipal hwδ hl ⟨Real.exp P, Real.exp_nonneg _⟩ hRi
  have hIi := (allocatedSlicedPhysicalJetIdeal_probability B U basis S hR hB lower width
    ha hδhalf hprincipal hwδ hl).2.1
  have hIs (z : Jet → ℝ) (hz : radius < ‖z‖) : ideal z = 0 :=
    allocatedSlicedPhysicalJetIdeal_zero_off_ball B U basis S hR hB lower width hw
      ha hδhalf hprincipal hwδ hl ⟨Real.exp P, Real.exp_nonneg _⟩ hRP z ((le_max_left _ _).trans_lt hz)
  have hDs (z : Jet → ℝ) (hz : radius < ‖z‖) : discrete z = 0 :=
    hreg.2.2.1 z ((le_max_right _ _).trans_lt hz)
  have he := allocatedSlicedDiscreteIdeal_l1 B U basis hR hσ S x u s hA hMk hi hP hMkP
    hRP hRi hσi hcount L step H M c hL hstep hH hδ hsubset hdense
    modulus residue hm hmM hsize hsmall hε hmesh N O hN hO hB hx hu ha hδone hη
    hprincipal A hTransition hσsmall
  exact allocatedLongReference_l1_comparison B U basis S x (fun _ => id) outputModulus outputResidue
    ideal discrete ⟨radius, (Real.exp_nonneg _).trans (le_max_right _ _)⟩ hIb.2 hreg.2.1 hIs hDs
    (mul_nonneg (NNReal.coe_nonneg _) (Real.exp_nonneg _)) (NNReal.coe_nonneg cap) hIb.1 hreg.1
    (hIi.sub hreg.2.2.2) he hmesh0 hmesh1 hscaleMesh hCmask hmask

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped ContDiff NNReal Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [∀ j, Nonempty (O j)]

local notation "hLayer" => layerSamplerDegree I n

theorem exists_allocated_haar_ideal_comparison
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
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
        {M : ℕ} (_hM : 0 < M)
        (_hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (M : ℝ)))
        {P : ℝ} (_hP : 0 ≤ P) (_hMP : (M : ℝ) ≤ Real.exp P)
        (_hRP : ∀ j, R j ≤ Real.exp P) (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
        (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
        (_hcount : ∀ j : Fin m, (Fintype.card
          (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)
        (modulus : ℕ)
        (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
        {mesh C : ℝ} (_hmesh0 : 0 ≤ mesh) (_hmesh1 : mesh ≤ 1)
        (_hmesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh) (_hC : 1 ≤ C)
        (_hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ∧
          allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ≤ C),
      let ideal := physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer
        (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1)
        (fun a => R a.1) (fun a => hR a.1) δ
      let Q := {q : (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1) //
        allocatedLongIntegerCoordinate B U basis S q}
      let select := allocatedLongIntegerSelect B U basis S (O := O)
      let bound : ℝ≥0 := ⟨Real.exp (allocatedDensityLog (G := G) B α O P), (Real.exp_pos _).le⟩
      let Kp : ℝ≥0 := (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound *
        bound ^ Fintype.card (LayerSamplerAxis I n)
      let Ki : ℝ≥0 := ‖(∏ q : (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1),
        R q.1.val.1)⁻¹‖₊ *
        (affineProductProfileLip (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1) δ *
          (NNReal.mk (Real.exp P) (Real.exp_pos P).le))
      let Ro := Real.toNNReal (max (Real.exp (allocatedJetSupportLog (G := G) B α O P))
        (Real.exp P * (partitionedIdealRadius α m + 1)))
      let proxy := allocatedLongProfileDensity B U basis S x rows modulus residue
        (allocatedContinuousLongJetProxy B U basis S x u rows s hA)
      let target := allocatedLongProfileDensity B U basis S x rows modulus residue ideal
      ∀ (v₀ : PrincipalAxisTuples (α := α)
          (fun a => ¬allocatedGridAxis (I := I) U basis S.value a) (allocatedPrincipalSides B U basis S))
        (Kcov : Fin m → Type*) [∀ j, Fintype (Kcov j)]
        [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
        (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
        (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
        (bW : ∀ j, Module.Basis (Kcov j) ℤ
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
        (d : ℕ) [NeZero d]
        (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
        [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
        (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
        (_hΩm : ∀ j t, MeasurableSet (Ω j t))
        (_hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j)),
      let covered := fun f => allocatedCoveredProfileDensity B U basis hR _hσ S x u v₀ rows hb o bW d Ω f
      let law := Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
      Measurable (covered proxy) ∧ Measurable (covered target) ∧
        Integrable (covered proxy) law ∧ Integrable (covered target) law ∧
        (∫ y, |covered proxy y - covered target y| ∂law) ≤
        C ^ Fintype.card (LayerSamplerAxis I n) *
          (ε + (2 * (Ro : ℝ)) ^ Fintype.card (UnselectedColumn select) *
            ((2 * (Ro : ℝ) + 2) ^ Fintype.card Q * ((Kp : ℝ) + Ki) * mesh)) := by
  obtain ⟨δ, hδ, hδ1, hδeq, ht, ht1, hcompare⟩ := exists_allocated_long_actual_l1
    (G := G) (α := α) (O := O) B ψ hψ hrange hzero hone A T hLip hTransition hε
  refine ⟨δ, hδ, hδ1, hδeq, ht, ht1, ?_⟩
  intro J _ U basis R hR σ hσ hσt S x u rows hrows hcard block s hA
    M hM hi P hP hMP hRP hRi hσi hcount modulus residue mesh C hmesh0 hmesh1 hmesh hC hm
  have hdata := hcompare U basis hR hσ hσt S x u rows hrows hcard block s hA
    hM hi hP hMP hRP hRi hσi hcount modulus residue hmesh0 hmesh1 hmesh hC hm
  have hp := allocatedContinuousLongJetProxy_output_bounds B U basis hR hσ S x rows s hA
    hM hi hP hMP hRP hRi hσi hcount u (fun j => (hσt j).trans ht1)
  have hpm := allocatedLongProfileDensity_measurable B U basis S x rows modulus residue
    _ hp.2.continuous.measurable
  have him := allocatedLongProfileDensity_measurable B U basis S x rows modulus residue
    _ (physicalActiveProfileIdeal_measurable (G := G) (B := B) (G × Option α) hLayer
      (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1)
      (fun a => R a.1) (fun a => hR a.1) δ)
  dsimp only
  intro v₀ Kcov _ _ hb o bW d _ ν _ _ Ω hΩm hΩ
  refine ⟨allocatedCoveredProfileDensity_measurable B U basis hR hσ S x u v₀ rows hb o bW d Ω hΩm hΩ _ hpm,
    allocatedCoveredProfileDensity_measurable B U basis hR hσ S x u v₀ rows hb o bW d Ω hΩm hΩ _ him,
    allocatedCoveredProfileDensity_integrable B U basis hR hσ S x u v₀ rows hb o bW d Ω hΩm hΩ ν _ hpm hdata.1,
    allocatedCoveredProfileDensity_integrable B U basis hR hσ S x u v₀ rows hb o bW d Ω hΩm hΩ ν _ him hdata.2.1, ?_⟩
  exact (allocatedCoveredProfileDensity_l1 B U basis hR hσ S x u v₀ rows hb o bW d Ω hΩm hΩ ν
    _ _ hpm him hdata.1 hdata.2.1).trans hdata.2.2

end Erdos3.VectorPolynomial

end

end OAI
