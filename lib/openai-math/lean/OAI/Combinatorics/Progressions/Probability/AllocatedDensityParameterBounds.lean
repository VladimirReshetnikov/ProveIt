/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Estimates.AllocatedPartitionedProfileJet
import OAI.Combinatorics.Progressions.Estimates.AllocatedRefinedLongJetComparison
import OAI.Combinatorics.Progressions.Linear.AllocatedFixedKernelReplacement
import OAI.Combinatorics.Progressions.Linear.KernelComparisonScales

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α O : Type*} [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (rows : O → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixedReal" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ) / (S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)

noncomputable def allocatedNormalizedProfileJet (a : LayerSamplerAxis I n)
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ)
    (r : SamplerCoefficientSlot G B (layerSamplerDegree I n) a → ℝ) (o : O) : ℝ :=
  booleanCoefficient (fun t => MvPolynomial.eval (normalizedCubeTuple input fixedReal y t)
    (allocatedAxisProfilePolynomial B R σ a r)) (rows o)

omit [DecidableEq O] in
theorem allocatedNormalizedProfileJet_measurable (a : LayerSamplerAxis I n) :
    Measurable (fun p :
      (PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ) ×
        (SamplerCoefficientSlot G B (layerSamplerDegree I n) a → ℝ) =>
      allocatedNormalizedProfileJet B U basis S x u rows a p.1 p.2) := by
  rcases a with ⟨j, a⟩
  cases a with
  | inl i =>
    exact originalMonomialJetMap_measurable_comp Subtype.val input rows
      (allocatedContinuousProfileCenters (G := G) B R j i)
      (allocatedContinuousProfileWidths (G := G) B R σ j i)
      (fun _ => fixedReal) (fun _ => measurable_const) Prod.fst
      (fun k => (measurable_pi_apply k).comp measurable_fst) Prod.snd
      (fun k => (measurable_pi_apply k).comp measurable_snd)
  | inr i =>
    exact originalMonomialJetMap_measurable_comp Subtype.val input rows
      (allocatedIntegerProfileCenters (G := G) B R j i)
      (allocatedIntegerProfileWidths (G := G) B R σ j i)
      (fun _ => fixedReal) (fun _ => measurable_const) Prod.fst
      (fun k => (measurable_pi_apply k).comp measurable_fst) Prod.snd
      (fun k => (measurable_pi_apply k).comp measurable_snd)

theorem allocatedNormalizedKernelJet_eq (j : Fin m)
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ)
    {H : ℝ} (hH : H ≠ 0) :
    normalizedIntegerColumns (scalarKernelIntegerJet x (j.val + 1) rows)
        (kernelJetCoefficientScale G (j.val + 1) S.value H) (fun _ => H) =
      realJetMatrix (fun d => MvPolynomial.monomial
        (kernelExponentEmbedding G (PrincipalTupleIndex B (layerSamplerDegree I n)) (j.val + 1) d).val 1)
        (normalizedCubeTuple input fixedReal y) rows := by
  have ht := normalizedMappedKernelJet_eq (j.val + 1) input fixedReal y x (fun _ _ => rfl) rows hH
  exact normalizedIntegerColumns_eq_of_instances ht

theorem allocatedMonomialProfile_unit_law (j : Fin m)
    (s : O ↪ BoundedIntegerExponent G (j.val + 1))
    (hA : ((scalarKernelIntegerJet x (j.val + 1) rows).submatrix id s).det ≠ 0)
    {H : ℝ} (hH : 0 < H)
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ)
    (c w : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℝ)
    (hw : ∀ e, 0 < w e) (L : ℝ≥0) (hbound : ∀ e, |c e| + w e ≤ L) :
    (unitCoefficientSource (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1))).map
        (originalMonomialJetMap Subtype.val input fixedReal rows c w y) =
      realDensityMeasure volume (affineSelectedJetDensity s
        (normalizedPivotEquiv ((scalarKernelIntegerJet x (j.val + 1) rows).submatrix id s) hA
          (fun o => kernelJetCoefficientScale G (j.val + 1) S.value H (s o)) (fun _ => H)
          (fun o => kernelJetCoefficientScale_pos G (j.val + 1) (Nat.cast_pos.mpr S.positive) hH (s o))
          (fun _ => hH))
        (matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns (scalarKernelIntegerJet x (j.val + 1) rows) s)
          (fun e => kernelJetCoefficientScale G (j.val + 1) S.value H e.val) (fun _ => H)))
        (allocatedNonkernelExponent B j) input fixedReal rows
        (c ∘ allocatedKernelCoefficientEquiv B j) (w ∘ allocatedKernelCoefficientEquiv B j) y) := by
  have hlaw := originalMonomialJetMap_unit_law
    (allocatedKernelCoefficientEquiv (G := G) B j) Subtype.val
    (scalarKernelIntegerJet x (j.val + 1) rows) s hA
    (kernelJetCoefficientScale G (j.val + 1) S.value H)
    (kernelJetCoefficientScale_pos G (j.val + 1) (Nat.cast_pos.mpr S.positive) hH)
    hH input fixedReal rows y
    (allocatedNormalizedKernelJet_eq B U basis S x u rows j y hH.ne') c w hw L hbound
  have he : (fun d : AllocatedNonkernelCoefficient (G := G) B j =>
      (allocatedKernelCoefficientEquiv (G := G) B j (.inr d)).val) =
      allocatedNonkernelExponent (G := G) B j := rfl
  rw [he] at hlaw
  exact hlaw

include hR hσ in
theorem allocatedContinuousProfileJet_unit_law (j : Fin m) (i : I j)
    (s : O ↪ BoundedIntegerExponent G (j.val + 1))
    (hA : ((scalarKernelIntegerJet x (j.val + 1) rows).submatrix id s).det ≠ 0)
    (hσ1 : σ j ≤ 1)
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ) :
    (unitCoefficientSource (SamplerCoefficientSlot G B (layerSamplerDegree I n) ⟨j, .inl i⟩)).map
        (allocatedNormalizedProfileJet B U basis S x u rows ⟨j, .inl i⟩ y) =
      realDensityMeasure volume (allocatedContinuousKernelDensity B U basis S j i x u rows s hA y) := by
  change (unitCoefficientSource (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1))).map
      (originalMonomialJetMap Subtype.val input fixedReal rows
        (allocatedContinuousProfileCenters (G := G) B R j i)
        (allocatedContinuousProfileWidths (G := G) B R σ j i) y) = _
  exact allocatedMonomialProfile_unit_law B U basis S x u rows j s hA zero_lt_one y
    (allocatedContinuousProfileCenters (G := G) B R j i)
    (allocatedContinuousProfileWidths (G := G) B R σ j i)
    (allocatedContinuousProfileWidths_pos B hR hσ j i) ⟨R j, (hR j).le⟩
    (allocatedContinuousProfile_bound B hR hσ j i hσ1)

include hR hσ in
theorem allocatedIntegerProfileJet_unit_law (j : Fin m) (i : Fin (n j))
    (s : O ↪ BoundedIntegerExponent G (j.val + 1))
    (hA : ((scalarKernelIntegerJet x (j.val + 1) rows).submatrix id s).det ≠ 0)
    (hσ1 : σ j ≤ 1)
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ) :
    (unitCoefficientSource (SamplerCoefficientSlot G B (layerSamplerDegree I n) ⟨j, .inr i⟩)).map
        (allocatedNormalizedProfileJet B U basis S x u rows ⟨j, .inr i⟩ y) =
      realDensityMeasure volume (allocatedIntegerKernelDensity B U basis S j i x u rows s hA y) := by
  have hH : 0 < (basisAxisScale (basis j) i : ℝ) := Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)
  change (unitCoefficientSource (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1))).map
      (originalMonomialJetMap Subtype.val input fixedReal rows
        (allocatedIntegerProfileCenters (G := G) B R j i)
        (allocatedIntegerProfileWidths (G := G) B R σ j i) y) = _
  exact allocatedMonomialProfile_unit_law B U basis S x u rows j s hA hH y
    (allocatedIntegerProfileCenters (G := G) B R j i)
    (allocatedIntegerProfileWidths (G := G) B R σ j i)
    (allocatedIntegerProfileWidths_pos B hR hσ j i) ⟨R j, (hR j).le⟩
    (allocatedKernelProfile_bound B hR hσ j i hσ1)

end Erdos3.VectorPolynomial

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

noncomputable def allocatedNormalizedLongJetFactor (y : activeInput → ℝ) :
    ∀ a : {a // ¬grid a}, (O a.val.1 → ℝ) → ℝ
  | ⟨⟨j, .inl i⟩, _⟩ => allocatedContinuousKernelDensity B U basis S j i x u (rows j) (s j) (hA j) y
  | ⟨⟨j, .inr i⟩, _⟩ => allocatedIntegerKernelDensity B U basis S j i x u (rows j) (s j) (hA j) y

noncomputable def allocatedNormalizedLongJetMap (y : activeInput → ℝ) :
    (activeCoefficient → ℝ) → (realOutput → ℝ) :=
  sigmaAxisSampler (fun a : {a // ¬grid a} =>
    allocatedNormalizedProfileJet B U basis S x u (rows a.val.1) a.val y)

noncomputable def allocatedNormalizedLongJetDensity (y : activeInput → ℝ) :
    (realOutput → ℝ) → ℝ :=
  sigmaAxisWeight (allocatedNormalizedLongJetFactor B U basis S x u rows s hA y)

noncomputable def allocatedContinuousLongJetProxy : (realOutput → ℝ) → ℝ :=
  densityMixture (jointBooleanSource (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val))
    (allocatedNormalizedLongJetDensity B U basis S x u rows s hA)

include hR hσ in
theorem allocatedNormalizedLongJetFactor_probability (hσ1 : ∀ j, σ j ≤ 1)
    (y : activeInput → ℝ) (a : {a // ¬grid a}) :
    (∀ v, 0 ≤ allocatedNormalizedLongJetFactor B U basis S x u rows s hA y a v) ∧
    Integrable (allocatedNormalizedLongJetFactor B U basis S x u rows s hA y a) ∧
    (∫ v, allocatedNormalizedLongJetFactor B U basis S x u rows s hA y a v) = 1 := by
  rcases a with ⟨⟨j, a⟩, ha⟩
  cases a with
  | inl i => exact allocatedContinuousKernelDensity_probability_data B U basis hR hσ S j i x u (rows j) (s j) (hA j) (hσ1 j) y
  | inr i => exact allocatedIntegerKernelDensity_probability_data B U basis hR hσ S j i x u (rows j) (s j) (hA j) (hσ1 j) y

include hR hσ in
theorem allocatedNormalizedLongJetFactor_measurable (hσ1 : ∀ j, σ j ≤ 1)
    (a : {a // ¬grid a}) :
    Measurable (fun p : (activeInput → ℝ) × (O a.val.1 → ℝ) =>
      allocatedNormalizedLongJetFactor B U basis S x u rows s hA p.1 a p.2) := by
  rcases a with ⟨⟨j, a⟩, ha⟩
  cases a with
  | inl i => exact allocatedContinuousKernelDensity_measurable B U basis hR hσ S j i x u (rows j) (s j) (hA j) (hσ1 j)
  | inr i => exact allocatedIntegerKernelDensity_measurable B U basis hR hσ S j i x u (rows j) (s j) (hA j) (hσ1 j)

omit [∀ j, DecidableEq (O j)] in
theorem allocatedNormalizedLongJetMap_measurable :
    Measurable (fun p : (activeInput → ℝ) × (activeCoefficient → ℝ) =>
      allocatedNormalizedLongJetMap B U basis S x u rows p.1 p.2) := by
  unfold allocatedNormalizedLongJetMap sigmaAxisSampler
  apply Measurable.of_eval
  intro o
  have hc : Measurable (fun p : (activeInput → ℝ) × (activeCoefficient → ℝ) =>
      (p.1, fun e : SamplerCoefficientSlot G B (layerSamplerDegree I n) o.1.val => p.2 ⟨o.1, e⟩)) :=
    measurable_fst.prodMk (Measurable.of_eval (fun e =>
      (measurable_pi_apply (⟨o.1, e⟩ : activeCoefficient)).comp measurable_snd))
  exact (measurable_pi_apply o.2).comp
    ((allocatedNormalizedProfileJet_measurable B U basis S x u (rows o.1.val.1) o.1.val).comp
      (f := fun p : (activeInput → ℝ) × (activeCoefficient → ℝ) =>
        (p.1, fun e => p.2 ⟨o.1, e⟩)) hc)

include hR hσ in
theorem allocatedNormalizedLongJetDensity_measurable (hσ1 : ∀ j, σ j ≤ 1) :
    Measurable (Function.uncurry (allocatedNormalizedLongJetDensity B U basis S x u rows s hA)) := by
  change Measurable (fun p : (activeInput → ℝ) × (realOutput → ℝ) =>
    ∏ a, allocatedNormalizedLongJetFactor B U basis S x u rows s hA p.1 a (fun o => p.2 ⟨a, o⟩))
  apply Finset.measurable_prod
  intro a _
  have hc : Measurable (fun p : (activeInput → ℝ) × (realOutput → ℝ) =>
      (p.1, fun o : O a.val.1 => p.2 ⟨a, o⟩)) :=
    measurable_fst.prodMk (Measurable.of_eval (fun o =>
      (measurable_pi_apply (⟨a, o⟩ : realOutput)).comp measurable_snd))
  exact (allocatedNormalizedLongJetFactor_measurable B U basis hR hσ S x u rows s hA hσ1 a).comp
    (f := fun p : (activeInput → ℝ) × (realOutput → ℝ) => (p.1, fun o => p.2 ⟨a, o⟩)) hc

include hR hσ in
theorem allocatedNormalizedLongJetDensity_probability (hσ1 : ∀ j, σ j ≤ 1)
    (y : activeInput → ℝ) :
    (∀ v, 0 ≤ allocatedNormalizedLongJetDensity B U basis S x u rows s hA y v) ∧
    Integrable (allocatedNormalizedLongJetDensity B U basis S x u rows s hA y) ∧
    (∫ v, allocatedNormalizedLongJetDensity B U basis S x u rows s hA y v) = 1 := by
  have hp := allocatedNormalizedLongJetFactor_probability B U basis hR hσ S x u rows s hA hσ1 y
  have hm : (∫ v, allocatedNormalizedLongJetDensity B U basis S x u rows s hA y v) = 1 := by
    unfold allocatedNormalizedLongJetDensity
    rw [sigmaAxisWeight_integral]
    exact Finset.prod_eq_one (fun a _ => (hp a).2.2)
  exact ⟨sigmaAxisWeight_nonneg _ (fun a => (hp a).1),
    Integrable.of_integral_ne_zero (hm.trans_ne one_ne_zero), hm⟩

include hR hσ in
theorem allocatedNormalizedLongJetDensity_unit_law (hσ1 : ∀ j, σ j ≤ 1)
    (y : activeInput → ℝ) :
    (unitCoefficientSource activeCoefficient).map
        (allocatedNormalizedLongJetMap B U basis S x u rows y) =
      realDensityMeasure volume (allocatedNormalizedLongJetDensity B U basis S x u rows s hA y) := by
  have hm (a : {a // ¬grid a}) :
      Measurable (allocatedNormalizedProfileJet B U basis S x u (rows a.val.1) a.val y) :=
    Measurable.of_uncurry_left
      (f := allocatedNormalizedProfileJet B U basis S x u (rows a.val.1) a.val) (x := y)
      (allocatedNormalizedProfileJet_measurable B U basis S x u (rows a.val.1) a.val)
  have hlaw (a : {a // ¬grid a}) :
      (unitCoefficientSource (SamplerCoefficientSlot G B (layerSamplerDegree I n) a.val)).map
          (allocatedNormalizedProfileJet B U basis S x u (rows a.val.1) a.val y) =
        realDensityMeasure volume (allocatedNormalizedLongJetFactor B U basis S x u rows s hA y a) := by
    rcases a with ⟨⟨j, a⟩, ha⟩
    cases a with
    | inl i => exact allocatedContinuousProfileJet_unit_law B U basis hR hσ S x u (rows j) j i (s j) (hA j) (hσ1 j) y
    | inr i => exact allocatedIntegerProfileJet_unit_law B U basis hR hσ S x u (rows j) j i (s j) (hA j) (hσ1 j) y
  unfold allocatedNormalizedLongJetMap
  rw [unitCoefficientSource_sigma, sigmaAxisSampler_image_law _ _ hm]
  simp_rw [hlaw]
  have hp := allocatedNormalizedLongJetFactor_probability B U basis hR hσ S x u rows s hA hσ1 y
  exact sigmaAxisMeasure_density _ (fun a => (hp a).2.1) (fun a => (hp a).1)

include hR hσ in
theorem allocatedContinuousLongJetProxy_image_law (hσ1 : ∀ j, σ j ≤ 1) :
    ((jointBooleanSource (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val)).prod
      (unitCoefficientSource activeCoefficient)).map
        (fun p => allocatedNormalizedLongJetMap B U basis S x u rows p.1 p.2) =
      realDensityMeasure volume (allocatedContinuousLongJetProxy B U basis S x u rows s hA) :=
  densityMixture_image_law _ _ _ _
    (allocatedNormalizedLongJetMap_measurable B U basis S x u rows) _
    (allocatedNormalizedLongJetDensity_measurable B U basis hR hσ S x u rows s hA hσ1)
    (allocatedNormalizedLongJetDensity_probability B U basis hR hσ S x u rows s hA hσ1)
    (allocatedNormalizedLongJetDensity_unit_law B U basis hR hσ S x u rows s hA hσ1)

include hR hσ in
theorem allocatedContinuousLongJetProxy_probability (hσ1 : ∀ j, σ j ≤ 1) :
    (∀ v, 0 ≤ allocatedContinuousLongJetProxy B U basis S x u rows s hA v) ∧
    Integrable (allocatedContinuousLongJetProxy B U basis S x u rows s hA) ∧
    (∫ v, allocatedContinuousLongJetProxy B U basis S x u rows s hA v) = 1 :=
  densityMixture_probability_density _ _ _
    (allocatedNormalizedLongJetDensity_measurable B U basis hR hσ S x u rows s hA hσ1)
    (Filter.Eventually.of_forall
      (allocatedNormalizedLongJetDensity_probability B U basis hR hσ S x u rows s hA hσ1))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem principalAxisParameter_card_le {D α : Type*} [Fintype D] [Fintype α]
    (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ)
    (P : D → Prop) [DecidablePred P] :
    Fintype.card (PrincipalAxisParameter (B := B) (h := h) (α := α) P) ≤
      Fintype.card (JointBlockParameter B h α) := by
  apply Fintype.card_le_of_injective
    (fun z : PrincipalAxisParameter (B := B) (h := h) (α := α) P =>
      (⟨z.1.val, z.2⟩ : JointBlockParameter B h α))
  intro a b hab
  rcases a with ⟨⟨a, ha⟩, x⟩
  rcases b with ⟨⟨b, hb⟩, y⟩
  cases hab
  rfl

theorem principalAxisColumnLip_le_exp {D α : Type*} [Fintype D] [Fintype α]
    (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ)
    (P : D → Prop) [DecidablePred P] (n d : ℕ) :
    (n : ℝ) * polynomialBoxLip
        (Fintype.card (PrincipalAxisParameter (B := B) (h := h) (α := α) P))
        d (normalizedJetMass α d) ≤
      Real.exp (n + 3*(Fintype.card (JointBlockParameter B h α) : ℝ)*d +
        (Fintype.card α : ℝ)*(d+1)) := by
  apply (normalizedJetColumnLip_le_exp α n _ d).trans
  apply Real.exp_le_exp.mpr
  have hc := principalAxisParameter_card_le (α := α) B h P
  gcongr

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedDensityColumnLog (α : Type*) [Fintype α] (j : Fin m) : ℝ :=
  Fintype.card (AllocatedNonkernelCoefficient (G := G) B j) +
    3*(Fintype.card (JointBlockParameter B (layerSamplerDegree I n) α) : ℝ)*(j.val+1) +
    (Fintype.card α : ℝ)*(j.val+2)

noncomputable def allocatedDensityLog (α : Type*) [Fintype α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] (P : ℝ) : ℝ :=
  kernelFamilyOutputLog (α := α) (J := G) O
      (AllocatedNonkernelCoefficient (G := G) B) (fun j => j.val+1) (4*(P+8)) +
    P + ∑ j, allocatedDensityColumnLog (G := G) B α j

theorem allocatedDensityLog_bounds (α : Type*) [Fintype α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] {P : ℝ} (hP : 0 ≤ P) :
    let K := kernelFamilyOutputLog (α := α) (J := G) O
      (AllocatedNonkernelCoefficient (G := G) B) (fun j => j.val+1) (4*(P+8))
    0 ≤ allocatedDensityLog (G := G) B α O P ∧
      K ≤ allocatedDensityLog (G := G) B α O P ∧
      ∀ j, K + allocatedDensityColumnLog (G := G) B α j + P ≤
        allocatedDensityLog (G := G) B α O P := by
  dsimp only
  have hK := kernelFamilyOutputLog_nonneg (α := α) (J := G) O
    (AllocatedNonkernelCoefficient (G := G) B) (fun j => j.val+1)
    (show 0 ≤ 4*(P+8) by positivity)
  have hj (j : Fin m) : 0 ≤ allocatedDensityColumnLog (G := G) B α j := by
    unfold allocatedDensityColumnLog
    positivity
  have hs := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hj j)
  unfold allocatedDensityLog
  refine ⟨by positivity, by linarith, ?_⟩
  intro j
  have h := Finset.single_le_sum (fun k _ => hj k) (Finset.mem_univ j)
  linarith

end VectorPolynomial
end Erdos3

end

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
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {M : ℕ} (hM : 0 < M)
variable (hi : ∀ j : Fin m,
  fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMP : (M : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m,
  (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "budget" => allocatedDensityLog (G := G) B α O P
local notation "bound" => NNReal.mk (Real.exp budget) (le_of_lt (Real.exp_pos budget))
local notation "radius" j => NNReal.mk (R j) (le_of_lt (hR j))
local notation "delta" j => NNReal.mk
  (allocatedUnitProfileWidth (R j) (σ j)
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (Fin.val j+1))))
  (le_of_lt (allocatedUnitProfileWidth_pos (hR j) (hσ j) _))

include hR hσ hM hi hP hMP hRP hRi hσi hcount

theorem allocatedDensityKernel_bounds (j : Fin m) {H : ℝ} (hH : 0 < H) :
    let E := normalizedPivotEquiv _ (hA j)
      (fun o => kernelJetCoefficientScale G (j.val+1) S.value H (s j o)) (fun _ => H)
      (fun o => kernelJetCoefficientScale_pos G (j.val+1) (Nat.cast_pos.mpr S.positive) hH (s j o))
      (fun _ => hH)
    pivotKernelCap (UnselectedColumn (s j)) E (radius j)
        ((delta j)⁻¹^Fintype.card (BoundedIntegerExponent G (j.val+1))) ≤ bound ∧
      pivotKernelLip (UnselectedColumn (s j)) E (radius j)
          (affineProductProfileLip (BoundedIntegerExponent G (j.val+1)) (delta j)) *
        (Fintype.card (AllocatedNonkernelCoefficient (G := G) B j) *
          polynomialBoxLip
            (Fintype.card (PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
              (α := α) (fun a => ¬grid a))) (j.val+1) (normalizedJetMass α (j.val+1))) *
        (radius j) ≤ bound := by
  dsimp only
  have hp' : 0 ≤ 4*(P+8) := by positivity
  have hPP : Real.exp P ≤ Real.exp (4*(P+8)) := Real.exp_le_exp.mpr (by linarith)
  have hb := allocatedDensityLog_bounds (G := G) B α O hP
  have hf := fixedKernel_family_output_bound (N := AllocatedNonkernelCoefficient (G := G) B)
    S.positive hM x (fun j : Fin m => j.val+1) rows s hA hi
    (fun j => delta j) (fun j => radius j)
    (fun j => allocatedUnitProfileWidth_pos (hR j) (hσ j) _) hp' (hMP.trans hPP)
    (fun j => (hRP j).trans hPP)
    (fun j => allocatedUnitProfileWidth_inverse_exp _ hP (hR j) (hσ j) (hRi j) (hσi j) (hcount j))
    (fun _ => H) (fun _ => hH)
  let K := kernelFamilyOutputLog (α := α) (J := G) O
    (AllocatedNonkernelCoefficient (G := G) B) (fun j => j.val+1) (4*(P+8))
  constructor
  · exact (hf.2.1 j).trans (by exact_mod_cast Real.exp_le_exp.mpr hb.2.1)
  · apply NNReal.coe_le_coe.mp
    have hmid :
        (Fintype.card (AllocatedNonkernelCoefficient (G := G) B j) : ℝ) *
          polynomialBoxLip
            (Fintype.card (PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
              (α := α) (fun a => ¬grid a))) (j.val+1) (normalizedJetMass α (j.val+1)) ≤
        Real.exp (allocatedDensityColumnLog (G := G) B α j) := by
      convert principalAxisColumnLip_le_exp (α := α) B (layerSamplerDegree I n)
        (fun a => ¬grid a) (Fintype.card (AllocatedNonkernelCoefficient (G := G) B j)) (j.val+1) using 1
      congr 1
      simp only [allocatedDensityColumnLog, Nat.cast_add, Nat.cast_one]
      ring
    have hlip := hf.2.2.1 j
    have hlip' := NNReal.coe_le_coe.mpr hlip
    simp only [NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_mk]
    calc
      _ ≤ Real.exp K * Real.exp (allocatedDensityColumnLog (G := G) B α j) * Real.exp P :=
        mul_le_mul (mul_le_mul hlip' hmid (by positivity) (Real.exp_pos _).le)
          (hRP j) (hR j).le (by positivity)
      _ = Real.exp (K + allocatedDensityColumnLog (G := G) B α j + P) := by
        rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ Real.exp budget := Real.exp_le_exp.mpr (hb.2.2 j)

variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

theorem allocatedContinuousKernelDensity_exp_bounds (hσ1 : ∀ j, σ j ≤ 1)
    (j : Fin m) (i : I j) (z : O j → ℝ) :
    (∀ y, |allocatedContinuousKernelDensity B U basis S j i x u (rows j) (s j) (hA j) y z| ≤ bound) ∧
      LipschitzOnWith bound
        (fun y => allocatedContinuousKernelDensity B U basis S j i x u (rows j) (s j) (hA j) y z)
        (Metric.closedBall 0 1) := by
  have hb := allocatedDensityKernel_bounds B U basis hR hσ S x rows s hA hM hi hP hMP hRP hRi hσi hcount j zero_lt_one
  have hd := allocatedContinuousKernelDensity_bounds B U basis hR hσ S j i x u (rows j) (s j) (hA j) (hσ1 j) z
  exact ⟨fun y => (hd.1 y).trans (by exact_mod_cast hb.1), hd.2.weaken hb.2⟩

theorem allocatedIntegerKernelDensity_exp_bounds (hσ1 : ∀ j, σ j ≤ 1)
    (j : Fin m) (i : Fin (n j)) (z : O j → ℝ) :
    (∀ y, |allocatedIntegerKernelDensity B U basis S j i x u (rows j) (s j) (hA j) y z| ≤ bound) ∧
      LipschitzOnWith bound
        (fun y => allocatedIntegerKernelDensity B U basis S j i x u (rows j) (s j) (hA j) y z)
        (Metric.closedBall 0 1) := by
  have hb := allocatedDensityKernel_bounds B U basis hR hσ S x rows s hA hM hi hP hMP hRP hRi hσi hcount j
    (Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i))
  have hd := allocatedIntegerKernelDensity_bounds B U basis hR hσ S j i x u (rows j) (s j) (hA j) (hσ1 j) z
  exact ⟨fun y => (hd.1 y).trans (by exact_mod_cast hb.1), hd.2.weaken hb.2⟩

theorem allocatedLongJetTarget_exp_bounds (hσ1 : ∀ j, σ j ≤ 1) :
    1 ≤ bound ∧
      (∀ y a z, |allocatedLongJetTarget B U basis S x u rows s hA y a z| ≤ bound) ∧
      (∀ a z, LipschitzOnWith bound
        (fun y => allocatedLongJetTarget B U basis S x u rows s hA y a z) (Metric.closedBall 0 1)) := by
  have hrow (a : {a // ¬grid a}) (z : CoefficientJetAxisRow O a.val) :
      (∀ y, |allocatedLongJetTarget B U basis S x u rows s hA y a z| ≤ bound) ∧
        LipschitzOnWith bound (fun y => allocatedLongJetTarget B U basis S x u rows s hA y a z)
          (Metric.closedBall 0 1) := by
    rcases a with ⟨⟨j, a⟩, ha⟩
    cases a with
    | inl i =>
      exact allocatedContinuousKernelDensity_exp_bounds B U basis hR hσ S x rows s hA
        hM hi hP hMP hRP hRi hσi hcount u hσ1 j i z
    | inr i =>
      exact allocatedIntegerKernelDensity_exp_bounds B U basis hR hσ S x rows s hA
        hM hi hP hMP hRP hRi hσi hcount u hσ1 j i
        (fun o => (z o : ℝ)/(basisAxisScale (basis j) i : ℝ))
  refine ⟨?_, fun y a z => (hrow a z).1 y, fun a z => (hrow a z).2⟩
  exact_mod_cast Real.one_le_exp_iff.mpr (allocatedDensityLog_bounds (G := G) B α O hP).1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators NNReal Classical

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

include hR hσ hM hi hP hMP hRP hRi hσi hcount

theorem allocatedNormalizedLongJetDensity_parameter_bounds (hσ1 : ∀ j, σ j ≤ 1)
    (z : (Σ a : {a // ¬grid a}, O a.val.1) → ℝ) :
    (∀ y, |allocatedNormalizedLongJetDensity B U basis S x u rows s hA y z| ≤ cap) ∧
    LipschitzOnWith lip (fun y => allocatedNormalizedLongJetDensity B U basis S x u rows s hA y z)
      (Metric.closedBall 0 1) := by
  let f := fun (a : {a // ¬grid a}) y =>
    allocatedNormalizedLongJetFactor B U basis S x u rows s hA y a (fun o => z ⟨a,o⟩)
  have hrow (a : {a // ¬grid a}) :
      (∀ y, |f a y| ≤ bound) ∧ LipschitzOnWith bound (f a) (Metric.closedBall 0 1) := by
    rcases a with ⟨⟨j,a⟩,ha⟩
    cases a with
    | inl i =>
      exact allocatedContinuousKernelDensity_exp_bounds B U basis hR hσ S x rows s hA
        hM hi hP hMP hRP hRi hσi hcount u hσ1 j i _
    | inr i =>
      exact allocatedIntegerKernelDensity_exp_bounds B U basis hR hσ S x rows s hA
        hM hi hP hMP hRP hRi hσi hcount u hσ1 j i _
  have hbound : 1 ≤ bound := by
    exact_mod_cast Real.one_le_exp_iff.mpr (allocatedDensityLog_bounds (G := G) B α O hP).1
  have hc : Fintype.card {a // ¬grid a} ≤ Fintype.card (LayerSamplerAxis I n) :=
    Fintype.card_subtype_le _
  have hpow : bound ^ Fintype.card {a // ¬grid a} ≤ cap := pow_le_pow_right₀ hbound hc
  have hcn : (Fintype.card {a // ¬grid a} : ℝ≥0) ≤ Fintype.card (LayerSamplerAxis I n) := by
    exact_mod_cast hc
  have hlip : (Fintype.card {a // ¬grid a} : ℝ≥0) * bound * bound ^ Fintype.card {a // ¬grid a} ≤ lip :=
    mul_le_mul (mul_le_mul_of_nonneg_right hcn zero_le) hpow zero_le zero_le
  have hb := finiteProduct_cap f (NNReal.coe_nonneg bound) (fun a => (hrow a).1)
  have hl := finiteProduct_lipschitzOn f (Metric.closedBall 0 1) bound bound hbound
    (fun a => (hrow a).2) (fun a y _ => (hrow a).1 y)
  exact ⟨fun y => (hb y).trans (NNReal.coe_le_coe.mpr hpow), hl.weaken hlip⟩

end Erdos3.VectorPolynomial

end

end OAI
