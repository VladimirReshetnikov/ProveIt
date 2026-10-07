import OAI.Combinatorics.Progressions.Estimates.AllocatedSlicedEndpointComparison

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {D : Type*} [Fintype D] {B F : D → Type*}
variable [∀ d, Fintype (B d)] [∀ d, Fintype (F d)]
variable [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (F d)]
variable (hB : ∀ d, 4 ≤ Fintype.card (B d)) (i : ∀ d, F d)

noncomputable def jointSlicedPrincipalDensity (c : ∀ d, B d → ℝ)
    (lower width : ∀ d, B d × F d → ℝ) (shift : D → ℝ) : ((Σ _d : D, Unit) → ℝ) → ℝ :=
  sigmaAxisWeight (fun d (v : Unit → ℝ) => canonicalSlicedPrincipalDensity (hB d) (i d)
    (c d) (lower d) (width d) (v () - shift d))

theorem jointSlicedPrincipalDensity_image_probability
    (c : ∀ d, B d → ℝ) (lower width : ∀ d, B d × F d → ℝ) (shift : D → ℝ)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hc : ∀ d b, a ≤ |c d b|) (hw : ∀ d p, δ ≤ width d p) (hl : ∀ d p, 0 ≤ lower d p) :
    (unitBoxMeasure (Σ d, B d × F d)).map
      (fun x => (fun o : Σ _d : D, Unit => shift o.1) + jointSlicedPrincipal c lower width x) =
        realDensityMeasure volume (jointSlicedPrincipalDensity hB i c lower width shift) ∧
      (∀ y, 0 ≤ jointSlicedPrincipalDensity hB i c lower width shift y) ∧
      Integrable (jointSlicedPrincipalDensity hB i c lower width shift) ∧
      (∫ y, jointSlicedPrincipalDensity hB i c lower width shift y) = 1 := by
  have hs (d) := canonicalSlicedPrincipalDensity_law_bounds (hB d) (i d) (c d) (lower d) (width d)
    ha hδ (hc d) (hw d) (hl d)
  have hmass : (∫ y, jointSlicedPrincipalDensity hB i c lower width shift y) = 1 := by
    rw [jointSlicedPrincipalDensity, sigmaAxisWeight_integral]
    apply Finset.prod_eq_one
    intro d _
    rw [unit_lift_integral (fun y => canonicalSlicedPrincipalDensity (hB d) (i d)
      (c d) (lower d) (width d) (y - shift d)), integral_sub_right_eq_self]
    exact (hs d).2.2.2.2
  refine ⟨?_, sigmaAxisWeight_nonneg _ (fun d y => ((hs d).2.1 _).1),
    Integrable.of_integral_ne_zero (hmass.trans_ne one_ne_zero), hmass⟩
  exact scalarJoint_image_density (fun d => principalSliceValue (c d) (lower d) (width d))
    (fun d => principalSliceValue_measurable _ _ _)
    (fun d => canonicalSlicedPrincipalDensity (hB d) (i d) (c d) (lower d) (width d))
    (fun d => (hs d).2.2.2.1) (fun d y => ((hs d).2.1 y).1) (fun d => (hs d).2.2.2.2)
    (fun d => (hs d).1) shift

theorem jointSlicedPrincipalDensity_measurable_family
    {P : Type*} [MeasurableSpace P]
    (c : P → ∀ d, B d → ℝ) (lower width : P → ∀ d, B d × F d → ℝ) (shift : P → D → ℝ)
    (hc : ∀ d b, Measurable (fun p => c p d b))
    (hl : ∀ d j, Measurable (fun p => lower p d j))
    (hw : ∀ d j, Measurable (fun p => width p d j))
    (hs : ∀ d, Measurable (fun p => shift p d)) :
    Measurable (fun p : P × ((Σ _d : D, Unit) → ℝ) =>
      jointSlicedPrincipalDensity hB i (c p.1) (lower p.1) (width p.1) (shift p.1) p.2) := by
  let _ : ∀ index, DecidableEq (B index) := inferInstance
  unfold jointSlicedPrincipalDensity sigmaAxisWeight tensorCutoffWeight
  apply Finset.measurable_prod
  intro d _
  have hf := canonicalSlicedPrincipalDensity_measurable_family (hB d) (i d)
    (fun p => c p d) (fun p => lower p d) (fun p => width p d) (hc d) (hl d) (hw d)
  have harg : Measurable (fun p : P × ((Σ _d : D, Unit) → ℝ) =>
      (p.1, p.2 ⟨d, ()⟩ - shift p.1 d)) := measurable_fst.prodMk
    (((measurable_pi_apply (⟨d, ()⟩ : Σ _d : D, Unit)).comp measurable_snd).sub
      ((hs d).comp measurable_fst))
  have he := hf.comp harg
  exact he

theorem jointSlicedPrincipalDensity_coordinate_product
    (c : ∀ d, B d → ℝ) (lower width : ∀ d, B d × F d → ℝ) (shift : D → ℝ) :
    jointSlicedPrincipalDensity hB i c lower width shift =
      independentCoordinateDensity (fun o : Σ _d : D, Unit =>
        fun y => canonicalSlicedPrincipalDensity (hB o.1) (i o.1) (c o.1) (lower o.1) (width o.1)
          (y - shift o.1)) := by
  let _ : ∀ index, DecidableEq (B index) := inferInstance
  funext y
  simp [jointSlicedPrincipalDensity, sigmaAxisWeight, tensorCutoffWeight,
    independentCoordinateDensity, Fintype.prod_sigma, sigmaAxisCoordinates]

theorem jointSlicedPrincipalDensity_cap_lipschitz
    (c : ∀ d, B d → ℝ) (lower width : ∀ d, B d × F d → ℝ) (shift : D → ℝ)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hc : ∀ d b, a ≤ |c d b|) (hw : ∀ d p, δ ≤ width d p) (hl : ∀ d p, 0 ≤ lower d p) :
    let K := fun d => SlicedProductBlock.uniformCap {j : F d // j ≠ i d}
      (a * δ ^ (Fintype.card {j : F d // j ≠ i d} + 1)) (mul_pos ha (pow_pos hδ _))
    (∀ y, jointSlicedPrincipalDensity hB i c lower width shift y ∈ Set.Icc (0 : ℝ) (∏ d, K d)) ∧
      LipschitzWith ((∏ d, (K d + 1)) * ∑ d, K d * (2 * K d))
        (jointSlicedPrincipalDensity hB i c lower width shift) := by
  intro K
  have hd (d) := canonicalSlicedPrincipalDensity_law_bounds (hB d) (i d) (c d) (lower d) (width d)
    ha hδ (hc d) (hw d) (hl d)
  let f := fun (o : Σ _d : D, Unit) (y : ℝ) =>
    canonicalSlicedPrincipalDensity (hB o.1) (i o.1) (c o.1) (lower o.1) (width o.1) (y - shift o.1)
  have hcap (o : Σ _d : D, Unit) (y : ℝ) : f o y ∈ Set.Icc (0 : ℝ) (K o.1) := (hd o.1).2.1 _
  have hLip (o : Σ _d : D, Unit) : LipschitzWith (K o.1 * (2 * K o.1)) (f o) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have he := ((hd o.1).2.2.1).dist_le_mul (x - shift o.1) (y - shift o.1)
    simpa only [dist_sub_right] using he
  rw [jointSlicedPrincipalDensity_coordinate_product]
  have hcap' := independentCoordinateDensity_cap f (fun o => (K o.1 : ℝ)) hcap
  have hLip' := independentCoordinateDensity_lipschitz f (fun o => K o.1) (fun o => K o.1 * (2 * K o.1)) hcap hLip
  constructor
  · simpa only [Fintype.prod_sigma, Fintype.prod_unique, NNReal.coe_prod] using hcap'
  · simpa only [Fintype.prod_sigma, Fintype.prod_unique, Fintype.sum_sigma, Fintype.sum_unique] using hLip'

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedAxisProfilePolynomial_principal_coeff
    (R σ : Fin m → ℝ) (a : LayerSamplerAxis I n)
    (r : SamplerCoefficientSlot G B (layerSamplerDegree I n) a → ℝ) (b : B a) :
    (allocatedAxisProfilePolynomial B R σ a r).coeff
        (canonicalPrincipalExponent (layerSamplerDegree I n) a b) =
      3 * principalProfileSize (R a.1) (Fintype.card (B a)) / 2 +
        principalProfileSize (R a.1) (Fintype.card (B a)) / 2 *
          r (principalCoefficientSlot (layerSamplerDegree I n) a b) := by
  rw [allocatedAxisProfilePolynomial_eq]
  change (monomialArrayPolynomial Subtype.val _).coeff
    (principalCoefficientSlot (layerSamplerDegree I n) a b).val = _
  rw [monomialArrayPolynomial_coeff Subtype.val Subtype.val_injective]
  have hp : principalCoefficientSlot (layerSamplerDegree I n) a b ∈
      principalCoefficientSlots (G := G) (layerSamplerDegree I n) a :=
    (mem_principalCoefficientSlots _ _ _).mpr ⟨b, rfl⟩
  have hz : principalCoefficientSlot (G := G) (layerSamplerDegree I n) a b ≠
      constantCoefficientSlot _ _ := by
    intro hz
    exact constantCoefficientSlot_not_principal (layerSamplerDegree I n) a
      (Nat.zero_lt_succ _) (hz ▸ hp)
  simp only [coefficientProfileCenter, coefficientProfileWidth, hp, hz, ite_true, ite_false]

theorem allocatedAxisProfilePolynomial_constant_coeff
    (R σ : Fin m → ℝ) (a : LayerSamplerAxis I n)
    (r : SamplerCoefficientSlot G B (layerSamplerDegree I n) a → ℝ) :
    (allocatedAxisProfilePolynomial B R σ a r).coeff 0 =
      R a.1 / 4 * r (constantCoefficientSlot _ _) := by
  rw [allocatedAxisProfilePolynomial_eq]
  change (monomialArrayPolynomial Subtype.val _).coeff
    (constantCoefficientSlot (LayerSamplerVariables G I n B) (layerSamplerDegree I n a)).val = _
  rw [monomialArrayPolynomial_coeff Subtype.val Subtype.val_injective]
  simp only [coefficientProfileCenter, coefficientProfileWidth,
    constantCoefficientSlot_not_principal (layerSamplerDegree I n) a (Nat.zero_lt_succ _),
    ite_false, ite_true, zero_add]

variable [∀ a, DecidableEq (B a)]
variable (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
variable (R σ : Fin m → ℝ)

local notation "degree" => layerSamplerDegree I n
local notation "Active" => {a // ¬P a}
local notation "Coeff" => ActiveProfileCoefficientIndex G B degree P
local notation "Input" => (Σ a : {a : LayerSamplerAxis I n // ¬P a},
  B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)

noncomputable def allocatedFixedPathPrincipal
    (r : Coeff → ℝ) (a : Active) (b : B a.val) : ℝ :=
  (allocatedAxisProfilePolynomial B R σ a.val (fun e => r ⟨a, e⟩)).coeff
    (canonicalPrincipalExponent degree a.val b) / R a.val.1

noncomputable def allocatedFixedPathShift (r : Coeff → ℝ) (a : Active) : ℝ :=
  (allocatedAxisProfilePolynomial B R σ a.val (fun e => r ⟨a, e⟩)).coeff 0 / R a.val.1

omit [∀ a, DecidableEq (B a)] [DecidablePred P] in
theorem allocatedFixedPathPrincipal_eq (hR : ∀ j, R j ≠ 0) (r : Coeff → ℝ) :
    allocatedFixedPathPrincipal B P R σ r =
      jointSlicedProfilePrincipal degree Subtype.val (unitProfilePrincipalSize (B := B))
        (fun a e => r ⟨a, e⟩) := by
  funext a b
  rw [allocatedFixedPathPrincipal, allocatedAxisProfilePolynomial_principal_coeff]
  have hs : principalProfileSize (R a.val.1) (Fintype.card (B a.val)) =
      R a.val.1 * unitProfilePrincipalSize (B := B) a.val := by
    simpa only [unitProfilePrincipalSize, mul_one] using
      principalProfileSize_mul (R a.val.1) 1 (Fintype.card (B a.val))
  rw [hs]
  unfold jointSlicedProfilePrincipal
  field_simp [hR]

omit [∀ a, DecidableEq (B a)] [DecidablePred P] in
theorem allocatedFixedPathShift_eq (hR : ∀ j, R j ≠ 0) (r : Coeff → ℝ) :
    allocatedFixedPathShift B P R σ r =
      fun a => (1 / 4 : ℝ) * r ⟨a, constantCoefficientSlot _ _⟩ := by
  funext a
  rw [allocatedFixedPathShift, allocatedAxisProfilePolynomial_constant_coeff]
  field_simp [hR]

noncomputable def allocatedFixedPathLiftMap
    (lower width : ∀ a : Active, B a.val × Fin (degree a.val) → ℝ)
    (r : Coeff → ℝ) (x : Input → ℝ) : Output → ℝ :=
  (fun o => allocatedFixedPathShift B P R σ r o.1) +
    jointSlicedPrincipal (allocatedFixedPathPrincipal B P R σ r) lower width x

noncomputable def allocatedFixedPathLiftDensity
    (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : Active, B a.val × Fin (degree a.val) → ℝ)
    (r : Coeff → ℝ) : (Output → ℝ) → ℝ :=
  jointSlicedPrincipalDensity hB (fun _ => ⟨0, Nat.zero_lt_succ _⟩)
    (allocatedFixedPathPrincipal B P R σ r) lower width (allocatedFixedPathShift B P R σ r)

theorem allocatedFixedPathPrincipal_bounds (hR : ∀ j, R j ≠ 0)
    (r : Coeff → ℝ) (hr : ∀ e, |r e| ≤ 1) (a : Active) (b : B a.val) :
    unitProfilePrincipalSize (B := B) a.val ≤ |allocatedFixedPathPrincipal B P R σ r a b| ∧
      |allocatedFixedPathPrincipal B P R σ r a b| ≤ 2 * unitProfilePrincipalSize (B := B) a.val := by
  let _ : ∀ axisIndex, DecidableEq (B axisIndex) := inferInstance
  let _ : DecidablePred P := inferInstance
  rw [allocatedFixedPathPrincipal_eq B P R σ hR]
  exact jointSlicedProfilePrincipal_unit_bounds degree Subtype.val
    (fun a e => r ⟨a, e⟩) (fun _ _ => hr _) a b

theorem allocatedFixedPathLiftDensity_law_probability
    (hR : ∀ j, R j ≠ 0) (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : Active, B a.val × Fin (degree a.val) → ℝ)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hprincipal : ∀ j : Active, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (r : Coeff → ℝ) (hr : ∀ e, |r e| ≤ 1) :
    (unitBoxMeasure Input).map (allocatedFixedPathLiftMap B P R σ lower width r) =
        realDensityMeasure volume (allocatedFixedPathLiftDensity B P R σ hB lower width r) ∧
      (∀ y, 0 ≤ allocatedFixedPathLiftDensity B P R σ hB lower width r y) ∧
      Integrable (allocatedFixedPathLiftDensity B P R σ hB lower width r) ∧
      (∫ y, allocatedFixedPathLiftDensity B P R σ hB lower width r y) = 1 := by
  exact jointSlicedPrincipalDensity_image_probability
    (D := Active) (B := fun j => B j.val) (F := fun j => Fin (degree j.val))
    hB (fun _ => ⟨0, Nat.zero_lt_succ _⟩)
    (allocatedFixedPathPrincipal B P R σ r) lower width
    (allocatedFixedPathShift B P R σ r) ha hδ
    (fun j b => (hprincipal j).trans
      (allocatedFixedPathPrincipal_bounds B P R σ hR r hr j b).1) hw hl

noncomputable def allocatedFixedPathLiftRowCap {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (j : Active) : ℝ≥0 :=
  SlicedProductBlock.uniformCap
    {k : Fin (degree j.val) // k ≠ ⟨0, Nat.zero_lt_succ _⟩}
    (a * δ ^ (Fintype.card {k : Fin (degree j.val) // k ≠ ⟨0, Nat.zero_lt_succ _⟩} + 1))
    (mul_pos ha (pow_pos hδ _))

theorem allocatedFixedPathLiftDensity_cap_lipschitz
    (hR : ∀ j, R j ≠ 0) (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : Active, B a.val × Fin (degree a.val) → ℝ)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hprincipal : ∀ j : Active, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (r : Coeff → ℝ) (hr : ∀ e, |r e| ≤ 1) :
    let K := allocatedFixedPathLiftRowCap P ha hδ
    (∀ y, allocatedFixedPathLiftDensity B P R σ hB lower width r y ∈
      Set.Icc (0 : ℝ) (∏ j, K j)) ∧
      LipschitzWith ((∏ j, (K j + 1)) * ∑ j, K j * (2 * K j))
        (allocatedFixedPathLiftDensity B P R σ hB lower width r) := by
  exact jointSlicedPrincipalDensity_cap_lipschitz
    (D := Active) (B := fun j => B j.val) (F := fun j => Fin (degree j.val))
    hB (fun _ => ⟨0, Nat.zero_lt_succ _⟩)
    (allocatedFixedPathPrincipal B P R σ r) lower width
    (allocatedFixedPathShift B P R σ r) ha hδ
    (fun j b => (hprincipal j).trans
      (allocatedFixedPathPrincipal_bounds B P R σ hR r hr j b).1) hw hl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Coeff" => ActiveProfileCoefficientIndex G B degree grid
local notation "Endpoint" => OneCubeActiveEndpoint (B := B) degree grid
local notation "Row" => OneCubeActiveRow grid
local notation "Output" => (Σ _e : Row, Unit)
local notation "axis" => (fun e : Row => Subtype.val (Prod.snd e))

noncomputable def allocatedSlicedNormalizedIdeal
    (lower width : ∀ a : {a // ¬grid a}, B a.val × Fin (degree a.val) → ℝ)
    (r : Coeff → ℝ) (y : Endpoint → ℝ) : Output → ℝ :=
  jointSlicedProfileShift degree axis (fun _ => 1 / 4) (fun e j => r ⟨e.2, j⟩) +
    jointSlicedPrincipal
      (jointSlicedProfilePrincipal degree axis (unitProfilePrincipalSize (B := B)) (fun e j => r ⟨e.2, j⟩))
      (fun e => lower e.2) (fun e => width e.2) y

noncomputable def allocatedSlicedConditionalIdealDensity
    (hB : ∀ a : {a // ¬grid a}, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : {a // ¬grid a}, B a.val × Fin (degree a.val) → ℝ)
    (r : Coeff → ℝ) : (Output → ℝ) → ℝ :=
  jointSlicedPrincipalDensity (fun e : Row => hB e.2) (fun _row => ⟨0, Nat.zero_lt_succ _⟩)
    (jointSlicedProfilePrincipal degree axis (unitProfilePrincipalSize (B := B)) (fun e j => r ⟨e.2, j⟩))
    (fun e => lower e.2) (fun e => width e.2) (fun e => (1 / 4 : ℝ) * r ⟨e.2, constantCoefficientSlot _ _⟩)

noncomputable def allocatedSlicedAveragedIdealDensity
    (hB : ∀ a : {a // ¬grid a}, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : {a // ¬grid a}, B a.val × Fin (degree a.val) → ℝ) : (Output → ℝ) → ℝ :=
  densityMixture (unitCoefficientSource Coeff) (allocatedSlicedConditionalIdealDensity B U basis S hB lower width)

theorem allocatedSlicedNormalizedIdeal_measurable
    (lower width : ∀ a : {a // ¬grid a}, B a.val × Fin (degree a.val) → ℝ) :
    Measurable (fun p : (Coeff → ℝ) × (Endpoint → ℝ) =>
      allocatedSlicedNormalizedIdeal B U basis S lower width p.1 p.2) := by
  let _ : ∀ axisIndex, DecidableEq (B axisIndex) := inferInstance
  unfold allocatedSlicedNormalizedIdeal jointSlicedProfileShift jointSlicedPrincipal sigmaAxisSampler
    principalSliceSingleton principalSliceValue jointSlicedProfilePrincipal
  fun_prop

theorem allocatedSlicedConditionalIdealDensity_measurable
    (hB : ∀ a : {a // ¬grid a}, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : {a // ¬grid a}, B a.val × Fin (degree a.val) → ℝ) :
    Measurable (Function.uncurry (allocatedSlicedConditionalIdealDensity B U basis S hB lower width)) := by
  have hc (e : Row) (b : B e.2.val) : Measurable (fun r : Coeff → ℝ =>
      jointSlicedProfilePrincipal degree axis (unitProfilePrincipalSize (B := B))
        (fun e j => r ⟨e.2, j⟩) e b) := by
    unfold jointSlicedProfilePrincipal
    fun_prop
  have hm := jointSlicedPrincipalDensity_measurable_family (fun e : Row => hB e.2)
    (fun e => (⟨0, Nat.zero_lt_succ _⟩ : Fin (degree e.2.val)))
    (fun r : Coeff → ℝ => jointSlicedProfilePrincipal degree axis (unitProfilePrincipalSize (B := B))
      (fun e j => r ⟨e.2, j⟩))
    (fun (_ : Coeff → ℝ) e => lower e.2) (fun (_ : Coeff → ℝ) e => width e.2)
    (fun (r : Coeff → ℝ) e => (1 / 4 : ℝ) * r ⟨e.2, constantCoefficientSlot _ _⟩)
    hc (fun _ _ => measurable_const) (fun _ _ => measurable_const)
    (fun e => measurable_const.mul (measurable_pi_apply _))
  exact hm

theorem allocatedSlicedConditionalIdealDensity_law_probability
    (hB : ∀ a : {a // ¬grid a}, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : {a // ¬grid a}, B a.val × Fin (degree a.val) → ℝ)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (r : Coeff → ℝ) (hr : ∀ j, |r j| ≤ 1) :
    (unitBoxMeasure Endpoint).map (allocatedSlicedNormalizedIdeal B U basis S lower width r) =
        realDensityMeasure volume (allocatedSlicedConditionalIdealDensity B U basis S hB lower width r) ∧
      (∀ y, 0 ≤ allocatedSlicedConditionalIdealDensity B U basis S hB lower width r y) ∧
      Integrable (allocatedSlicedConditionalIdealDensity B U basis S hB lower width r) ∧
      (∫ y, allocatedSlicedConditionalIdealDensity B U basis S hB lower width r y) = 1 := by
  have hc (e : Row) (b : B e.2.val) : a ≤
      |jointSlicedProfilePrincipal degree axis (unitProfilePrincipalSize (B := B))
        (fun e j => r ⟨e.2, j⟩) e b| :=
    (hprincipal e.2).trans (jointSlicedProfilePrincipal_unit_bounds degree axis
      (fun e j => r ⟨e.2, j⟩) (fun e j => hr _) e b).1
  exact jointSlicedPrincipalDensity_image_probability (fun e : Row => hB e.2)
    (fun e => ⟨0, Nat.zero_lt_succ _⟩) _ (fun e => lower e.2) (fun e => width e.2)
    (fun e => (1 / 4 : ℝ) * r ⟨e.2, constantCoefficientSlot _ _⟩) ha hδ hc (fun e => hw e.2) (fun e => hl e.2)

theorem allocatedSlicedAveragedIdealDensity_law_probability
    (hB : ∀ a : {a // ¬grid a}, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : {a // ¬grid a}, B a.val × Fin (degree a.val) → ℝ)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p) :
    ((unitCoefficientSource Coeff).prod (unitBoxMeasure Endpoint)).map
        (fun p => allocatedSlicedNormalizedIdeal B U basis S lower width p.1 p.2) =
        realDensityMeasure volume (allocatedSlicedAveragedIdealDensity B U basis S hB lower width) ∧
      (∀ y, 0 ≤ allocatedSlicedAveragedIdealDensity B U basis S hB lower width y) ∧
      Integrable (allocatedSlicedAveragedIdealDensity B U basis S hB lower width) ∧
      (∫ y, allocatedSlicedAveragedIdealDensity B U basis S hB lower width y) = 1 := by
  have hcond := allocatedSlicedConditionalIdealDensity_law_probability B U basis S hB lower width ha hδ hprincipal hw hl
  have hprob : ∀ᵐ r ∂unitCoefficientSource Coeff,
      (∀ y, 0 ≤ allocatedSlicedConditionalIdealDensity B U basis S hB lower width r y) ∧
      Integrable (allocatedSlicedConditionalIdealDensity B U basis S hB lower width r) ∧
      (∫ y, allocatedSlicedConditionalIdealDensity B U basis S hB lower width r y) = 1 :=
    (unitCoefficientSource_abs_le Coeff).mono (fun r hr => (hcond r hr).2)
  have hlaw := (unitCoefficientSource_abs_le Coeff).mono (fun r hr => (hcond r hr).1)
  have hm := allocatedSlicedConditionalIdealDensity_measurable B U basis S hB lower width
  refine ⟨?_, densityMixture_probability_density _ volume _ hm hprob⟩
  exact densityMixture_image_law_of_ae _ _ volume _
    (allocatedSlicedNormalizedIdeal_measurable B U basis S lower width) _ hm hprob hlaw

end Erdos3.VectorPolynomial

end

end OAI
