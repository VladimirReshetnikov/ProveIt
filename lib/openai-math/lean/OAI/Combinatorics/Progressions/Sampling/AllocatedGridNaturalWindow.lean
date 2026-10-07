/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Sampling.ForecastInactiveFixedSupport

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

theorem count_finset_indicator_data {X : Type*} [Countable X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (W : Finset X) :
    Integrable (fun x => (W : Set X).indicator (fun _ => (1 : ℝ)) x) Measure.count ∧
      (∫ x, (W : Set X).indicator (fun _ => (1 : ℝ)) x ∂Measure.count) = (W.card : ℝ) := by
  have hz (x : X) (hx : x ∉ W) : (W : Set X).indicator (fun _ => (1 : ℝ)) x = 0 :=
    Set.indicator_of_notMem hx _
  refine ⟨count_integrable_of_zero_off_finset W _ hz, ?_⟩
  rw [count_integral_eq_sum_of_zero_off_finset W _ hz]
  calc
    _ = ∑ _x ∈ W, (1 : ℝ) := Finset.sum_congr rfl (fun x hx => Set.indicator_of_mem hx _)
    _ = (W.card : ℝ) := by simp

end Erdos3

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (O : Fin m → Type*) [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)

noncomputable def allocatedGridWindowFactor
    (choose : {a // grid a} → Prop) [DecidablePred choose]
    (windows : ∀ a : {a // grid a}, Finset (CoefficientJetAxisRow O a.val))
    (laws : ∀ a : {a // grid a}, PMF (CoefficientJetAxisRow O a.val))
    (a : {a // grid a}) (z : CoefficientJetAxisRow O a.val) : ℝ := by
  exact if choose a then (windows a : Set (CoefficientJetAxisRow O a.val)).indicator
    (fun _ => (1 : ℝ)) z else (laws a z).toReal

noncomputable def allocatedGridWindowWeight
    (choose : {a // grid a} → Prop) [DecidablePred choose]
    (windows : ∀ a : {a // grid a}, Finset (CoefficientJetAxisRow O a.val))
    (laws : ∀ a : {a // grid a}, PMF (CoefficientJetAxisRow O a.val))
    (z : AllocatedFrozenJetRows B U b S O) : ℝ :=
  ∏ a, allocatedGridWindowFactor B U b S O choose windows laws a (z a)

omit [∀ j, Fintype (O j)] in
theorem allocatedGridWindowFactor_nonneg
    (selected : {a // grid a} → Prop) [DecidablePred selected]
    (W : ∀ a : {a // grid a}, Finset (CoefficientJetAxisRow O a.val))
    (p : ∀ a : {a // grid a}, PMF (CoefficientJetAxisRow O a.val))
    (a : {a // grid a}) (z : CoefficientJetAxisRow O a.val) :
    0 ≤ allocatedGridWindowFactor B U b S O selected W p a z := by
  unfold allocatedGridWindowFactor
  split_ifs
  · exact Set.indicator_nonneg (fun _ _ => zero_le_one) z
  · exact ENNReal.toReal_nonneg

omit [∀ j, Fintype (O j)] in
theorem allocatedGridWindowWeight_nonneg
    (selected : {a // grid a} → Prop) [DecidablePred selected]
    (W : ∀ a : {a // grid a}, Finset (CoefficientJetAxisRow O a.val))
    (p : ∀ a : {a // grid a}, PMF (CoefficientJetAxisRow O a.val))
    (z : AllocatedFrozenJetRows B U b S O) :
    0 ≤ allocatedGridWindowWeight B U b S O selected W p z :=
  Finset.prod_nonneg (fun a _ => allocatedGridWindowFactor_nonneg B U b S O selected W p a (z a))

theorem allocatedGridWindowFactor_measurable
    (selected : {a // grid a} → Prop) [DecidablePred selected]
    (W : ∀ a : {a // grid a}, Finset (CoefficientJetAxisRow O a.val))
    (p : ∀ a : {a // grid a}, PMF (CoefficientJetAxisRow O a.val))
    (a : {a // grid a}) :
    Measurable (allocatedGridWindowFactor B U b S O selected W p a) := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · let : Countable (CoefficientJetAxisRow O (⟨j, Sum.inr i⟩ : LayerSamplerAxis I n)) :=
      inferInstanceAs (Countable (O j → ℤ))
    let : MeasurableSingletonClass (CoefficientJetAxisRow O (⟨j, Sum.inr i⟩ : LayerSamplerAxis I n)) :=
      inferInstanceAs (MeasurableSingletonClass (O j → ℤ))
    exact measurable_of_countable _

theorem allocatedGridWindowWeight_measurable
    (selected : {a // grid a} → Prop) [DecidablePred selected]
    (W : ∀ a : {a // grid a}, Finset (CoefficientJetAxisRow O a.val))
    (p : ∀ a : {a // grid a}, PMF (CoefficientJetAxisRow O a.val))
    :
    Measurable (allocatedGridWindowWeight B U b S O selected W p) :=
  Finset.measurable_prod _ (fun a _ => (allocatedGridWindowFactor_measurable B U b S O selected W p a).comp
    (measurable_pi_apply a))

theorem allocatedGridWindowFactor_mass_data
    (selected : {a // grid a} → Prop) [DecidablePred selected]
    (W : ∀ a : {a // grid a}, Finset (CoefficientJetAxisRow O a.val))
    (p : ∀ a : {a // grid a}, PMF (CoefficientJetAxisRow O a.val))
    (a : {a // grid a}) :
    Integrable (allocatedGridWindowFactor B U b S O selected W p a)
      (coefficientJetAxisReference O a.val) ∧
      (∫ z, allocatedGridWindowFactor B U b S O selected W p a z
        ∂coefficientJetAxisReference O a.val) = (if selected a then ((W a).card : ℝ) else 1) := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · let : Countable (CoefficientJetAxisRow O (⟨j, Sum.inr i⟩ : LayerSamplerAxis I n)) :=
      inferInstanceAs (Countable (O j → ℤ))
    let : MeasurableSingletonClass (CoefficientJetAxisRow O (⟨j, Sum.inr i⟩ : LayerSamplerAxis I n)) :=
      inferInstanceAs (MeasurableSingletonClass (O j → ℤ))
    change Integrable _ (Measure.count : Measure (CoefficientJetAxisRow O (⟨j, Sum.inr i⟩ : LayerSamplerAxis I n))) ∧
      (∫ z : CoefficientJetAxisRow O (⟨j, Sum.inr i⟩ : LayerSamplerAxis I n), _ ∂Measure.count) = _
    unfold allocatedGridWindowFactor
    by_cases hs : selected ⟨⟨j, Sum.inr i⟩, ha⟩
    · simpa only [hs, ite_true] using
        count_finset_indicator_data (W ⟨⟨j, Sum.inr i⟩, ha⟩)
    · simpa only [hs, ite_false] using
        (show Integrable (fun z => (p ⟨⟨j, Sum.inr i⟩, ha⟩ z).toReal) Measure.count ∧
          (∫ z, (p ⟨⟨j, Sum.inr i⟩, ha⟩ z).toReal ∂Measure.count) = 1 from
            ⟨pmf_real_integrable _, pmf_real_integral_count _⟩)

theorem allocatedGridWindowWeight_mass_data
    (selected : {a // grid a} → Prop) [DecidablePred selected]
    (W : ∀ a : {a // grid a}, Finset (CoefficientJetAxisRow O a.val))
    (p : ∀ a : {a // grid a}, PMF (CoefficientJetAxisRow O a.val))
    :
    Integrable (allocatedGridWindowWeight B U b S O selected W p) (allocatedFrozenJetReference B U b S O) ∧
      (∫ z, |allocatedGridWindowWeight B U b S O selected W p z| ∂allocatedFrozenJetReference B U b S O) =
        ∏ a, if selected a then ((W a).card : ℝ) else 1 := by
  have hp := allocatedGridWindowFactor_mass_data B U b S O selected W p
  refine ⟨Integrable.fintype_prod_dep (fun a => (hp a).1), ?_⟩
  simp_rw [abs_of_nonneg (allocatedGridWindowWeight_nonneg B U b S O selected W p _)]
  change (∫ z, (∏ a, allocatedGridWindowFactor B U b S O selected W p a (z a))
    ∂Measure.pi (fun a : {a // grid a} => coefficientJetAxisReference O a.val)) = _
  rw [integral_fintype_prod_eq_prod]
  exact Finset.prod_congr rfl (fun a _ => (hp a).2)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (O : Fin m → Type*) [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)

noncomputable def allocatedSelectedGridMass
    (selected : {a // grid a} → Prop) [DecidablePred selected]
    (p : ∀ a : {a // grid a}, PMF (CoefficientJetAxisRow O a.val))
    (z : AllocatedFrozenJetRows B U b S O) : ℝ :=
  ∏ a, if selected a then (p a (z a)).toReal else 1

noncomputable def allocatedRemainingGridMass
    (selected : {a // grid a} → Prop) [DecidablePred selected]
    (p : ∀ a : {a // grid a}, PMF (CoefficientJetAxisRow O a.val))
    (z : AllocatedFrozenJetRows B U b S O) : ℝ :=
  ∏ a, if selected a then 1 else (p a (z a)).toReal

noncomputable def allocatedPartialGridApproximation
    (selected : {a // grid a} → Prop) [DecidablePred selected]
    (p : ∀ a : {a // grid a}, PMF (CoefficientJetAxisRow O a.val))
    (N : ℝ) (g : AllocatedFrozenJetRows B U b S O → ℂ)
    (z : AllocatedFrozenJetRows B U b S O) : ℂ :=
  (g z / (N : ℂ)) * (allocatedRemainingGridMass B U b S O selected p z : ℂ)

omit [∀ j, Fintype (O j)] in
theorem allocatedRemainingGridMass_nonneg
    (selected : {a // grid a} → Prop) [DecidablePred selected]
    (p : ∀ a : {a // grid a}, PMF (CoefficientJetAxisRow O a.val))
    (z : AllocatedFrozenJetRows B U b S O) :
    0 ≤ allocatedRemainingGridMass B U b S O selected p z := by
  apply Finset.prod_nonneg
  intro a _
  split_ifs
  · exact zero_le_one
  · exact ENNReal.toReal_nonneg

omit [∀ j, Fintype (O j)] in
theorem allocatedSelectedGridMass_mul_remaining
    (selected : {a // grid a} → Prop) [DecidablePred selected]
    (p : ∀ a : {a // grid a}, PMF (CoefficientJetAxisRow O a.val))
    (z : AllocatedFrozenJetRows B U b S O) :
    allocatedSelectedGridMass B U b S O selected p z * allocatedRemainingGridMass B U b S O selected p z =
      ∏ a, (p a (z a)).toReal := by
  unfold allocatedSelectedGridMass allocatedRemainingGridMass
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro a _
  by_cases h : selected a <;> simp only [h, ite_true, ite_false, mul_one, one_mul]

theorem allocatedRemainingGridMass_measurable
    (selected : {a // grid a} → Prop) [DecidablePred selected]
    (p : ∀ a : {a // grid a}, PMF (CoefficientJetAxisRow O a.val)) :
    Measurable (allocatedRemainingGridMass B U b S O selected p) := by
  apply Finset.measurable_prod
  intro a _
  exact (measurable_of_countable (fun z => if selected a then (1 : ℝ) else (p a z).toReal)).comp
    (measurable_pi_apply a)

theorem allocatedPartialGridApproximation_measurable
    (selected : {a // grid a} → Prop) [DecidablePred selected]
    (p : ∀ a : {a // grid a}, PMF (CoefficientJetAxisRow O a.val))
    (N : ℝ) (g : AllocatedFrozenJetRows B U b S O → ℂ) (hg : Measurable g) :
    Measurable (allocatedPartialGridApproximation B U b S O selected p N g) :=
  (hg.div_const (N : ℂ)).mul (allocatedRemainingGridMass_measurable B U b S O selected p).complex_ofReal

omit [∀ j, Fintype (O j)] in
theorem allocatedGridWindowWeight_inside
    (selected : {a // grid a} → Prop) [DecidablePred selected]
    (p : ∀ a : {a // grid a}, PMF (CoefficientJetAxisRow O a.val))
    (W : ∀ a : {a // grid a}, Finset (CoefficientJetAxisRow O a.val))
    (z : AllocatedFrozenJetRows B U b S O) (hz : ∀ a, selected a → z a ∈ W a) :
    allocatedGridWindowWeight B U b S O selected W p z = allocatedRemainingGridMass B U b S O selected p z := by
  apply Finset.prod_congr rfl
  intro a _
  unfold allocatedGridWindowFactor
  by_cases ha : selected a
  · simp only [ha, ite_true, Set.indicator_of_mem (hz a ha)]
  · simp only [ha, ite_false]

omit [∀ j, Fintype (O j)] in
theorem allocatedGridWindowWeight_outside
    (selected : {a // grid a} → Prop) [DecidablePred selected]
    (p : ∀ a : {a // grid a}, PMF (CoefficientJetAxisRow O a.val))
    (W : ∀ a : {a // grid a}, Finset (CoefficientJetAxisRow O a.val))
    (z : AllocatedFrozenJetRows B U b S O) (hz : ¬∀ a, selected a → z a ∈ W a) :
    allocatedGridWindowWeight B U b S O selected W p z = 0 := by
  push Not at hz
  obtain ⟨a, ha, hz⟩ := hz
  apply Finset.prod_eq_zero (Finset.mem_univ a)
  simp only [allocatedGridWindowFactor, ha, ite_true, Set.indicator_of_notMem hz]

omit [∀ j, Fintype (O j)] in
theorem allocatedPartialGridApproximation_error
    (selected : {a // grid a} → Prop) [DecidablePred selected]
    (p : ∀ a : {a // grid a}, PMF (CoefficientJetAxisRow O a.val))
    (W : ∀ a : {a // grid a}, Finset (CoefficientJetAxisRow O a.val))
    (g : AllocatedFrozenJetRows B U b S O → ℂ)
    {N ε : ℝ} (hN : 0 < N)
    (hzero : ∀ z, (¬∀ a, selected a → z a ∈ W a) →
      allocatedSelectedGridMass B U b S O selected p z = 0 ∧ g z = 0)
    (he : ∀ z, ‖(N : ℂ) * (allocatedSelectedGridMass B U b S O selected p z : ℂ) - g z‖ ≤ ε)
    (z : AllocatedFrozenJetRows B U b S O) :
    ‖((∏ a, (p a (z a)).toReal : ℝ) : ℂ) - allocatedPartialGridApproximation B U b S O selected p N g z‖ ≤
      (ε / N) * allocatedGridWindowWeight B U b S O selected W p z := by
  rw [← allocatedSelectedGridMass_mul_remaining B U b S O selected p z]
  have hid : ((allocatedSelectedGridMass B U b S O selected p z *
      allocatedRemainingGridMass B U b S O selected p z : ℝ) : ℂ) -
        allocatedPartialGridApproximation B U b S O selected p N g z =
      ((allocatedSelectedGridMass B U b S O selected p z : ℂ) - g z / (N : ℂ)) *
        (allocatedRemainingGridMass B U b S O selected p z : ℂ) := by
    unfold allocatedPartialGridApproximation
    push_cast
    ring
  rw [hid, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (allocatedRemainingGridMass_nonneg B U b S O selected p z)]
  by_cases hz : ∀ a, selected a → z a ∈ W a
  · rw [allocatedGridWindowWeight_inside B U b S O selected p W z hz]
    exact mul_le_mul_of_nonneg_right (normalized_complex_point_error _ _ hN (he z))
      (allocatedRemainingGridMass_nonneg B U b S O selected p z)
  · obtain ⟨h0, hg0⟩ := hzero z hz
    rw [h0, hg0, Complex.ofReal_zero, zero_div, sub_zero, norm_zero, zero_mul,
      allocatedGridWindowWeight_outside B U b S O selected p W z hz, mul_zero]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
variable (selected : {a // allocatedGridAxis (I := I) U b S.value a} → Prop)
variable [DecidablePred selected]
local notation "laws" => allocatedSupportedGridJetPMF B U b hR hσ S x rows q r hcell

noncomputable def allocatedSelectedGridExtension (g : ((a : {a : gridAxes // selected a}) → CoefficientJetAxisRow O (Subtype.val (Subtype.val a))) → ℂ) (N : ℝ) :
    AllocatedFrozenJetRows B U b S O → ℂ :=
  selectedProductExtension selected (fun a z => (laws a z).toReal) g N

theorem allocatedSelectedGridExtension_measurable (g : ((a : {a : gridAxes // selected a}) → CoefficientJetAxisRow O (Subtype.val (Subtype.val a))) → ℂ) (N : ℝ) :
    Measurable (allocatedSelectedGridExtension B U b hR hσ S x rows q r hcell selected g N) := by
  apply selectedProductExtension_measurable
  · exact fun a => measurable_of_countable _
  · exact measurable_of_countable _

omit [∀ j, Fintype (O j)] in
theorem allocatedSelectedGridExtension_error
    (W : ∀ a : gridAxes, Finset (CoefficientJetAxisRow O a.val))
    (g : ((a : {a : gridAxes // selected a}) → CoefficientJetAxisRow O (Subtype.val (Subtype.val a))) → ℂ) {N ε : ℝ} (hN : 0 < N)
    (hzero : ∀ z : ((a : {a : gridAxes // selected a}) → CoefficientJetAxisRow O (Subtype.val (Subtype.val a))), (∃ a, z a ∉ W a.val) →
      (∏ a, (laws a.val (z a)).toReal) = 0 ∧ g z = 0)
    (he : ∀ z : ((a : {a : gridAxes // selected a}) → CoefficientJetAxisRow O (Subtype.val (Subtype.val a))),
      ‖(N : ℂ) * ((∏ a, (laws a.val (z a)).toReal : ℝ) : ℂ) - g z‖ ≤ ε)
    (z : AllocatedFrozenJetRows B U b S O) :
    ‖(allocatedSupportedGridJetDensity B U b hR hσ S x rows q r hcell z : ℂ) -
      allocatedSelectedGridExtension B U b hR hσ S x rows q r hcell selected g N z‖ ≤
      (ε / N) * allocatedGridWindowWeight B U b S O selected W laws z := by
  exact selectedProductExtension_error selected (fun a z => (laws a z).toReal)
    (fun _ _ => ENNReal.toReal_nonneg) W g hN hzero he z

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)

noncomputable def allocatedFrozenNaturalScale : {a // grid a} → ℕ
  | ⟨⟨_, .inl _⟩, ha⟩ => False.elim ha
  | ⟨⟨j, .inr i⟩, _⟩ => allocatedPrincipalGridScale (G := G) B U b (R := R) j i

theorem allocatedFrozenNaturalScale_pos (hR : ∀ j, 0 < R j) (a : {a // grid a}) :
    0 < allocatedFrozenNaturalScale B U b S a := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · exact allocatedPrincipalGridScale_pos_of_radius B U b hR j i

variable (α : Type*) [Fintype α]

noncomputable def allocatedFrozenNaturalRadius : {a // grid a} → ℝ
  | ⟨⟨_, .inl _⟩, ha⟩ => False.elim ha
  | ⟨⟨j, .inr i⟩, _⟩ => allocatedNaturalSupportRadius (G := G) B α j i

theorem allocatedFrozenNaturalRadius_nonneg (a : {a // grid a}) :
    0 ≤ allocatedFrozenNaturalRadius B U b S α a := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · exact allocatedNaturalSupportRadius_nonneg (G := G) B α j i

variable (O : Fin m → Type*) [∀ j, Fintype (O j)]

noncomputable def allocatedFrozenNaturalWindow : ∀ a : {a // grid a}, Finset (CoefficientJetAxisRow O a.val)
  | ⟨⟨_, .inl _⟩, ha⟩ => False.elim ha
  | ⟨⟨j, .inr i⟩, _⟩ => naturalScaleIntegerWindow (O j)
      (allocatedNaturalSupportRadius (G := G) B α j i)
      (allocatedPrincipalGridScale (G := G) B U b (R := R) j i)

noncomputable def allocatedSelectedNaturalVolume
    (selected : {a // grid a} → Prop) [DecidablePred selected] : ℝ :=
  ∏ a, if selected a then (allocatedFrozenNaturalScale B U b S a : ℝ) ^ Fintype.card (O a.val.1) else 1

noncomputable def allocatedSelectedNaturalWindowVolume
    (selected : {a // grid a} → Prop) [DecidablePred selected] : ℝ :=
  ∏ a, if selected a then (2 * allocatedFrozenNaturalRadius B U b S α a + 3) ^ Fintype.card (O a.val.1) else 1

theorem allocatedFrozenNaturalWindow_card_le (hR : ∀ j, 0 < R j) (a : {a // grid a}) :
    ((allocatedFrozenNaturalWindow B U b S α O a).card : ℝ) ≤
      (2 * allocatedFrozenNaturalRadius B U b S α a + 3) ^ Fintype.card (O a.val.1) *
        (allocatedFrozenNaturalScale B U b S a : ℝ) ^ Fintype.card (O a.val.1) := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · exact naturalScaleIntegerWindow_card_le (O j)
      (allocatedNaturalSupportRadius_nonneg (G := G) B α j i)
      (allocatedPrincipalGridScale_pos_of_radius B U b hR j i)

omit [Fintype α] in
theorem allocatedSelectedNaturalVolume_pos (hR : ∀ j, 0 < R j)
    (selected : {a // grid a} → Prop) [DecidablePred selected] :
    0 < allocatedSelectedNaturalVolume B U b S O selected := by
  apply Finset.prod_pos
  intro a _
  split_ifs
  · exact pow_pos (Nat.cast_pos.mpr (allocatedFrozenNaturalScale_pos B U b S hR a)) _
  · exact zero_lt_one

theorem allocatedSelectedNaturalWindowVolume_nonneg
    (selected : {a // grid a} → Prop) [DecidablePred selected] :
    0 ≤ allocatedSelectedNaturalWindowVolume B U b S α O selected := by
  apply Finset.prod_nonneg
  intro a _
  split_ifs
  · exact pow_nonneg (by linarith [allocatedFrozenNaturalRadius_nonneg B U b S α a]) _
  · exact zero_le_one

theorem allocatedFrozenNaturalWindow_selected_card_le (hR : ∀ j, 0 < R j)
    (selected : {a // grid a} → Prop) [DecidablePred selected] :
    (∏ a, if selected a then ((allocatedFrozenNaturalWindow B U b S α O a).card : ℝ) else 1) ≤
      allocatedSelectedNaturalWindowVolume B U b S α O selected *
        allocatedSelectedNaturalVolume B U b S O selected := by
  unfold allocatedSelectedNaturalWindowVolume allocatedSelectedNaturalVolume
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro a _
    split_ifs <;> positivity
  · intro a _
    by_cases ha : selected a
    · simpa only [ha, ite_true] using allocatedFrozenNaturalWindow_card_le B U b S α O hR a
    · simp only [ha, ite_false, mul_one, le_refl]

end Erdos3.VectorPolynomial

end

end OAI
