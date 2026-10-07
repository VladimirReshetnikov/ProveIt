/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import OAI.Combinatorics.Progressions.Sampling.AllocatedCoefficientSampler

namespace OAI

section

namespace Erdos3
open MeasureTheory

theorem mixedScalarArrayLaw_integer_marginal {I Z Q : Type*}
    [Fintype I] [Fintype Z] [Fintype Q]
    (c w : I → Q → ℝ) (hw : ∀ i q, 0 < w i q) (p : Z → Q → PMF ℤ) :
    MeasurePreserving Prod.snd (mixedScalarArrayLaw c w p)
      (Measure.pi (fun z => Measure.pi (fun q => (p z q).toMeasure))) := by
  let : ∀ i q, IsProbabilityMeasure (affineCoefficientMeasure (c i q) (w i q)) :=
    fun i q => affineCoefficientMeasure_probability _ (hw i q)
  exact measurePreserving_snd

theorem pmf_bind_pair_toMeasure {X Y : Type*} [Countable X] [Countable Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (p : PMF X) (q : PMF Y) :
    (p.bind (fun x => q.map (fun y => (x, y)))).toMeasure = p.toMeasure.prod q.toMeasure := by
  apply Measure.ext_of_singleton
  rintro ⟨x, y⟩
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), pmf_bind_pair_apply,
    ← Set.singleton_prod_singleton, Measure.prod_prod]
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]

namespace VectorPolynomial
open Module Submodule
open scoped BigOperators Classical

abbrev CoefficientIntegerScalarIndex (K : Type*) {m : ℕ} (n : Fin m → ℕ) :=
  Σ j : Fin m, BoundedCoefficientExponent K (j.val + 1) × Fin (n j)

def coefficientIntegerScalars {K : Type*} {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
    (a : CoefficientSamplerArrays (K := K) I n) (q : CoefficientIntegerScalarIndex K n) : ℤ :=
  (a q.1).2 q.2.2 q.2.1

theorem coefficientIntegerScalars_measurable {K : Type*} {m : ℕ}
    {I : Fin m → Type*} {n : Fin m → ℕ} :
    Measurable (coefficientIntegerScalars (K := K) (I := I) (n := n)) := by
  apply Measurable.of_eval
  intro q
  exact (measurable_pi_apply q.2.1).comp
    ((measurable_pi_apply q.2.2).comp (measurable_snd.comp (measurable_pi_apply q.1)))

theorem coefficientIntegerScalars_measurePreserving {K : Type*} [Fintype K] {m : ℕ}
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
    (hw : ∀ j i q, 0 < w j i q)
    (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ) :
    MeasurePreserving coefficientIntegerScalars
      (Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j)))
      (Measure.pi (fun q : CoefficientIntegerScalarIndex K n => (p q.1 q.2.2 q.2.1).toMeasure)) := by
  let μ := fun q : CoefficientIntegerScalarIndex K n => (p q.1 q.2.2 q.2.1).toMeasure
  have hrow (j : Fin m) : MeasurePreserving
      (fun a : (I j → BoundedCoefficientExponent K (j.val + 1) → ℝ) ×
        (Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → ℤ) =>
          fun q : BoundedCoefficientExponent K (j.val + 1) × Fin (n j) => a.2 q.2 q.1)
      (mixedScalarArrayLaw (c j) (w j) (p j))
      (Measure.pi (fun q => μ ⟨j, q⟩)) := by
    exact ((finiteArray_uncurry_measurePreserving (fun q i => (p j i q).toMeasure)).comp
      (finiteArrayTranspose_measurePreserving (fun i q => (p j i q).toMeasure))).comp
        (mixedScalarArrayLaw_integer_marginal (c j) (w j) (hw j) (p j))
  have houter := measurePreserving_pi
    (fun j => mixedScalarArrayLaw (c j) (w j) (p j))
    (fun j => Measure.pi (fun q => μ ⟨j, q⟩)) hrow
  have hflat : MeasurePreserving
      (fun (x : ∀ j : Fin m, BoundedCoefficientExponent K (j.val + 1) × Fin (n j) → ℤ)
        (q : CoefficientIntegerScalarIndex K n) => x q.1 q.2)
      (Measure.pi (fun j => Measure.pi (fun q => μ ⟨j, q⟩))) (Measure.pi μ) :=
    ⟨Measurable.of_eval (fun q => (measurable_pi_apply q.2).comp (measurable_pi_apply q.1)),
      sigmaProductMeasure_flatten μ⟩
  exact hflat.comp houter

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

noncomputable def allocatedCoefficientIntegerPMF :
    PMF (CoefficientIntegerScalarIndex (LayerSamplerVariables G I n B) n → ℤ) :=
  independentProductPMF (fun q => allocatedLayerIntegerPMFs B U b hR hσ S q.1 q.2.2 q.2.1)

theorem allocatedCoefficientSource_integer_measurePreserving :
    MeasurePreserving coefficientIntegerScalars
      (allocatedCoefficientSource B U b hR hσ S)
      (allocatedCoefficientIntegerPMF B U b hR hσ S).toMeasure := by
  simpa only [allocatedCoefficientSource, allocatedCoefficientIntegerPMF,
    independentProductPMF, Measure.toPMF_toMeasure] using
    coefficientIntegerScalars_measurePreserving
      (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
      (allocatedLayerWidths_pos B U b hR hσ S) (allocatedLayerIntegerPMFs B U b hR hσ S)

theorem allocatedCoefficientSource_integer_map :
    (allocatedCoefficientSource B U b hR hσ S).map coefficientIntegerScalars =
      (allocatedCoefficientIntegerPMF B U b hR hσ S).toMeasure :=
  (allocatedCoefficientSource_integer_measurePreserving B U b hR hσ S).map_eq

theorem allocatedCoefficientSource_integer_prod_measurePreserving
    {Deck : Type*} [Countable Deck] [MeasurableSpace Deck] [MeasurableSingletonClass Deck]
    (q : PMF Deck) :
    MeasurePreserving (Prod.map coefficientIntegerScalars id)
      ((allocatedCoefficientSource B U b hR hσ S).prod q.toMeasure)
      ((allocatedCoefficientIntegerPMF B U b hR hσ S).bind
        (fun a => q.map (fun deck => (a, deck)))).toMeasure := by
  let : IsProbabilityMeasure (allocatedCoefficientSource B U b hR hσ S) :=
    allocatedCoefficientSource_probability B U b hR hσ S
  rw [pmf_bind_pair_toMeasure]
  exact (allocatedCoefficientSource_integer_measurePreserving B U b hR hσ S).prod
    (MeasurePreserving.id q.toMeasure)

theorem allocatedCoefficientSource_integer_prod_integral
    {Deck : Type*} [Countable Deck] [MeasurableSpace Deck] [MeasurableSingletonClass Deck]
    (q : PMF Deck)
    (f : (CoefficientIntegerScalarIndex (LayerSamplerVariables G I n B) n → ℤ) → Deck → ℂ) :
    (∫ a, f (coefficientIntegerScalars a.1) a.2
      ∂(allocatedCoefficientSource B U b hR hσ S).prod q.toMeasure) =
    ∫ a, f a.1 a.2 ∂((allocatedCoefficientIntegerPMF B U b hR hσ S).bind
      (fun a => q.map (fun deck => (a, deck)))).toMeasure := by
  have hp := allocatedCoefficientSource_integer_prod_measurePreserving B U b hR hσ S q
  rw [← hp.map_eq]
  exact (integral_map_of_stronglyMeasurable hp.measurable
    (measurable_of_countable (fun a => f a.1 a.2)).stronglyMeasurable).symm

theorem allocatedCoefficientSource_integer_prod_complexMean
    {Deck : Type*} [Countable Deck] [MeasurableSpace Deck] [MeasurableSingletonClass Deck]
    (q : PMF Deck)
    (f : (CoefficientIntegerScalarIndex (LayerSamplerVariables G I n B) n → ℤ) → Deck → ℂ)
    {C : ℝ} (hf : ∀ a deck, ‖f a deck‖ ≤ C) :
    (∫ a, f (coefficientIntegerScalars a.1) a.2
      ∂(allocatedCoefficientSource B U b hR hσ S).prod q.toMeasure) =
      ∑' a : (CoefficientIntegerScalarIndex (LayerSamplerVariables G I n B) n → ℤ) × Deck,
        (((allocatedCoefficientIntegerPMF B U b hR hσ S a.1).toReal * (q a.2).toReal : ℝ) : ℂ) *
          f a.1 a.2 := by
  rw [allocatedCoefficientSource_integer_prod_integral]
  let p := (allocatedCoefficientIntegerPMF B U b hR hσ S).bind
    (fun a => q.map (fun deck => (a, deck)))
  have hi : Integrable (fun a => f a.1 a.2) p.toMeasure :=
    pmf_integrable_of_norm_le p (fun a => f a.1 a.2) (fun a => hf a.1 a.2)
  simpa only [p, pmf_bind_pair_apply, ENNReal.toReal_mul, Complex.real_smul] using
    PMF.integral_eq_tsum p (fun a => f a.1 a.2) hi

theorem allocatedCoefficientSource_integer_prod_eventProbability
    {Deck : Type*} [Countable Deck] [MeasurableSpace Deck] [MeasurableSingletonClass Deck]
    (q : PMF Deck)
    (E : (CoefficientIntegerScalarIndex (LayerSamplerVariables G I n B) n → ℤ) → Deck → Prop) :
    (((allocatedCoefficientSource B U b hR hσ S).prod q.toMeasure)
      {a | E (coefficientIntegerScalars a.1) a.2}).toReal =
      (((allocatedCoefficientIntegerPMF B U b hR hσ S).bind
        (fun a => q.map (fun deck => decide (E a deck)))) true).toReal := by
  let p := (allocatedCoefficientIntegerPMF B U b hR hσ S).bind
    (fun a => q.map (fun deck => (a, deck)))
  let obs := fun a : (CoefficientIntegerScalarIndex (LayerSamplerVariables G I n B) n → ℤ) × Deck =>
    decide (E a.1 a.2)
  have hp := allocatedCoefficientSource_integer_prod_measurePreserving B U b hR hσ S q
  have hset :
      ((allocatedCoefficientSource B U b hR hσ S).prod q.toMeasure)
        {a | E (coefficientIntegerScalars a.1) a.2} = p.toMeasure {a | E a.1 a.2} := by
    rw [← hp.map_eq, Measure.map_apply hp.measurable (Set.to_countable _).measurableSet]
    rfl
  have hobs : (p.map obs) true = p.toMeasure {a | E a.1 a.2} := by
    rw [← PMF.toMeasure_apply_singleton _ true (measurableSet_singleton _),
      ← PMF.toMeasure_map _ _ (measurable_of_countable _),
      Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
    congr 1
    ext a
    simp [obs]
  rw [hset, ← hobs]
  congr 1
  simp only [p, PMF.map_bind, PMF.map_comp, obs, Function.comp_def]

theorem allocatedCoefficientSource_integer_prod_indicator
    {Deck : Type*} [Countable Deck] [MeasurableSpace Deck] [MeasurableSingletonClass Deck]
    (q : PMF Deck)
    (E : (CoefficientIntegerScalarIndex (LayerSamplerVariables G I n B) n → ℤ) → Deck → Prop) :
    (∫ a, (if E (coefficientIntegerScalars a.1) a.2 then (1 : ℝ) else 0)
      ∂(allocatedCoefficientSource B U b hR hσ S).prod q.toMeasure) =
      (((allocatedCoefficientIntegerPMF B U b hR hσ S).bind
        (fun a => q.map (fun deck => decide (E a deck)))) true).toReal := by
  have hp := allocatedCoefficientSource_integer_prod_measurePreserving B U b hR hσ S q
  have hs : MeasurableSet
      {a : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n × Deck |
        E (coefficientIntegerScalars a.1) a.2} :=
    (Set.to_countable {a : (CoefficientIntegerScalarIndex (LayerSamplerVariables G I n B) n → ℤ) × Deck |
      E a.1 a.2}).measurableSet.preimage hp.measurable
  calc
    _ = (((allocatedCoefficientSource B U b hR hσ S).prod q.toMeasure)
        {a | E (coefficientIntegerScalars a.1) a.2}).toReal := by
      simpa only [Set.indicator, Set.mem_ofPred_eq, Pi.one_apply, Measure.real] using
        integral_indicator_one (μ := (allocatedCoefficientSource B U b hR hσ S).prod q.toMeasure) hs
    _ = _ := allocatedCoefficientSource_integer_prod_eventProbability B U b hR hσ S q E

end VectorPolynomial
end Erdos3

end

end OAI
