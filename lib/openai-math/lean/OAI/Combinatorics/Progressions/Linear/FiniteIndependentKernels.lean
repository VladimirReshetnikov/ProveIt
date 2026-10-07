import OAI.Combinatorics.Progressions.Probability.ShiftedProductCoordinateLaw

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

universe uA uX uY uZ

theorem dependentProductPMF_finite_bind
    {A : Type uA} [Fintype A] {X : A → Type uX} {Y : A → Type uY}
    [∀ a, Fintype (X a)] [∀ a, MeasurableSpace (X a)] [∀ a, MeasurableSingletonClass (X a)]
    [∀ a, Countable (Y a)] [∀ a, MeasurableSpace (Y a)] [∀ a, MeasurableSingletonClass (Y a)]
    (p : ∀ a, PMF (X a)) (q : ∀ a, X a → PMF (Y a)) :
    (dependentProductPMF p).bind (fun x => dependentProductPMF (fun a => q a (x a))) =
      dependentProductPMF (fun a => (p a).bind (q a)) := by
  classical
  ext y
  simp only [PMF.bind_apply, tsum_fintype, dependentProductPMF_apply,
    ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun a x => p a x * q a x (y a))).symm

theorem dependentProductPMF_eval
    {A : Type uA} [Fintype A] {X : A → Type uX}
    [∀ a, Countable (X a)] [∀ a, MeasurableSpace (X a)] [∀ a, MeasurableSingletonClass (X a)]
    (p : ∀ a, PMF (X a)) (a : A) :
    (dependentProductPMF p).map (fun x => x a) = p a := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map (fun x => x a) (dependentProductPMF p) (by fun_prop)]
  simp only [dependentProductPMF, Measure.toPMF_toMeasure]
  exact (measurePreserving_eval (fun a => (p a).toMeasure) a).map_eq

theorem pmf_bind_of_finite_independent_coordinates
    {A : Type uA} [Fintype A] {X : A → Type uX} {Y : A → Type uY} {Z : Type uZ}
    [∀ a, Fintype (X a)] [∀ a, MeasurableSpace (X a)] [∀ a, MeasurableSingletonClass (X a)]
    [∀ a, Countable (Y a)] [∀ a, MeasurableSpace (Y a)] [∀ a, MeasurableSingletonClass (Y a)]
    (p : PMF Z) (g : Z → ∀ a, X a) (t : ∀ a, PMF (X a))
    (ht : p.map g = dependentProductPMF t) (q : ∀ a, X a → PMF (Y a)) :
    p.bind (fun z => dependentProductPMF (fun a => q a (g z a))) =
      dependentProductPMF (fun a => p.bind (fun z => q a (g z a))) := by
  have hcoord (a : A) : p.map (fun z => g z a) = t a :=
    (PMF.map_comp g p (fun x => x a)).symm.trans
      ((congrArg (fun μ : PMF (∀ a, X a) => μ.map (fun x => x a)) ht).trans
        (dependentProductPMF_eval t a))
  have hlocal (a : A) : p.bind (fun z => q a (g z a)) = (t a).bind (q a) :=
    (PMF.bind_map p (fun z => g z a) (q a)).symm.trans
      (congrArg (fun μ : PMF (X a) => μ.bind (q a)) (hcoord a))
  calc
    _ = (p.map g).bind (fun x => dependentProductPMF (fun a => q a (x a))) :=
      (PMF.bind_map p g (fun x => dependentProductPMF (fun a => q a (x a)))).symm
    _ = (dependentProductPMF t).bind (fun x => dependentProductPMF (fun a => q a (x a))) :=
      congrArg (fun μ : PMF (∀ a, X a) => μ.bind
        (fun x => dependentProductPMF (fun a => q a (x a)))) ht
    _ = dependentProductPMF (fun a => (t a).bind (q a)) := dependentProductPMF_finite_bind t q
    _ = _ := congrArg (fun μ : ∀ a, PMF (Y a) => dependentProductPMF μ)
      (funext (fun a => (hlocal a).symm))

end Erdos3

end

end OAI
