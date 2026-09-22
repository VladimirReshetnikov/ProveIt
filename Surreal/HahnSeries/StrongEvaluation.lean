import Surreal.HahnSeries.Evaluation
import Surreal.HahnSeries.Regroup

/-!
# Strong additivity of admissible formal-series evaluation

A family of ordinary power series is source-summable precisely when each
degree occurs in only finitely many members. At a positive-order Hahn
argument, the entire family of coefficient-times-power terms, indexed by
the source member and its degree, is jointly strongly summable. Regrouping
by either index proves that evaluation preserves the source coefficient
sum. This is the strong-additivity clause of `thm:exact` in the report on
Hahn evaluation at omega.

The source index type has an arbitrary universe and need not be small in
any separately fixed universe. Zero arguments are included by their infinite
order. No topology, field hypothesis, or no-zero-divisors hypothesis is used.
-/

universe u v w

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

variable {R : Type u} {ι : Type v} [CommRing R]

/-- Ordinary formal-series summability is finite coefficient incidence at every degree. -/
def PowerSeriesSummable (f : ι → PowerSeries R) : Prop :=
  ∀ n, (fun i => (f i).coeff n).HasFiniteSupport

/-- The coefficientwise source sum; its strong-sum interpretation requires source summability. -/
def powerSeriesSum (f : ι → PowerSeries R) : PowerSeries R :=
  PowerSeries.mk (fun n => ∑ᶠ i, (f i).coeff n)

@[simp] theorem coeff_powerSeriesSum (f : ι → PowerSeries R) (n : ℕ) :
    (powerSeriesSum f).coeff n = ∑ᶠ i, (f i).coeff n :=
  PowerSeries.coeff_mk _ _

variable {Γ : Type w} [AddCommMonoid Γ] [LinearOrder Γ]
  [IsOrderedCancelAddMonoid Γ]

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
private def coefficientRefinement {α β : Type*} (s : SummableFamily Γ R β)
    (c : α → β → R) (hc : ∀ b, (fun a => c a b).HasFiniteSupport) :
    SummableFamily Γ R (α × β) where
  toFun p := c p.1 p.2 • s p.2
  isPWO_iUnion_support' := s.isPWO_iUnion_support.mono <| by
    refine Set.iUnion_subset fun p => ?_
    intro g hg
    exact Set.mem_iUnion.mpr ⟨p.2, support_smul_subset _ _ hg⟩
  finite_co_support' g := by
    apply ((s.finite_co_support g).biUnion
      (fun b _ => (hc b).image (fun a => (a, b)))).subset
    rintro ⟨a, b⟩ hab
    have hb : (s b).coeff g ≠ 0 := by
      intro h
      exact hab (by simp [coeff_smul, h])
    have ha : c a b ≠ 0 := by
      intro h
      exact hab (by simp [h])
    exact Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hb, ⟨a, ha, rfl⟩⟩⟩

/-- The full coefficient-times-power family is jointly strongly summable before regrouping. -/
def powerSeriesEvaluationJointFamily (x : R⟦Γ⟧) (_hx : 0 < x.orderTop)
    (f : ι → PowerSeries R) (hf : PowerSeriesSummable f) :
    SummableFamily Γ R (ι × ℕ) :=
  coefficientRefinement (SummableFamily.powers x) (fun i n => (f i).coeff n) hf

@[simp] theorem powerSeriesEvaluationJointFamily_apply (x : R⟦Γ⟧)
    (hx : 0 < x.orderTop) (f : ι → PowerSeries R) (hf : PowerSeriesSummable f)
    (p : ι × ℕ) :
    powerSeriesEvaluationJointFamily x hx f hf p = (f p.1).coeff p.2 • x ^ p.2 := by
  change (f p.1).coeff p.2 • SummableFamily.powers x p.2 = _
  rw [SummableFamily.powers_of_orderTop_pos hx]

/-- Regrouping by source member constructs the jointly summable family of evaluated values. -/
def evaluatedPowerSeriesFamily (x : R⟦Γ⟧) (hx : 0 < x.orderTop)
    (f : ι → PowerSeries R) (hf : PowerSeriesSummable f) : SummableFamily Γ R ι :=
  regroup (powerSeriesEvaluationJointFamily x hx f hf) Prod.fst

/-- Every term of the constructed evaluated family is the original admissible evaluation. -/
@[simp] theorem evaluatedPowerSeriesFamily_apply (x : R⟦Γ⟧) (hx : 0 < x.orderTop)
    (f : ι → PowerSeries R) (hf : PowerSeriesSummable f) (i : ι) :
    evaluatedPowerSeriesFamily x hx f hf i = evaluate x hx (f i) := by
  apply _root_.HahnSeries.ext
  funext g
  rw [evaluatedPowerSeriesFamily, regroup_apply, SummableFamily.coeff_hsum, coeff_evaluate]
  simp only [restrict_apply, powerSeriesEvaluationJointFamily_apply,
    single_zero_mul_eq_smul]
  apply finsum_eq_of_bijective (fun p : {p : ι × ℕ // p.1 = i} => p.val.2)
  · constructor
    · intro a b hab
      apply Subtype.ext
      exact Prod.ext (a.property.trans b.property.symm) hab
    · intro n
      exact ⟨⟨(i, n), rfl⟩, rfl⟩
  · intro p
    simp only [p.property]

/-- Regrouping the joint family by degree gives the terms of the source coefficient sum. -/
theorem regroup_powerSeriesEvaluationJointFamily_snd (x : R⟦Γ⟧) (hx : 0 < x.orderTop)
    (f : ι → PowerSeries R) (hf : PowerSeriesSummable f) :
    regroup (powerSeriesEvaluationJointFamily x hx f hf) Prod.snd =
      SummableFamily.powerSeriesFamily x (powerSeriesSum f) := by
  apply SummableFamily.ext
  intro n
  apply _root_.HahnSeries.ext
  funext g
  rw [regroup_apply, SummableFamily.coeff_hsum,
    SummableFamily.powerSeriesFamily_of_orderTop_pos hx]
  simp only [restrict_apply, powerSeriesEvaluationJointFamily_apply,
    coeff_smul, coeff_powerSeriesSum, smul_eq_mul]
  rw [finsum_mul' _ _ (hf n)]
  apply finsum_eq_of_bijective (fun p : {p : ι × ℕ // p.2 = n} => p.val.1)
  · constructor
    · intro a b hab
      apply Subtype.ext
      exact Prod.ext hab (a.property.trans b.property.symm)
    · intro i
      exact ⟨⟨(i, n), rfl⟩, rfl⟩
  · intro p
    simp only [p.property]

/-- Admissible evaluation preserves every source-summable ordinary power-series family. -/
theorem evaluate_powerSeriesSum (x : R⟦Γ⟧) (hx : 0 < x.orderTop)
    (f : ι → PowerSeries R) (hf : PowerSeriesSummable f) :
    evaluate x hx (powerSeriesSum f) = (evaluatedPowerSeriesFamily x hx f hf).hsum := by
  change (SummableFamily.powerSeriesFamily x (powerSeriesSum f)).hsum = _
  rw [← regroup_powerSeriesEvaluationJointFamily_snd x hx f hf, hsum_regroup]
  exact (hsum_regroup (powerSeriesEvaluationJointFamily x hx f hf) Prod.fst).symm

/-- The abstract preservation statement also exposes the actual summability certificate. -/
theorem summable_evaluate_powerSeries (x : R⟦Γ⟧) (hx : 0 < x.orderTop)
    (f : ι → PowerSeries R) (hf : PowerSeriesSummable f) :
    ∃ s : SummableFamily Γ R ι,
      (∀ i, s i = evaluate x hx (f i)) ∧ evaluate x hx (powerSeriesSum f) = s.hsum :=
  ⟨evaluatedPowerSeriesFamily x hx f hf,
    evaluatedPowerSeriesFamily_apply x hx f hf, evaluate_powerSeriesSum x hx f hf⟩

end

end Surreal.HahnSeries
