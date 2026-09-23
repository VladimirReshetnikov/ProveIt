import Surreal.Surcomplex.PowerSeries
import Surreal.Surcomplex.StrongAlgebra

/-!
# Strong evaluation of finite linear combinations of ordinary series

Actual surcomplex scalar coefficients may be infinite. A finite linear
combination of ordinary power series still has a strongly summable term
family at every infinitesimal input. These closure rules support the local
angular germs in `trigonometry:thm:polyroots`.
-/

universe u v
namespace Surreal.Surcomplex

noncomputable section

/-- A fixed actual scalar may multiply an ordinary series under strong evaluation. -/
theorem strongSeries_scalar (a h : Surcomplex.{u}) (hh : IsInfinitesimal h)
    (f : PowerSeries ℂ) :
    ∃ hs : StronglySummable (fun n =>
      (PowerSeries.C a * PowerSeries.map ofComplex f).coeff n * h ^ n),
      strongSum _ hs = a * powerSeriesEvaluation h hh f := by
  have hf := stronglySummable_powerSeries h hh f
  have he : (fun n => (PowerSeries.C a * PowerSeries.map ofComplex f).coeff n * h ^ n) =
      (fun n => a * (ofComplex (f.coeff n) * h ^ n)) := by
    funext n
    simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_map, mul_assoc]
  rw [he]
  refine ⟨hf.const_mul a, ?_⟩
  rw [strongSum_const_mul hf a, ← powerSeriesEvaluation_eq_strongSum]

/-- Finite sums of strongly evaluable actual-coefficient series evaluate term by term. -/
theorem strongSeries_finset_sum {ι : Type v} (s : Finset ι)
    (F : ι → PowerSeries Surcomplex.{u}) (y : ι → Surcomplex.{u})
    (h : Surcomplex.{u}) (hh : IsInfinitesimal h)
    (hF : ∀ i ∈ s, ∃ hs : StronglySummable (fun n => (F i).coeff n * h ^ n),
      strongSum _ hs = y i) :
    ∃ hs : StronglySummable (fun n => (∑ i ∈ s, F i).coeff n * h ^ n),
      strongSum _ hs = ∑ i ∈ s, y i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hs := strongSeries_scalar (0 : Surcomplex.{u}) h hh (0 : PowerSeries ℂ)
    simpa only [Finset.sum_empty, map_zero, zero_mul] using hs
  | @insert i s hi ih =>
    obtain ⟨hf, he⟩ := hF i (Finset.mem_insert_self _ _)
    obtain ⟨hg, he'⟩ := ih (fun j hj => hF j (Finset.mem_insert_of_mem hj))
    have ht : (fun n => (∑ j ∈ insert i s, F j).coeff n * h ^ n) =
        (fun n => (F i).coeff n * h ^ n + (∑ j ∈ s, F j).coeff n * h ^ n) := by
      funext n
      rw [Finset.sum_insert hi, map_add, add_mul]
    rw [ht]
    refine ⟨hf.add hg, ?_⟩
    rw [strongSum_add hf hg, he, he', Finset.sum_insert hi]

end
end Surreal.Surcomplex
