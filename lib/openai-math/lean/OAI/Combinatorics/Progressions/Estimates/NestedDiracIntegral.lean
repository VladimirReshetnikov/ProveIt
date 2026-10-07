import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem integral_dirac_first {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] (z : Z) (f : Z × X → ℝ) (hf : Measurable f) :
    (∫ p, f p ∂(Measure.dirac z).prod ν) = ∫ x, f (z, x) ∂ν := by
  rw [Measure.dirac_prod]
  exact integral_map measurable_prodMk_left.aemeasurable hf.aestronglyMeasurable

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem integral_dirac_first_nested {Z X Y : Type*}
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (z : Z) (f : (Z × X) × Y → ℝ) (hf : Measurable f) :
    (∫ p, f p ∂((Measure.dirac z).prod μ).prod ν) =
      ∫ p : X × Y, f ((z, p.1), p.2) ∂μ.prod ν := by
  have he : ((Measure.dirac z).prod μ).prod ν =
      (μ.prod ν).map (fun p : X × Y => ((z, p.1), p.2)) := by
    calc
      _ = (μ.map (Prod.mk z)).prod (ν.map id) := by
        rw [Measure.dirac_prod, Measure.map_id]
      _ = _ := Measure.map_prod_map μ ν measurable_prodMk_left measurable_id
  rw [he]
  exact integral_map
    ((measurable_const.prodMk measurable_fst).prodMk measurable_snd).aemeasurable hf.aestronglyMeasurable

end Erdos3

end

end OAI
