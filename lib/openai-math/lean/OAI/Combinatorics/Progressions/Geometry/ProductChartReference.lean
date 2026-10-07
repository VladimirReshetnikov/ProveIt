import Mathlib.MeasureTheory.Constructions.Pi

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ENNReal

theorem ennreal_smul_sigmaFinite {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] (c : ℝ≥0∞) (hc : c ≠ ∞) : SigmaFinite (c • μ) where
  out' := ⟨{
    set := spanningSets μ
    set_mem := fun _ => trivial
    finite := by
      intro i
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top hc.lt_top (measure_spanningSets_lt_top μ i)
    spanning := iUnion_spanningSets μ }⟩

theorem piChart_reference_map {I : Type*} [Fintype I] {X Y : I → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    (ν : ∀ i, Measure (Y i)) [∀ i, SigmaFinite (ν i)]
    (q : ∀ i, X i → Y i) (hq : ∀ i, Measurable (q i)) (S : ∀ i, Set (X i))
    (hmap : ∀ i, ((μ i).restrict (S i)).map (q i) = (ν i).restrict (q i '' S i)) :
    ((Measure.pi μ).restrict (Set.univ.pi S)).map (fun x i => q i (x i)) =
      (Measure.pi ν).restrict ((fun x i => q i (x i)) '' Set.univ.pi S) := by
  let : ∀ i, SigmaFinite (((μ i).restrict (S i)).map (q i)) := by
    intro i
    rw [hmap i]
    infer_instance
  rw [Measure.restrict_pi_pi, Measure.pi_map_pi (fun i => (hq i).aemeasurable)]
  simp_rw [hmap]
  rw [← Measure.restrict_pi_pi]
  congr 1
  exact (Set.piMap_image_univ_pi q S).symm

end Erdos3

end

end OAI
