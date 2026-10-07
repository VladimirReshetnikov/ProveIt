import Mathlib.MeasureTheory.Group.Integral
import OAI.Combinatorics.Progressions.Fourier.TorusCellBudget

namespace OAI

section

namespace Erdos3

open MeasureTheory CircleFourier
open scoped BigOperators Classical

theorem ambientTorusTent_integrable {G J : Type*} [TopologicalSpace G]
    [MeasurableSpace G] [BorelSpace G] [Fintype J]
    (μ : Measure G) [IsFiniteMeasure μ] (f : G → J → UnitAddCircle) (hf : Continuous f) (q : ℕ) :
    Integrable (fun x => ambientTorusTent q (f x)) μ := by
  apply Integrable.of_bound ((ambientTorusTent_lipschitz q).continuous.comp hf).aestronglyMeasurable 1
  exact ae_of_all μ (fun x => by
    change ‖ambientTorusTent q (f x)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (ambientTorusTent_range q (f x)).1]
    exact (ambientTorusTent_range q (f x)).2)

noncomputable def ambientTentMass {G J : Type*} [MeasurableSpace G] [Fintype J]
    (μ : Measure G) (f : G → J → UnitAddCircle) (q : ℕ) : ℝ := ∫ x, ambientTorusTent q (f x) ∂μ

theorem ambientTentMass_le_one {G J : Type*} [TopologicalSpace G]
    [MeasurableSpace G] [BorelSpace G] [Fintype J]
    (μ : Measure G) [IsProbabilityMeasure μ] (f : G → J → UnitAddCircle) (hf : Continuous f) (q : ℕ) :
    ambientTentMass μ f q ≤ 1 := by
  have h := integral_mono (ambientTorusTent_integrable μ f hf q) (integrable_const (1 : ℝ))
    (fun x => (ambientTorusTent_range q (f x)).2)
  simpa only [ambientTentMass, integral_const, probReal_univ, one_smul] using h

theorem ambientTentMass_lower {G J : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G] [MeasurableAdd₂ G] [Fintype J]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (f : G →+ (J → UnitAddCircle)) (hf : Continuous f) {q : ℕ} (hq : 0 < q) :
    1 / (2 * (q : ℝ) ^ Fintype.card J) ≤ ambientTentMass μ f q := by
  obtain ⟨a, ha⟩ := ambientTorus_image_cover f hq
  have hi (i : J → Fin q) : Integrable (fun x => ambientTorusTent q (f (x - a i))) μ :=
    ambientTorusTent_integrable μ _ (hf.comp (continuous_id.sub continuous_const)) q
  have htrans (i : J → Fin q) :
      (∫ x, ambientTorusTent q (f (x - a i)) ∂μ) = ambientTentMass μ f q := by
    simpa only [ambientTentMass, sub_eq_add_neg, add_comm] using
      integral_add_left_eq_self (μ := μ) (fun x => ambientTorusTent q (f x)) (-a i)
  have hpoint (x : G) : 1 / 2 ≤ ∑ i : J → Fin q, ambientTorusTent q (f (x - a i)) := by
    obtain ⟨i, hi⟩ := ha x
    have hsmall : ‖f (x - a i)‖ ≤ 2 / (q : ℝ) := by
      simpa only [map_sub, dist_eq_norm] using hi
    exact (ambientTorusTent_ge_half hq _ hsmall).trans
      (Finset.single_le_sum (fun j _ => (ambientTorusTent_range q (f (x - a j))).1) (Finset.mem_univ i))
  have hsum := integral_mono (integrable_const (1 / 2 : ℝ))
    (integrable_finsetSum _ (fun i _ => hi i)) hpoint
  rw [integral_finsetSum _ (fun i _ => hi i)] at hsum
  simp only [integral_const, probReal_univ, one_smul, htrans, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] at hsum
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  apply (div_le_iff₀ (by positivity : 0 < 2 * (q : ℝ) ^ Fintype.card J)).mpr
  nlinarith

end Erdos3

end

end OAI
