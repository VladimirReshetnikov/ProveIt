import OAI.Combinatorics.Progressions.Estimates.FiniteEventUnion
import OAI.Combinatorics.Progressions.Estimates.FiniteProductWitness
import OAI.Combinatorics.Progressions.Estimates.FiniteReciprocalTenthTail

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem finite_witness_probability_tenth_tail {Ω : Type*} [Fintype Ω]
    (w : FiniteProbabilityWeights Ω) (E : ℕ → Ω → Prop) {R B : ℕ} (hR : 0 < R)
    {η : ℝ} (hη : 0 ≤ η)
    (hE : ∀ d ∈ Finset.Ioc R B, w.eventProbability (E d) ≤ 1 / (d : ℝ) ^ 10 + η) :
    w.eventProbability (fun x => ∃ d ∈ Finset.Ioc R B, E d x) ≤
      1 / (9 * (R : ℝ) ^ 9) + (B : ℝ) * η := by
  have hunion := w.eventProbability_union_bound
    (fun x => ∃ d ∈ Finset.Ioc R B, E d x)
    (fun (d : Finset.Ioc R B) x => E d.val x)
    (by intro x hx; obtain ⟨d, hd, hdx⟩ := hx; exact ⟨⟨d, hd⟩, hdx⟩)
  have htail := finite_reciprocal_tenth_tail (Finset.Ioc R B) hR
    (fun d hd => (Finset.mem_Ioc.mp hd).1)
  have hcard : ((Finset.Ioc R B).card : ℝ) ≤ B := by
    exact_mod_cast (show (Finset.Ioc R B).card ≤ B by simp)
  calc
    _ ≤ ∑ d : Finset.Ioc R B, (1 / (d.val : ℝ) ^ 10 + η) :=
      hunion.trans (Finset.sum_le_sum (fun d _ => hE d.val d.property))
    _ = (∑ d ∈ Finset.Ioc R B, 1 / (d : ℝ) ^ 10) + ((Finset.Ioc R B).card : ℝ) * η := by
      calc
        _ = ∑ d ∈ Finset.Ioc R B, (1 / (d : ℝ) ^ 10 + η) :=
          Finset.sum_coe_sort (Finset.Ioc R B) (fun d : ℕ => 1 / (d : ℝ) ^ 10 + η)
        _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := add_le_add htail (mul_le_mul_of_nonneg_right hcard hη)

theorem finite_product_witness_probability {Ω I : Type*} [Fintype Ω]
    (w : FiniteProbabilityWeights Ω) (S : Finset I) (f : Ω → I → ℕ)
    (single composite : ℕ → Ω → Prop) {R Q : ℕ} (hR : 0 < R)
    (hQ : ∀ x i, i ∈ S → f x i ≤ Q)
    (hsingle : ∀ x i, i ∈ S → R < f x i → single (f x i) x)
    (hcomposite : ∀ x T, T ⊆ S → R < ∏ i ∈ T, f x i →
      (∏ i ∈ T, f x i) ≤ R ^ 2 → composite (∏ i ∈ T, f x i) x)
    {η : ℝ} (hη : 0 ≤ η)
    (hsingleProb : ∀ d ∈ Finset.Ioc R Q,
      w.eventProbability (single d) ≤ 1 / (d : ℝ) ^ 10 + η)
    (hcompositeProb : ∀ d ∈ Finset.Ioc R (R ^ 2),
      w.eventProbability (composite d) ≤ 1 / (d : ℝ) ^ 10 + η) :
    w.eventProbability (fun x => R < ∏ i ∈ S, f x i) ≤
      2 / (9 * (R : ℝ) ^ 9) + ((Q : ℝ) + (R : ℝ) ^ 2) * η := by
  let Esingle := fun x => ∃ d ∈ Finset.Ioc R Q, single d x
  let Ecomposite := fun x => ∃ d ∈ Finset.Ioc R (R ^ 2), composite d x
  have hcover (x) (hx : R < ∏ i ∈ S, f x i) : Esingle x ∨ Ecomposite x := by
    obtain h | ⟨T, hT, hlo, hhi⟩ := finite_product_witness S (f x) hR hx
    · obtain ⟨i, hi, hlarge⟩ := h
      exact Or.inl ⟨f x i, Finset.mem_Ioc.mpr ⟨hlarge, hQ x i hi⟩, hsingle x i hi hlarge⟩
    · exact Or.inr ⟨∏ i ∈ T, f x i, Finset.mem_Ioc.mpr ⟨hlo, hhi⟩,
        hcomposite x T hT hlo hhi⟩
  have hsingleTail := finite_witness_probability_tenth_tail w single hR hη hsingleProb
  have hcompositeTail := finite_witness_probability_tenth_tail w composite hR hη hcompositeProb
  calc
    _ ≤ w.eventProbability (fun x => Esingle x ∨ Ecomposite x) :=
      w.eventProbability_mono _ _ hcover
    _ ≤ w.eventProbability Esingle + w.eventProbability Ecomposite :=
      w.eventProbability_or_le Esingle Ecomposite
    _ ≤ (1 / (9 * (R : ℝ) ^ 9) + (Q : ℝ) * η) +
        (1 / (9 * (R : ℝ) ^ 9) + ((R ^ 2 : ℕ) : ℝ) * η) :=
      add_le_add hsingleTail hcompositeTail
    _ = _ := by push_cast; ring

end Erdos3

end

end OAI
