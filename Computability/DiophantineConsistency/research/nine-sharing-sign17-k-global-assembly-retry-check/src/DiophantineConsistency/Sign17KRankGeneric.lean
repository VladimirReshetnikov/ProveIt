import DiophantineConsistency.Sign17ExactDegree
import Mathlib.Order.WellFounded

/-! SOURCE-ONLY. Generic conditional rank criterion, without a concrete provider. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KRankGeneric

theorem candidate_positions (rank f : Fin 942 → Fin 942) (weight : Fin 942 → ℕ)
    (hrankzero : rank 0 = 0) (hrankinj : Function.Injective rank)
    (horder : ∀ a b, a ≠ 0 → b ≠ 0 →
      (rank a < rank b ↔ weight b < weight a))
    (hzero : f 0 = 0)
    (hnonzero : ∀ i, i ≠ 0 → f i ≠ 0)
    (hdesc : ∀ i j, i < j → i ≠ 0 → weight (f j) < weight (f i)) :
    ∀ i, rank (f i) = i := by
  have hm : StrictMono (fun i => rank (f i)) := by
    intro i j hij
    by_cases hi : i = 0
    · subst i
      have hj : j ≠ 0 := by
        intro h
        subst j
        exact (lt_irrefl _ hij)
      have hmj : rank (f j) ≠ 0 := by
        intro h
        apply hnonzero j hj
        apply hrankinj
        simpa only [hrankzero] using h
      simpa only [hzero, hrankzero] using (Fin.pos_iff_ne_zero.mpr hmj)
    · have hj : j ≠ 0 := by
        intro h
        subst j
        exact (not_lt_of_ge (Fin.zero_le i) hij)
      exact (horder (f i) (f j) (hnonzero i hi) (hnonzero j hj)).2
        (hdesc i j hij hi)
  intro i
  exact le_antisymm hm.apply_le hm.le_apply

end DiophantineConsistency.Sign17KRankGeneric
#print axioms DiophantineConsistency.Sign17KRankGeneric.candidate_positions
