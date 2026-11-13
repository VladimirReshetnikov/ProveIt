import DiophantineConsistency.Sign17ExactDegree
import Mathlib.Order.WellFounded

/-! SOURCE-ONLY. Conditional rank certificate; no concrete table checked here. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KRankCertificate
open MF.WangTiles942 WangTiles942

theorem candidate_positions (f : Fin 942 → Fin 942)
    (hzero : f 0 = 0)
    (hnonzero : ∀ i, i ≠ 0 → f i ≠ 0)
    (hdesc : ∀ i j, i < j → i ≠ 0 →
      selectorWeight (tile (f j)) < selectorWeight (tile (f i))) :
    ∀ i, physicalMap (f i) = i := by
  have hm : StrictMono (fun i => physicalMap (f i)) := by
    intro i j hij
    by_cases hi : i = 0
    · subst i
      have hj : j ≠ 0 := by
        intro h
        subst j
        exact (lt_irrefl _ hij)
      have hmj : physicalMap (f j) ≠ 0 := by
        intro h
        apply hnonzero j hj
        apply physicalMap_injective
        simpa only [physicalMap_zero] using h
      simpa only [hzero, physicalMap_zero] using (Fin.pos_iff_ne_zero.mpr hmj)
    · have hj : j ≠ 0 := by
        intro h
        subst j
        exact (not_lt_of_ge (Fin.zero_le i) hij)
      exact (physical_lt_iff_weight (f i) (f j) (hnonzero i hi) (hnonzero j hj)).2
        (hdesc i j hij hi)
  intro i
  exact le_antisymm hm.apply_le hm.le_apply

end DiophantineConsistency.Sign17KRankCertificate
#print axioms DiophantineConsistency.Sign17KRankCertificate.candidate_positions
