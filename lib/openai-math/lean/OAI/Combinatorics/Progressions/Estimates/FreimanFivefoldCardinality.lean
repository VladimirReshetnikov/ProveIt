import OAI.Combinatorics.Progressions.Estimates.FreimanInverseLift
import OAI.Combinatorics.Progressions.Geometry.DenseRealBoxCell

namespace OAI

section

namespace Erdos3.FreimanModel

open scoped Pointwise

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

def fiveTermValue (x : Fin 5 → G) : G := x 0 + x 1 + x 2 - x 3 - x 4

theorem fiveTermValue_eq_iff {A : Set G} {B : Set H} {f : G → H}
    (hf : IsAddFreimanIso 5 A B f) {x y : Fin 5 → G}
    (hx : ∀ i, x i ∈ A) (hy : ∀ i, y i ∈ A) :
    fiveTermValue (f ∘ x) = fiveTermValue (f ∘ y) ↔ fiveTermValue x = fiveTermValue y := by
  let s : Multiset G := x 0 ::ₘ x 1 ::ₘ x 2 ::ₘ y 3 ::ₘ y 4 ::ₘ 0
  let t : Multiset G := y 0 ::ₘ y 1 ::ₘ y 2 ::ₘ x 3 ::ₘ x 4 ::ₘ 0
  have hsA : ∀ ⦃a⦄, a ∈ s → a ∈ A := by
    intro a ha
    simp only [s, Multiset.mem_cons, Multiset.notMem_zero, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    exacts [hx 0, hx 1, hx 2, hy 3, hy 4]
  have htA : ∀ ⦃a⦄, a ∈ t → a ∈ A := by
    intro a ha
    simp only [t, Multiset.mem_cons, Multiset.notMem_zero, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    exacts [hy 0, hy 1, hy 2, hx 3, hx 4]
  have hrel := hf.map_sum_eq_map_sum hsA htA (by simp [s]) (by simp [t])
  simp only [fiveTermValue, Function.comp_apply, sub_sub, sub_eq_sub_iff_add_eq_add, add_assoc]
  simpa [s, t, add_assoc] using hrel

theorem card_fiveTermValues_le [DecidableEq G] [DecidableEq H] [Fintype H]
    (A : Finset G) {B : Set H} (f : G → H)
    (hf : IsAddFreimanIso 5 (A : Set G) B f) :
    ((Fintype.piFinset fun _ : Fin 5 => A).image fiveTermValue).card ≤ Fintype.card H := by
  classical
  let U := Fintype.piFinset fun _ : Fin 5 => A
  have hrel : ∀ x ∈ U, ∀ y ∈ U,
      fiveTermValue x = fiveTermValue y ↔
        fiveTermValue (f ∘ x) = fiveTermValue (f ∘ y) := by
    intro x hx y hy
    exact (fiveTermValue_eq_iff hf (Fintype.mem_piFinset.mp hx)
      (Fintype.mem_piFinset.mp hy)).symm
  have hcard := card_image_eq_of_same_fibers U fiveTermValue (fun x => fiveTermValue (f ∘ x)) hrel
  change (U.image fiveTermValue).card ≤ _
  rw [hcard]
  exact Finset.card_le_univ _

theorem sub_subset_fiveTermValues [DecidableEq G] (A P : Finset G)
    (hP : P ⊆ 2 • A - 2 • A) :
    A - P ⊆ (Fintype.piFinset fun _ : Fin 5 => A).image fiveTermValue := by
  classical
  intro z hz
  obtain ⟨a, ha, p, hp, rfl⟩ := Finset.mem_sub.mp hz
  obtain ⟨q, hq, hval⟩ := mem_two_nsmul_sub_two_nsmul_iff.mp (hP hp)
  let x : Fin 5 → G := ![a, q.neg₁, q.neg₂, q.pos₁, q.pos₂]
  have hx : x ∈ Fintype.piFinset (fun _ : Fin 5 => A) := by
    apply Fintype.mem_piFinset.mpr
    intro i
    fin_cases i
    · exact ha
    · exact hq.2.2.1
    · exact hq.2.2.2
    · exact hq.1
    · exact hq.2.1
  refine Finset.mem_image.mpr ⟨x, hx, ?_⟩
  rw [← hval]
  change a + q.neg₁ + q.neg₂ - q.pos₁ - q.pos₂ = a - (q.pos₁ + q.pos₂ - q.neg₁ - q.neg₂)
  abel

theorem card_sub_le_of_fourfold_subset [DecidableEq G] [DecidableEq H] [Fintype H]
    (A P : Finset G) {B : Set H} (f : G → H)
    (hf : IsAddFreimanIso 5 (A : Set G) B f) (hP : P ⊆ 2 • A - 2 • A) :
    (A - P).card ≤ Fintype.card H :=
  (Finset.card_le_card (sub_subset_fiveTermValues A P hP)).trans (card_fiveTermValues_le A f hf)

end Erdos3.FreimanModel

end

end OAI
