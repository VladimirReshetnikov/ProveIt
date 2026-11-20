import Mathlib.Data.Finset.Prod
import Mathlib.Order.Interval.Finset.Nat
import MoserWorm.UpperBound.Certificate.Families
import MoserWorm.UpperBound.Certificate.Partition

namespace MoserWorm.UpperBound.Certificate

abbrev insideRect := Partition.insideOK

/-- Cell as a finite set of grid points. -/
def cellSet (r : ℕ × ℕ × ℕ × ℕ) : Finset (ℕ × ℕ) :=
  Finset.Icc r.1 r.2.1 ×ˢ Finset.Icc r.2.2.1 r.2.2.2

lemma mem_cellSet {r : ℕ × ℕ × ℕ × ℕ} {pq : ℕ × ℕ} :
    pq ∈ cellSet r ↔ (r.1 ≤ pq.1 ∧ pq.1 ≤ r.2.1) ∧
      (r.2.2.1 ≤ pq.2 ∧ pq.2 ≤ r.2.2.2) := by
  simp [cellSet, Finset.mem_product, Finset.mem_Icc]

lemma card_cellSet {r : ℕ × ℕ × ℕ × ℕ} (h1 : r.1 ≤ r.2.1) (h2 : r.2.2.1 ≤ r.2.2.2) :
    (cellSet r).card = (r.2.1 - r.1 + 1) * (r.2.2.2 - r.2.2.1 + 1) := by
  rw [cellSet, Finset.card_product, Nat.card_Icc, Nat.card_Icc]
  congr 1 <;> omega

/-- The disjointness relation tested by the checker. -/
def disjRel (r1 r2 : ℕ × ℕ × ℕ × ℕ) : Prop :=
  r1.2.1 < r2.1 ∨ r2.2.1 < r1.1 ∨ r1.2.2.2 < r2.2.2.1 ∨ r2.2.2.2 < r1.2.2.1

lemma cellSet_disjoint {r1 r2 : ℕ × ℕ × ℕ × ℕ} (h : disjRel r1 r2) :
    Disjoint (cellSet r1) (cellSet r2) := by
  rw [Finset.disjoint_left]
  rintro ⟨p, q⟩ h1 h2
  rw [mem_cellSet] at h1 h2
  rcases h with h | h | h | h <;> omega

/-- `pairwiseOk` implies pairwise disjointness. -/
lemma pairwiseOk_pairwise (l : List (ℕ × ℕ × ℕ × ℕ))
    (h : checkTree.pairwiseOk l = true) : l.Pairwise disjRel := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
    obtain ⟨a, b, c, d⟩ := x
    rw [checkTree.pairwiseOk] at h
    rw [Bool.and_eq_true] at h
    refine List.Pairwise.cons (fun r2 hr2 => ?_) (ih h.2)
    have := (List.all_eq_true.mp h.1) r2 hr2
    obtain ⟨a2, b2, c2, d2⟩ := r2
    simp only [Bool.or_eq_true, decide_eq_true_eq] at this
    unfold disjRel
    tauto

/-- Disjoint from every member implies disjoint from the folded union. -/
lemma disjoint_foldr_union (x : Finset (ℕ × ℕ)) (l : List (Finset (ℕ × ℕ)))
    (h : ∀ y ∈ l, Disjoint x y) :
    Disjoint x (l.foldr (· ∪ ·) ∅) := by
  induction l with
  | nil => simp
  | cons y ys ih =>
    rw [List.foldr_cons, Finset.disjoint_union_right]
    exact ⟨h y (by simp), ih (fun z hz => h z (by simp [hz]))⟩

/-- Card of a disjoint folded union. -/
lemma card_foldr_union (l : List (Finset (ℕ × ℕ)))
    (h : l.Pairwise (fun a b => Disjoint a b)) :
    (l.foldr (· ∪ ·) ∅).card = (l.map Finset.card).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.pairwise_cons] at h
    rw [List.foldr_cons, Finset.card_union_of_disjoint
      (disjoint_foldr_union x xs h.1), List.map_cons, List.sum_cons, ih h.2]

lemma mem_foldr_union {l : List (Finset (ℕ × ℕ))} {pq : ℕ × ℕ}
    (h : pq ∈ l.foldr (· ∪ ·) ∅) : ∃ f ∈ l, pq ∈ f := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    rw [List.foldr_cons, Finset.mem_union] at h
    rcases h with h | h
    · exact ⟨x, by simp, h⟩
    · obtain ⟨f, hf, hpq⟩ := ih h
      exact ⟨f, by simp [hf], hpq⟩

/-- The refinement covering argument: inside + disjoint + cardinality
imply that some cell contains the point. -/
lemma exists_cell_of_cover (rects : List (ℕ × ℕ × ℕ × ℕ)) (R : ℕ × ℕ × ℕ × ℕ)
    (hin : ∀ r ∈ rects, insideRect R r = true)
    (hpw : rects.Pairwise disjRel)
    (harea : rects.foldl
        (fun acc x => acc + (x.2.1 - x.1 + 1) * (x.2.2.2 - x.2.2.1 + 1)) 0
      = (R.2.1 - R.1 + 1) * (R.2.2.2 - R.2.2.1 + 1))
    {P Q : ℕ} (hP : R.1 ≤ P ∧ P ≤ R.2.1) (hQ : R.2.2.1 ≤ Q ∧ Q ≤ R.2.2.2) :
    ∃ r ∈ rects, r.1 ≤ P ∧ P ≤ r.2.1 ∧ r.2.2.1 ≤ Q ∧ Q ≤ r.2.2.2 := by
  have hinside : ∀ r ∈ rects, R.1 ≤ r.1 ∧ r.1 ≤ r.2.1 ∧ r.2.1 ≤ R.2.1 ∧
      R.2.2.1 ≤ r.2.2.1 ∧ r.2.2.1 ≤ r.2.2.2 ∧ r.2.2.2 ≤ R.2.2.2 := by
    intro r hr
    have := hin r hr
    simp only [insideRect, Partition.insideOK, Bool.and_eq_true, decide_eq_true_eq] at this
    tauto
  -- the folded union of the cells
  set U := (rects.map cellSet).foldr (· ∪ ·) ∅ with hU
  have hsub : U ⊆ cellSet R := by
    intro pq hpq
    obtain ⟨f, hf, hmem⟩ := mem_foldr_union hpq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hf
    have hins := hinside r hr
    rw [mem_cellSet] at hmem ⊢
    omega
  have hpwd : (rects.map cellSet).Pairwise (fun a b => Disjoint a b) :=
    List.Pairwise.map _ (fun a b hab => cellSet_disjoint hab) hpw
  have hcardU : U.card = (rects.map (fun r => (r.2.1 - r.1 + 1) *
      (r.2.2.2 - r.2.2.1 + 1))).sum := by
    rw [hU, card_foldr_union _ hpwd, List.map_map]
    congr 1
    refine List.map_congr_left (fun r hr => ?_)
    have hins := hinside r hr
    exact card_cellSet (by omega) (by omega)
  have hfold : ∀ (l : List (ℕ × ℕ × ℕ × ℕ)) (acc : ℕ), l.foldl
      (fun acc x => acc + (x.2.1 - x.1 + 1) * (x.2.2.2 - x.2.2.1 + 1)) acc
      = acc + (l.map (fun r => (r.2.1 - r.1 + 1) * (r.2.2.2 - r.2.2.1 + 1))).sum := by
    intro l
    induction l with
    | nil => simp
    | cons x xs ih =>
      intro acc
      rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]
      ring
  have hcardR : (cellSet R).card = U.card := by
    rw [hcardU, card_cellSet (by omega) (by omega), ← harea, hfold rects 0,
      Nat.zero_add]
  have hUeq : U = cellSet R :=
    Finset.eq_of_subset_of_card_le hsub (le_of_eq hcardR)
  have hPQ : (P, Q) ∈ U := by
    rw [hUeq, mem_cellSet]
    exact ⟨hP, hQ⟩
  obtain ⟨f, hf, hmem⟩ := mem_foldr_union hPQ
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hf
  rw [mem_cellSet] at hmem
  exact ⟨r, hr, by omega⟩


end MoserWorm.UpperBound.Certificate
