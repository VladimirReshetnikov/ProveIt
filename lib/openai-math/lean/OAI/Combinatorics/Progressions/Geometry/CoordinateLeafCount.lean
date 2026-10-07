/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.PhysicalPairAccuracyLogBounds

namespace OAI

section

namespace Erdos3.CoordinateDecisionTree

universe u v

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v}

theorem trace_eq_of_agree (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (base input other : ∀ i, Value i)
    (hagree : ∀ i ∈ (trace tree I base input).1, other i = input i) :
    trace tree I base other = trace tree I base input := by
  induction tree generalizing I base with
  | leaf => rfl
  | split i children ih =>
    have hi : i ∈ (trace (children (input i)) (insert i I) (Function.update base i (input i)) input).1 :=
      trace_contains _ _ _ _ (Finset.mem_insert_self _ _)
    have he : other i = input i := hagree i hi
    simp only [trace, he]
    exact ih (input i) (insert i I) (Function.update base i (input i)) hagree

theorem trace_outside (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (base input : ∀ i, Value i) (j : ι) (hj : j ∉ (trace tree I base input).1) :
    (trace tree I base input).2 j = base j := by
  induction tree generalizing I base with
  | leaf => rfl
  | split i children ih =>
    have hji : j ≠ i := by
      intro he
      subst j
      exact hj (trace_contains (children (input i)) (insert i I)
        (Function.update base i (input i)) input (Finset.mem_insert_self _ _))
    exact (ih (input i) (insert i I) (Function.update base i (input i)) hj).trans
      (Function.update_of_ne hji _ _)

def traceCylinder (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (base input : ∀ i, Value i) : ProductCylinder Value :=
  ProductCylinder.ofAssignment (trace tree I base input).1 (trace tree I base input).2

theorem traceCylinder_assignment (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (base input : ∀ i, Value i) :
    (traceCylinder tree I base input).assignment base = (trace tree I base input).2 := by
  funext i
  by_cases hi : i ∈ (trace tree I base input).1
  · exact ProductCylinder.assignment_mem _ base i hi
  · change (if h : i ∈ (trace tree I base input).1 then _ else base i) = _
    rw [dite_eq_right hi]
    exact (trace_outside tree I base input i hi).symm

theorem traceCylinder_contains (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (base input : ∀ i, Value i) (hinput : ∀ i ∈ I, input i = base i) :
    (traceCylinder tree I base input).Contains input := by
  intro i
  exact (trace_agrees tree I base input (fun j hj => (hinput j hj).symm) i i.property).symm

theorem traceCylinder_contains_iff (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (base input other : ∀ i, Value i) (hinput : ∀ i ∈ I, input i = base i) :
    (traceCylinder tree I base input).Contains other ↔
      (∀ i ∈ I, other i = base i) ∧ traceCylinder tree I base other = traceCylinder tree I base input := by
  have htrace := trace_agrees tree I base input (fun i hi => (hinput i hi).symm)
  constructor
  · intro h
    have hagree : ∀ i ∈ (trace tree I base input).1, other i = input i := by
      intro i hi
      exact (h ⟨i, hi⟩).trans (htrace i hi)
    have heq := trace_eq_of_agree tree I base input other hagree
    refine ⟨fun i hi => (hagree i (trace_contains tree I base input hi)).trans (hinput i hi), ?_⟩
    unfold traceCylinder
    rw [heq]
  · rintro ⟨hother, heq⟩
    rw [← heq]
    exact traceCylinder_contains tree I base other hother

end Erdos3.CoordinateDecisionTree

end

section

namespace Erdos3.CoordinateDecisionTree

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Value : ι → Type*}
  [∀ i, Fintype (Value i)]

noncomputable def leafCylinders (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (base : ∀ i, Value i) : Finset (ProductCylinder Value) :=
  (Finset.univ.filter (fun input : ∀ i, Value i => ∀ i ∈ I, input i = base i)).image
    (traceCylinder tree I base)

theorem mem_leafCylinders (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (base : ∀ i, Value i) (c : ProductCylinder Value) :
    c ∈ leafCylinders tree I base ↔
      ∃ input, (∀ i ∈ I, input i = base i) ∧ traceCylinder tree I base input = c := by
  simp only [leafCylinders, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]

theorem leafCylinders_contains_iff (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (base input : ∀ i, Value i) (c : ProductCylinder Value) (hc : c ∈ leafCylinders tree I base) :
    c.Contains input ↔ (∀ i ∈ I, input i = base i) ∧ traceCylinder tree I base input = c := by
  obtain ⟨source, hs, rfl⟩ := (mem_leafCylinders tree I base c).mp hc
  exact traceCylinder_contains_iff tree I base source input hs

theorem leafCylinders_unique (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (base input : ∀ i, Value i) (c d : ProductCylinder Value)
    (hc : c ∈ leafCylinders tree I base) (hd : d ∈ leafCylinders tree I base)
    (hci : c.Contains input) (hdi : d.Contains input) : c = d :=
  ((leafCylinders_contains_iff tree I base input c hc).mp hci).2.symm.trans
    ((leafCylinders_contains_iff tree I base input d hd).mp hdi).2

theorem leafCylinders_indicator_sum (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (base input : ∀ i, Value i) :
    (∑ c ∈ leafCylinders tree I base, productFiberIndicator c.1 (c.assignment base) input) =
      productFiberIndicator I base input := by
  have he (c : ProductCylinder Value) (hc : c ∈ leafCylinders tree I base) :
      productFiberIndicator c.1 (c.assignment base) input =
        if (∀ i ∈ I, input i = base i) ∧ traceCylinder tree I base input = c then 1 else 0 := by
    simp only [productFiberIndicator, ← ProductCylinder.contains_iff,
      leafCylinders_contains_iff tree I base input c hc]
  calc
    _ = ∑ c ∈ leafCylinders tree I base,
        if (∀ i ∈ I, input i = base i) ∧ traceCylinder tree I base input = c then (1 : ℝ) else 0 :=
      Finset.sum_congr rfl he
    _ = _ := by
      by_cases hi : ∀ i ∈ I, input i = base i
      · have hc : traceCylinder tree I base input ∈ leafCylinders tree I base :=
          (mem_leafCylinders tree I base _).mpr ⟨input, hi, rfl⟩
        have hvalue : productFiberIndicator I base input = 1 := by
          unfold productFiberIndicator
          exact ite_eq_left hi
        rw [hvalue, Finset.sum_eq_single (traceCylinder tree I base input)]
        · exact ite_eq_left ⟨hi, rfl⟩
        · intro c _ hne
          exact ite_eq_right (fun h => hne h.2.symm)
        · exact fun hn => False.elim (hn hc)
      · have hvalue : productFiberIndicator I base input = 0 := by
          unfold productFiberIndicator
          exact ite_eq_right hi
        rw [hvalue]
        apply Finset.sum_eq_zero
        intro c _
        exact ite_eq_right (fun h => hi h.1)

theorem leafCylinders_partition (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (base : ∀ i, Value i) (f : (∀ i, Value i) → ℝ) (input : ∀ i, Value i) :
    (∑ c ∈ leafCylinders tree I base, productFiberIndicator c.1 (c.assignment base) input * f input) =
      productFiberIndicator I base input * f input := by
  rw [← Finset.sum_mul, leafCylinders_indicator_sum]

theorem leafCylinders_partition_empty (tree : CoordinateDecisionTree ι Value)
    (base : ∀ i, Value i) (f : (∀ i, Value i) → ℝ) (input : ∀ i, Value i) :
    (∑ c ∈ leafCylinders tree ∅ base, productFiberIndicator c.1 (c.assignment base) input * f input) = f input := by
  simpa [productFiberIndicator] using leafCylinders_partition tree ∅ base f input

theorem leafCylinders_mass_sum (tree : CoordinateDecisionTree ι Value) (I : Finset ι)
    (base : ∀ i, Value i) (w : (∀ i, Value i) → ℝ) :
    (∑ c ∈ leafCylinders tree I base, productFiberMass w c.1 (c.assignment base)) =
      productFiberMass w I base := by
  unfold productFiberMass
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, leafCylinders_indicator_sum]

end Erdos3.CoordinateDecisionTree

end

section

namespace Erdos3.CoordinateDecisionTree

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : ι → Type*}
  [∀ i, Fintype (Y i)]
  {Good : Finset ι → (∀ i, Y i) → Prop}
  {tree : CoordinateDecisionTree ι Y} {I : Finset ι} {base : ∀ i, Y i} {d : ℕ}

theorem Valid.leaf_good (h : Valid Good I base tree d)
    (c : ProductCylinder Y) (hc : c ∈ leafCylinders tree I base) :
    Good c.1 (c.assignment base) := by
  obtain ⟨input, _, rfl⟩ := (mem_leafCylinders tree I base c).mp hc
  rw [traceCylinder_assignment]
  exact h.trace_good input

theorem Valid.leaf_card_le (h : Valid Good I base tree d)
    (c : ProductCylinder Y) (hc : c ∈ leafCylinders tree I base) : c.1.card ≤ I.card + d := by
  obtain ⟨input, _, rfl⟩ := (mem_leafCylinders tree I base c).mp hc
  exact h.trace_card_le input

theorem Valid.leafCylinders_subset_bounded (h : Valid Good I base tree d)
    {A : ℕ} (hA : I.card + d ≤ A) :
    leafCylinders tree I base ⊆ ProductCylinder.bounded (X := Y) A := by
  intro c hc
  exact (ProductCylinder.mem_bounded A c).mpr ((h.leaf_card_le c hc).trans hA)

theorem Valid.leafCylinders_card_le_exp (h : Valid Good I base tree d)
    {A : ℕ} (hA : I.card + d ≤ A) {P W : ℝ} (hP : 0 ≤ P) (hW : 0 ≤ W)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hY : ∀ i, (Fintype.card (Y i) : ℝ) ≤ Real.exp W) :
    ((leafCylinders tree I base).card : ℝ) ≤ Real.exp ((A : ℝ) * (P + W + 1)) :=
  (Nat.cast_le.mpr (Finset.card_le_card (h.leafCylinders_subset_bounded hA))).trans
    (ProductCylinder.bounded_card_le_exp hP hW hcount hY A)

noncomputable def leafSourceAssignments (X : ι → Type*) [∀ i, Fintype (X i)]
    (tree : CoordinateDecisionTree ι Y) (I : Finset ι) (base : ∀ i, Y i) :
    Finset (Σ c : ProductCylinder Y, ∀ i : c.1, X i.val) :=
  (leafCylinders tree I base).sigma (fun _c => Finset.univ)

theorem mem_leafSourceAssignments (X : ι → Type*) [∀ i, Fintype (X i)]
    (tree : CoordinateDecisionTree ι Y) (I : Finset ι) (base : ∀ i, Y i)
    (z : Σ c : ProductCylinder Y, ∀ i : c.1, X i.val) :
    z ∈ leafSourceAssignments X tree I base ↔ z.1 ∈ leafCylinders tree I base := by
  simp only [leafSourceAssignments, Finset.mem_sigma, Finset.mem_univ, and_true]

theorem Valid.leafSourceAssignments_card_le_exp (h : Valid Good I base tree d)
    (X : ι → Type*) [∀ i, Fintype (X i)] {A : ℕ} (hA : I.card + d ≤ A)
    {P V W : ℝ} (hP : 0 ≤ P) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hX : ∀ i, (Fintype.card (X i) : ℝ) ≤ Real.exp V)
    (hY : ∀ i, (Fintype.card (Y i) : ℝ) ≤ Real.exp W) :
    ((leafSourceAssignments X tree I base).card : ℝ) ≤
      Real.exp ((A : ℝ) * (P + V + W + 1)) := by
  have hleaves := h.leafCylinders_card_le_exp hA hP hW hcount hY
  have hcard : ((leafSourceAssignments X tree I base).card : ℝ) =
      ∑ c ∈ leafCylinders tree I base, (Fintype.card (∀ i : c.1, X i.val) : ℝ) := by
    simp only [leafSourceAssignments, Finset.card_sigma, Finset.card_univ, Nat.cast_sum]
  rw [hcard]
  calc
    _ ≤ ∑ _c ∈ leafCylinders tree I base, Real.exp ((A : ℝ) * V) := by
      apply Finset.sum_le_sum
      intro c hc
      exact partial_assignment_card_le_exp hV hX c.1 ((h.leaf_card_le c hc).trans hA)
    _ = ((leafCylinders tree I base).card : ℝ) * Real.exp ((A : ℝ) * V) := by simp
    _ ≤ Real.exp ((A : ℝ) * (P + W + 1)) * Real.exp ((A : ℝ) * V) :=
      mul_le_mul_of_nonneg_right hleaves (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3.CoordinateDecisionTree

end

end OAI
