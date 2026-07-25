import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Linarith

/-!
# Interval partitions of a segment

The 1-D workhorse for the small-order impossibility results: if finitely many
closed intervals `[x, x + s]` with positive lengths, pairwise disjoint
interiors and endpoints inside `[lo, hi]` cover every point of `(lo, hi]`,
then their lengths sum to `hi - lo`.

Intervals are recorded as pairs `(x, s)` of position and length.  Interior
disjointness is used through the separation predicate `sep1`: one interval
ends before the other begins.
-/

namespace LeanProofs

namespace SquaredSquare

/-- Two 1-D intervals `(x, s)` are separated: one ends before the other
begins. -/
def sep1 (p q : ℝ × ℝ) : Prop :=
  p.1 + p.2 ≤ q.1 ∨ q.1 + q.2 ≤ p.1

theorem sep1_symm {p q : ℝ × ℝ} (h : sep1 p q) : sep1 q p :=
  h.symm

/-- Lower bound for `foldr min`. -/
theorem lt_foldr_min {c : ℝ} (L : List ℝ) (a : ℝ) (ha : c < a)
    (h : ∀ x ∈ L, c < x) : c < L.foldr min a := by
  induction L with
  | nil => exact ha
  | cons x t ih =>
    have hx := h x (List.mem_cons_self ..)
    have ht := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    exact lt_min hx ht

/-- `foldr min` is at most each list element. -/
theorem foldr_min_le_mem {x : ℝ} (L : List ℝ) (a : ℝ) (hx : x ∈ L) :
    L.foldr min a ≤ x := by
  induction L with
  | nil => cases hx
  | cons y t ih =>
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact min_le_left _ _
    · exact le_trans (min_le_right _ _) (ih hx')

/-- `foldr min` is at most the initial value. -/
theorem foldr_min_le_init (L : List ℝ) (a : ℝ) : L.foldr min a ≤ a := by
  induction L with
  | nil => exact le_rfl
  | cons y t ih => exact le_trans (min_le_right _ _) ih

/-- **Interval partition sum.**  If the intervals of `B` have positive
lengths, live inside `[lo, hi]`, are pairwise separated, and cover every
point of `(lo, hi]`, then their lengths sum to `hi - lo`. -/
theorem interval_cover_sum :
    ∀ (n : ℕ) (B : List (ℝ × ℝ)) (lo hi : ℝ), B.length = n → lo ≤ hi →
      (∀ p ∈ B, 0 < p.2) →
      (∀ p ∈ B, lo ≤ p.1 ∧ p.1 + p.2 ≤ hi) →
      B.Pairwise sep1 →
      (∀ x, lo < x → x ≤ hi → ∃ p ∈ B, p.1 ≤ x ∧ x ≤ p.1 + p.2) →
      (B.map Prod.snd).sum = hi - lo := by
  intro n
  induction n with
  | zero =>
    intro B lo hi hlen hle hpos hbnd hsep hcov
    have hB : B = [] := List.length_eq_zero_iff.mp hlen
    subst hB
    rcases eq_or_lt_of_le hle with rfl | hlt
    · simp
    · obtain ⟨p, hp, -⟩ := hcov hi hlt le_rfl
      exact absurd hp (List.not_mem_nil)
  | succ n ih =>
    intro B lo hi hlen hle hpos hbnd hsep hcov
    classical
    -- B is nonempty, so lo < hi
    obtain ⟨p₀, hp₀⟩ : ∃ p, p ∈ B := by
      cases B with
      | nil => simp at hlen
      | cons a t => exact ⟨a, List.mem_cons_self ..⟩
    have hlolt : lo < hi := by
      have h1 := hpos p₀ hp₀
      have h2 := hbnd p₀ hp₀
      linarith [h2.1, h2.2]
    -- the smallest left endpoint strictly beyond lo (or hi if none)
    set μ : ℝ :=
      ((B.filter (fun r => decide (lo < r.1))).map Prod.fst).foldr min hi
      with hμdef
    have hμlo : lo < μ := by
      refine lt_foldr_min _ _ hlolt ?_
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨r, hr, rfl⟩ := hx
      rw [List.mem_filter] at hr
      exact of_decide_eq_true hr.2
    have hμle : ∀ r ∈ B, lo < r.1 → μ ≤ r.1 := by
      intro r hr hlt
      refine foldr_min_le_mem _ _ ?_
      rw [List.mem_map]
      exact ⟨r, List.mem_filter.mpr ⟨hr, decide_eq_true hlt⟩, rfl⟩
    have hμhi : μ ≤ hi := foldr_min_le_init _ _
    -- the interval covering the point (lo + μ)/2 starts exactly at lo
    obtain ⟨q, hq, hq1, hq2⟩ :=
      hcov ((lo + μ) / 2) (by linarith) (by linarith)
    have hqlo : q.1 = lo := by
      rcases lt_or_ge lo q.1 with h | h
      · have := hμle q hq h
        linarith
      · exact le_antisymm h (hbnd q hq).1
    -- split B at q
    obtain ⟨B₁, B₂, rfl⟩ := List.append_of_mem hq
    have hqmem : q ∈ B₁ ++ q :: B₂ := hq
    -- unpack pairwise separation
    rw [List.pairwise_append] at hsep
    obtain ⟨hsep₁, hsep₂', hcross⟩ := hsep
    rw [List.pairwise_cons] at hsep₂'
    obtain ⟨hqsep, hsep₂⟩ := hsep₂'
    -- every other interval starts at or after lo + q.2
    have hafter : ∀ r ∈ B₁ ++ B₂, lo + q.2 ≤ r.1 := by
      intro r hr
      have hrB : r ∈ B₁ ++ q :: B₂ := by
        rcases List.mem_append.mp hr with h | h
        · exact List.mem_append.mpr (Or.inl h)
        · exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ h))
      have hrpos := hpos r hrB
      have hrbnd := hbnd r hrB
      rcases List.mem_append.mp hr with h | h
      · rcases hcross r h q (List.mem_cons_self ..) with hs | hs
        · exfalso
          rw [hqlo] at hs
          linarith [hrbnd.1]
        · rw [hqlo] at hs
          linarith
      · rcases hqsep r h with hs | hs
        · rw [hqlo] at hs
          linarith
        · exfalso
          rw [hqlo] at hs
          linarith [hrbnd.1]
    -- the remaining intervals satisfy the hypotheses on [lo + q.2, hi]
    have hqbnd := hbnd q hqmem
    have hqpos := hpos q hqmem
    have hlen' : (B₁ ++ B₂).length = n := by
      simp only [List.length_append, List.length_cons] at hlen ⊢
      omega
    have hmem' : ∀ r ∈ B₁ ++ B₂, r ∈ B₁ ++ q :: B₂ := by
      intro r hr
      rcases List.mem_append.mp hr with h | h
      · exact List.mem_append.mpr (Or.inl h)
      · exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ h))
    have hsum' : ((B₁ ++ B₂).map Prod.snd).sum = hi - (lo + q.2) := by
      refine ih (B₁ ++ B₂) (lo + q.2) hi hlen' (by linarith [hqbnd.2, hqlo]) ?_ ?_ ?_ ?_
      · exact fun r hr => hpos r (hmem' r hr)
      · exact fun r hr => ⟨hafter r hr, (hbnd r (hmem' r hr)).2⟩
      · refine List.pairwise_append.mpr ⟨hsep₁, hsep₂, ?_⟩
        exact fun a ha b hb => hcross a ha b (List.mem_cons_of_mem _ hb)
      · intro x hx1 hx2
        obtain ⟨r, hr, hr1, hr2⟩ := hcov x (by linarith) hx2
        rcases List.mem_append.mp hr with h | h
        · exact ⟨r, List.mem_append.mpr (Or.inl h), hr1, hr2⟩
        · rcases List.mem_cons.mp h with rfl | h'
          · exfalso
            rw [hqlo] at hr2
            linarith
          · exact ⟨r, List.mem_append.mpr (Or.inr h'), hr1, hr2⟩
    -- reassemble the sum
    have : ((B₁ ++ q :: B₂).map Prod.snd).sum
        = (B₁.map Prod.snd).sum + (q.2 + (B₂.map Prod.snd).sum) := by
      simp [List.sum_append]
    rw [this]
    have : ((B₁ ++ B₂).map Prod.snd).sum
        = (B₁.map Prod.snd).sum + (B₂.map Prod.snd).sum := by
      simp [List.sum_append]
    rw [this] at hsum'
    linarith

/-- Convenience wrapper: no explicit length parameter. -/
theorem interval_cover_sum' (B : List (ℝ × ℝ)) (lo hi : ℝ) (hle : lo ≤ hi)
    (hpos : ∀ p ∈ B, 0 < p.2)
    (hbnd : ∀ p ∈ B, lo ≤ p.1 ∧ p.1 + p.2 ≤ hi)
    (hsep : B.Pairwise sep1)
    (hcov : ∀ x, lo < x → x ≤ hi → ∃ p ∈ B, p.1 ≤ x ∧ x ≤ p.1 + p.2) :
    (B.map Prod.snd).sum = hi - lo :=
  interval_cover_sum B.length B lo hi rfl hle hpos hbnd hsep hcov

end SquaredSquare

end LeanProofs
