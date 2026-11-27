import GRHArticle.ProgressionFree.Rankin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.NormNum
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite prefix certificates for integer geometric progressions

An admissible prefix is equivalent to a vertex cover of the forbidden triples
by its excluded elements. The cover search checks integer-weight bounds.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped BigOperators

/-- The positive integers up to and including the cutoff. -/
def integerPrefix (N : ℕ) : Finset ℕ := Icc 1 N

/-- The progression convention uses integral ratios if `integral` is true,
and rational ratios otherwise. -/
def IntegerPrefixAdmissible (integral : Bool) (A : Set ℕ) : Prop :=
  ∀ ⦃a b c⦄, a ∈ A → b ∈ A → c ∈ A → a < b → b < c →
    a * c = b * b → (integral = true → a ∣ b) → False

theorem integerPrefixAdmissible_rational_iff {A : Set ℕ}
    (hpos : ∀ a ∈ A, 0 < a) :
    IntegerPrefixAdmissible false A ↔ ThreeGPFree A := by
  constructor
  · intro h a ha b hb c hc he
    have ha₀ := hpos a ha
    have hc₀ := hpos c hc
    rcases lt_trichotomy a b with hab | hab | hab
    · have hbc : b < c := by
        by_contra! hcb
        have hlt := Nat.mul_lt_mul_of_pos_right hab hc₀
        exact (hlt.trans_le (Nat.mul_le_mul_left b hcb)).ne he
      exact (h ha hb hc hab hbc he (by simp)).elim
    · exact hab
    · have hcb : c < b := by
        by_contra! hbc
        have hlt := Nat.mul_lt_mul_of_pos_right hab hc₀
        have hle := Nat.mul_le_mul_left b hbc
        exact ((hlt.trans_le' hle).ne he.symm)
      exact (h hc hb ha hcb hab (by simpa only [mul_comm c a] using he) (by simp)).elim
  · intro h a b c ha hb hc hab _ he _
    exact hab.ne (h ha hb hc he)

theorem integerPrefixAdmissible_integral_iff {A : Set ℕ} (hpos : ∀ a ∈ A, 0 < a) :
    IntegerPrefixAdmissible true A ↔
      ∀ a r : ℕ, 1 < r → a ∈ A → a*r ∈ A → a*r*r ∉ A := by
  constructor
  · intro h a r hr ha hb hc
    have ha₀ := hpos a ha
    have has : 0 < a*r := Nat.mul_pos ha₀ (by omega)
    exact h ha hb hc
      (by simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left hr ha₀)
      (by simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left hr has)
      (by ring) (fun _ ↦ dvd_mul_right a r)
  · intro h a b c ha hb hc hab _ he hd
    obtain ⟨r, rfl⟩ := hd rfl
    have hcr : c = a*r*r := Nat.mul_left_cancel (hpos a ha) (by
      rw [he]
      ring)
    have hr : 1 < r := by
      by_contra! h
      exact hab.not_ge (by simpa only [mul_one] using Nat.mul_le_mul_left a h)
    exact h a r hr ha hb (hcr ▸ hc)

/-- A candidate progression in increasing order. -/
structure IntegerPrefixTriple where
  first : ℕ
  middle : ℕ
  last : ℕ
  deriving DecidableEq, Repr

/-- The vertices of the forbidden triple. -/
def IntegerPrefixTriple.vertices (e : IntegerPrefixTriple) : List ℕ :=
  [e.first, e.middle, e.last]

/-- Enumeration by the first two terms, with the third term obtained by
exact division. -/
def integerPrefixEdges (integral : Bool) (N : ℕ) : List IntegerPrefixTriple :=
  (List.range' 1 N).flatMap fun a ↦ (List.range' 1 N).filterMap fun b ↦
    let c := b*b/a
    if a < b ∧ b < c ∧ c ≤ N ∧ a*c = b*b ∧ (integral = true → a ∣ b) then
      some ⟨a, b, c⟩
    else none

private theorem mem_integerIntervalList {N a : ℕ} :
    a ∈ List.range' 1 N ↔ a ∈ integerPrefix N := by
  simp only [List.mem_range', one_mul, integerPrefix, mem_Icc]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · rintro ⟨ha, hN⟩
    exact ⟨a-1, by omega, by omega⟩

theorem mem_integerPrefixEdges {integral : Bool} {N : ℕ} {e : IntegerPrefixTriple} :
    e ∈ integerPrefixEdges integral N ↔
      1 ≤ e.first ∧ e.first < e.middle ∧ e.middle < e.last ∧ e.last ≤ N ∧
        e.first * e.last = e.middle * e.middle ∧ (integral = true → e.first ∣ e.middle) := by
  constructor
  · intro he
    obtain ⟨a, ha, hb⟩ := List.mem_flatMap.mp he
    obtain ⟨b, _, hb⟩ := List.mem_filterMap.mp hb
    dsimp only at hb
    split at hb
    · next h =>
      cases Option.some.inj hb
      exact ⟨(mem_Icc.mp (mem_integerIntervalList.mp ha)).1, h⟩
    · simp at hb
  · intro he
    have ha : e.first ∈ integerPrefix N := mem_Icc.mpr ⟨he.1, by omega⟩
    have hb : e.middle ∈ integerPrefix N := mem_Icc.mpr ⟨by omega, by omega⟩
    apply List.mem_flatMap.mpr
    refine ⟨e.first, mem_integerIntervalList.mpr ha, List.mem_filterMap.mpr
      ⟨e.middle, mem_integerIntervalList.mpr hb, ?_⟩⟩
    have hc : e.middle*e.middle/e.first = e.last := by
      rw [← he.2.2.2.2.1, Nat.mul_div_cancel_left _ (by omega)]
    rw [hc, if_pos he.2]

/-- Every forbidden triple has a vertex in the cover. -/
def integerPrefixCovers (C : Finset ℕ) (es : List IntegerPrefixTriple) : Prop :=
  ∀ e ∈ es, ∃ x ∈ e.vertices, x ∈ C

private theorem integerPrefixCovers_complement_iff {integral : Bool} {N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ integerPrefix N) :
    integerPrefixCovers (integerPrefix N \ A) (integerPrefixEdges integral N) ↔
      IntegerPrefixAdmissible integral (A : Set ℕ) := by
  constructor
  · intro h a b c ha hb hc hab hbc he hd
    have hmem : (⟨a,b,c⟩ : IntegerPrefixTriple) ∈ integerPrefixEdges integral N :=
      mem_integerPrefixEdges.mpr ⟨(mem_Icc.mp (hA ha)).1, hab, hbc, (mem_Icc.mp (hA hc)).2, he, hd⟩
    obtain ⟨x, hx, hx'⟩ := h _ hmem
    simp only [IntegerPrefixTriple.vertices, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact (mem_sdiff.mp hx').2 (by assumption)
  · intro h e he
    have hes := mem_integerPrefixEdges.mp he
    by_contra! hno
    have hm (x : ℕ) (hx : x ∈ e.vertices) (hb : x ∈ integerPrefix N) : x ∈ A := by
      by_contra hx'
      exact hno x hx (mem_sdiff.mpr ⟨hb, hx'⟩)
    have ha := hm e.first (by simp [IntegerPrefixTriple.vertices])
      (mem_Icc.mpr ⟨hes.1, by omega⟩)
    have hb := hm e.middle (by simp [IntegerPrefixTriple.vertices])
      (mem_Icc.mpr ⟨by omega, by omega⟩)
    have hc := hm e.last (by simp [IntegerPrefixTriple.vertices])
      (mem_Icc.mpr ⟨by omega, hes.2.2.2.1⟩)
    exact h ha hb hc hes.2.1 hes.2.2.1 hes.2.2.2.2.1 hes.2.2.2.2.2

private def removeIncident (x : ℕ) (es : List IntegerPrefixTriple) :
    List IntegerPrefixTriple :=
  es.filter fun e ↦ !e.vertices.contains x

private def feasibleCover (w : ℕ → ℕ) : ℕ → ℕ → List IntegerPrefixTriple → Bool
  | 0, _, es => es.isEmpty
  | _+1, _, [] => true
  | f+1, b, e::es => e.vertices.any fun x ↦
      decide (w x ≤ b) && feasibleCover w f (b-w x) (removeIncident x es)

private theorem feasibleCover_of_covers {w : ℕ → ℕ} {C : Finset ℕ} {b f : ℕ}
    {es : List IntegerPrefixTriple} (hf : es.length ≤ f) (hc : integerPrefixCovers C es)
    (hb : ∑ x ∈ C, w x ≤ b) : feasibleCover w f b es = true := by
  induction f generalizing b C es with
  | zero =>
    cases es with
    | nil => rfl
    | cons e es => simp at hf
  | succ f ih =>
    cases es with
    | nil => rfl
    | cons e es =>
      obtain ⟨x, hxe, hxC⟩ := hc e (by simp)
      have hsum := sum_erase_add C w hxC
      simp only [feasibleCover, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨x, hxe, by omega, ih (C := C.erase x) ?_ ?_ (by omega)⟩
      · have hlen := List.length_filter_le (fun e : IntegerPrefixTriple ↦ !e.vertices.contains x) es
        change es.length + 1 ≤ f + 1 at hf
        exact hlen.trans (Nat.le_of_succ_le_succ hf)
      · intro t ht
        rw [removeIncident, List.mem_filter] at ht
        obtain ⟨y, hyt, hyC⟩ := hc t (List.mem_cons_of_mem _ ht.1)
        refine ⟨y, hyt, mem_erase.mpr ⟨?_, hyC⟩⟩
        have hxnot : x ∉ t.vertices := by simpa using ht.2
        exact fun hyx ↦ hxnot (hyx ▸ hyt)

private theorem covers_of_feasibleCover {w : ℕ → ℕ} {V : Finset ℕ} {b f : ℕ}
    {es : List IntegerPrefixTriple} (hV : ∀ e ∈ es, ∀ x ∈ e.vertices, x ∈ V)
    (hb : feasibleCover w f b es = true) :
    ∃ C ⊆ V, integerPrefixCovers C es ∧ ∑ x ∈ C, w x ≤ b := by
  induction f generalizing b es with
  | zero =>
    cases es with
    | nil => exact ⟨∅, empty_subset _, by simp [integerPrefixCovers], by simp⟩
    | cons => simp [feasibleCover] at hb
  | succ f ih =>
    cases es with
    | nil => exact ⟨∅, empty_subset _, by simp [integerPrefixCovers], by simp⟩
    | cons e es =>
      simp only [feasibleCover, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hb
      obtain ⟨x, hxe, hxb, hb⟩ := hb
      have hxf : ∀ t ∈ removeIncident x es, ∀ y ∈ t.vertices, y ∈ V := by
        intro t ht
        rw [removeIncident, List.mem_filter] at ht
        exact hV t (by simp [ht.1])
      obtain ⟨C, hCV, hc, hcw⟩ := ih hxf hb
      refine ⟨insert x C, insert_subset (hV e (by simp) x hxe) hCV, ?_, ?_⟩
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact ⟨x, hxe, mem_insert_self _ _⟩
        · by_cases hxt : x ∈ t.vertices
          · exact ⟨x, hxt, mem_insert_self _ _⟩
          · obtain ⟨y, hyt, hyC⟩ := hc t (by simp [removeIncident, ht, hxt])
            exact ⟨y, hyt, mem_insert_of_mem hyC⟩
      · by_cases hx : x ∈ C
        · rw [insert_eq_of_mem hx]
          omega
        · rw [sum_insert hx]
          omega

theorem integerPrefixEdge_vertices_mem {integral : Bool} {N : ℕ}
    {e : IntegerPrefixTriple} (he : e ∈ integerPrefixEdges integral N) :
    ∀ x ∈ e.vertices, x ∈ integerPrefix N := by
  have h := mem_integerPrefixEdges.mp he
  intro x hx
  simp only [IntegerPrefixTriple.vertices, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> exact mem_Icc.mpr ⟨by omega, by omega⟩

/-- Check whether a cover of the forbidden triples has total cost at most
the supplied budget. -/
def integerPrefixCoverFeasible (integral : Bool) (N : ℕ) (w : ℕ → ℕ) (budget : ℕ) : Bool :=
  let es := integerPrefixEdges integral N
  feasibleCover w es.length budget es

theorem integerPrefixCoverFeasible_iff {integral : Bool} {N : ℕ} {w : ℕ → ℕ}
    {budget : ℕ} :
    integerPrefixCoverFeasible integral N w budget = true ↔
      ∃ C ⊆ integerPrefix N, integerPrefixCovers C (integerPrefixEdges integral N) ∧
        ∑ x ∈ C, w x ≤ budget := by
  constructor
  · exact covers_of_feasibleCover (fun _ he ↦ integerPrefixEdge_vertices_mem he)
  · rintro ⟨C, _, hC, hcost⟩
    exact feasibleCover_of_covers le_rfl hC hcost

/-- The greatest retained weight among the admissible subsets of the prefix,
for any natural-valued vertex weights. -/
noncomputable def integerPrefixWeightMax (integral : Bool) (N : ℕ) (w : ℕ → ℕ) : ℕ := by
  classical
  exact ((integerPrefix N).powerset.filter fun A : Finset ℕ ↦ IntegerPrefixAdmissible integral (A : Set ℕ)).sup
    fun A ↦ ∑ x ∈ A, w x

theorem integerPrefixWeight_le_max {integral : Bool} {N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ integerPrefix N) (ha : IntegerPrefixAdmissible integral (A : Set ℕ))
    (w : ℕ → ℕ) :
    ∑ x ∈ A, w x ≤ integerPrefixWeightMax integral N w := by
  classical
  unfold integerPrefixWeightMax
  exact Finset.le_sup (f := fun A : Finset ℕ ↦ ∑ x ∈ A, w x) (b := A)
    (mem_filter.mpr ⟨mem_powerset.mpr hA, ha⟩)

theorem integerPrefixWeightMax_of_budget {integral : Bool} {N : ℕ} {w : ℕ → ℕ}
    {budget : ℕ}
    (hyes : integerPrefixCoverFeasible integral N w budget = true)
    (hno : budget = 0 ∨ integerPrefixCoverFeasible integral N w (budget-1) = false) :
    integerPrefixWeightMax integral N w = (∑ x ∈ integerPrefix N, w x) - budget := by
  classical
  apply le_antisymm
  · unfold integerPrefixWeightMax
    apply Finset.sup_le
    intro A hA
    obtain ⟨hsub, hadm⟩ := mem_filter.mp hA
    have hsub := mem_powerset.mp hsub
    have hC := (integerPrefixCovers_complement_iff hsub).mpr hadm
    have hcover : budget ≤ ∑ x ∈ integerPrefix N \ A, w x := by
      rcases hno with rfl | hno
      · exact Nat.zero_le _
      · by_contra! hbad
        have htrue := (integerPrefixCoverFeasible_iff (w := w) (budget := budget-1)).mpr
          ⟨integerPrefix N \ A, sdiff_subset, hC, by omega⟩
        rw [hno] at htrue
        contradiction
    have hs := sum_sdiff (f := w) hsub
    omega
  · obtain ⟨C, hsub, hc, hw⟩ := integerPrefixCoverFeasible_iff.mp hyes
    have hadm := (integerPrefixCovers_complement_iff (integral := integral) (A := integerPrefix N \ C) sdiff_subset).mp
      (by rwa [Finset.sdiff_sdiff_eq_self hsub])
    have hb := integerPrefixWeight_le_max sdiff_subset hadm w
    have hs := sum_sdiff (f := w) hsub
    omega

/-- The cardinality optimum at the given prefix cutoff. -/
noncomputable def integerPrefixCardMax (integral : Bool) (N : ℕ) : ℕ :=
  integerPrefixWeightMax integral N (fun _ ↦ 1)

/-- A common integer denominator for all reciprocal prefix weights. -/
def integerPrefixWeightScale (N : ℕ) : ℕ := (N+1).factorial

/-- The article's reciprocal weight multiplied by a common positive
denominator. -/
def integerPrefixScaledWeight (N a : ℕ) : ℕ :=
  integerPrefixWeightScale N / a - integerPrefixWeightScale N / (N+1)

private theorem integerPrefixScaledWeight_eq {N a : ℕ} (ha : a ∈ integerPrefix N) :
    (integerPrefixScaledWeight N a : ℚ) / (integerPrefixWeightScale N : ℚ) =
      (1:ℚ)/a - 1/(N+1) := by
  obtain ⟨ha₁, haN⟩ := mem_Icc.mp ha
  have hscale : (integerPrefixWeightScale N : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos (N+1)).ne'
  have ha₀ : (a : ℚ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  have hN₀ : (N : ℚ) + 1 ≠ 0 := by positivity
  have he {k : ℕ} (hk : 0 < k) (hkN : k ≤ N+1) :
      ((integerPrefixWeightScale N / k : ℕ) : ℚ) =
        (integerPrefixWeightScale N : ℚ) / k := by
    have hk₀ : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
    apply (eq_div_iff hk₀).mpr
    exact_mod_cast Nat.div_mul_cancel (Nat.dvd_factorial hk hkN)
  unfold integerPrefixScaledWeight
  rw [Nat.cast_sub (Nat.div_le_div_left (by omega) (by omega)), he (by omega) (by omega),
    he (Nat.succ_pos N) le_rfl, Nat.cast_succ]
  field_simp

/-- The maximum of the unscaled truncated reciprocal weights. -/
noncomputable def integerPrefixReciprocalMax (integral : Bool) (N : ℕ) : ℚ :=
  (integerPrefixWeightMax integral N (integerPrefixScaledWeight N) : ℚ) /
    (integerPrefixWeightScale N : ℚ)

/-- The difference between the sum of the separately optimized prefix
counts and the weight achievable by one admissible set. -/
noncomputable def integerPrefixLoss (integral : Bool) (N : ℕ) : ℚ :=
  (∑ k ∈ integerPrefix N, (integerPrefixCardMax integral k : ℚ) / (k*(k+1))) -
    integerPrefixReciprocalMax integral N

theorem integerPrefixCount_le_max {integral : Bool} {N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ integerPrefix N) (ha : IntegerPrefixAdmissible integral (A : Set ℕ)) :
    A.card ≤ integerPrefixCardMax integral N := by
  simpa [integerPrefixCardMax] using integerPrefixWeight_le_max hA ha (fun _ ↦ 1)

theorem integerPrefixReciprocal_le_max {integral : Bool} {N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ integerPrefix N) (ha : IntegerPrefixAdmissible integral (A : Set ℕ)) :
    ∑ a ∈ A, ((1:ℚ)/a - 1/(N+1)) ≤ integerPrefixReciprocalMax integral N := by
  have hs : (0:ℚ) < integerPrefixWeightScale N := by
    exact_mod_cast Nat.factorial_pos (N+1)
  have hm : ((∑ a ∈ A, integerPrefixScaledWeight N a : ℕ) : ℚ) ≤
      integerPrefixWeightMax integral N (integerPrefixScaledWeight N) := by
    exact_mod_cast integerPrefixWeight_le_max hA ha (integerPrefixScaledWeight N)
  have he := div_le_div_of_nonneg_right hm hs.le
  rw [Nat.cast_sum, Finset.sum_div] at he
  unfold integerPrefixReciprocalMax
  calc
    _ = ∑ a ∈ A, (integerPrefixScaledWeight N a : ℚ) / (integerPrefixWeightScale N : ℚ) :=
      sum_congr rfl fun _ ha ↦ (integerPrefixScaledWeight_eq (hA ha)).symm
    _ ≤ _ := he

private theorem sum_prefix_telescopes {N : ℕ} {A : Finset ℕ} (hA : A ⊆ integerPrefix N) :
    ∑ k ∈ integerPrefix N, ((A.filter (· ≤ k)).card : ℚ) / (k*(k+1)) =
      ∑ a ∈ A, ((1:ℚ)/a - 1/(N+1)) := by
  calc
    _ = ∑ k ∈ integerPrefix N, ∑ a ∈ A,
        (if a ≤ k then (1:ℚ)/k - 1/(k+1) else 0) := by
      apply sum_congr rfl
      intro k hk
      have hk₀ : (k : ℚ) ≠ 0 := by
        exact_mod_cast (show k ≠ 0 from Nat.ne_of_gt (mem_Icc.mp hk).1)
      have hk₁ : (k : ℚ)+1 ≠ 0 := by positivity
      rw [← sum_filter]
      have hconst : (1:ℚ)/k - 1/(k+1) = 1/(k*(k+1)) := by
        field_simp
        ring
      rw [hconst, sum_const, nsmul_eq_mul, div_eq_mul_inv]
      simp only [one_div]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro a ha
      have h := mem_Icc.mp (hA ha)
      have hf : (integerPrefix N).filter (a ≤ ·) = Ico a (N+1) := by
        ext k
        simp only [integerPrefix, mem_filter, mem_Icc, mem_Ico]
        omega
      rw [← sum_filter, hf]
      simpa only [neg_sub_neg, Nat.cast_add, Nat.cast_one] using
        (sum_Ico_sub (fun k : ℕ ↦ -((1:ℚ)/k)) (show a ≤ N+1 by omega))

/-- Any admissible set loses at least the finite prefix loss against the
separate cardinality optima, with weights (1/(k(k+1))). -/
theorem integerPrefixLoss_le_deficit {integral : Bool} {N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ integerPrefix N) (ha : IntegerPrefixAdmissible integral (A : Set ℕ)) :
    integerPrefixLoss integral N ≤
      ∑ k ∈ integerPrefix N,
        ((integerPrefixCardMax integral k : ℚ) - ((A.filter (· ≤ k)).card : ℚ)) /
          (k*(k+1)) := by
  simp only [sub_div, sum_sub_distrib, integerPrefixLoss]
  rw [sum_prefix_telescopes hA]
  exact sub_le_sub_left (integerPrefixReciprocal_le_max hA ha) _

theorem sum_integerPrefix {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ k ∈ integerPrefix N, f k = ∑ k ∈ range N, f (1+k) := by
  have h : integerPrefix N = Ico 1 (N+1) := by
    ext k
    simp only [integerPrefix, mem_Icc, mem_Ico]
    omega
  rw [h, sum_Ico_eq_sum_range, Nat.add_sub_cancel]

private def countsTwelve (k : ℕ) : ℕ :=
  ([0,1,2,3,3,4,5,6,7,7,8,9,10] : List ℕ)[k]?.getD 0

set_option maxRecDepth 20000 in
private theorem prefixTwelve_card_budgets (integral : Bool) :
    ∀ k : Fin 13,
      integerPrefixCoverFeasible integral k (fun _ ↦ 1) (k-countsTwelve k) = true ∧
        (k-countsTwelve k = 0 ∨
          integerPrefixCoverFeasible integral k (fun _ ↦ 1) (k-countsTwelve k-1) = false) := by
  cases integral <;> decide

private theorem integerPrefixCardMax_twelve (integral : Bool) {k : ℕ} (hk : k ≤ 12) :
    integerPrefixCardMax integral k = countsTwelve k := by
  obtain ⟨hy, hn⟩ := prefixTwelve_card_budgets integral ⟨k, by omega⟩
  have hk' : ∀ k : Fin 13, countsTwelve k ≤ k := by decide
  have htab : countsTwelve k ≤ k := hk' ⟨k, by omega⟩
  change integerPrefixCoverFeasible integral k (fun _ ↦ 1) (k-countsTwelve k) = true at hy
  change k-countsTwelve k = 0 ∨
    integerPrefixCoverFeasible integral k (fun _ ↦ 1) (k-countsTwelve k-1) = false at hn
  unfold integerPrefixCardMax
  rw [integerPrefixWeightMax_of_budget hy hn, sum_const, smul_eq_mul, mul_one,
    integerPrefix, Nat.card_Icc]
  omega

set_option maxRecDepth 20000 in
private theorem prefixTwelve_reciprocal_budgets (integral : Bool) :
    integerPrefixCoverFeasible integral 12 (integerPrefixScaledWeight 12) 1330560000 = true ∧
    integerPrefixCoverFeasible integral 12 (integerPrefixScaledWeight 12) 1330559999 = false := by
  cases integral <;> decide

theorem integerPrefixReciprocalMax_twelve (integral : Bool) :
    integerPrefixReciprocalMax integral 12 = (78737:ℚ)/40040 := by
  obtain ⟨hy, hn⟩ := prefixTwelve_reciprocal_budgets integral
  rw [integerPrefixReciprocalMax,
    integerPrefixWeightMax_of_budget hy (Or.inr hn), sum_integerPrefix]
  norm_num [Finset.sum_range_succ, integerPrefixScaledWeight, integerPrefixWeightScale, Nat.factorial]

/-- The exact prefix obstruction at 12 holds for both conventions. -/
theorem integerPrefixLoss_twelve (integral : Bool) :
    integerPrefixLoss integral 12 = (1:ℚ)/156 := by
  unfold integerPrefixLoss
  have hs :
      (∑ k ∈ integerPrefix 12, (integerPrefixCardMax integral k : ℚ) / (k*(k+1))) =
        ∑ k ∈ integerPrefix 12, (countsTwelve k : ℚ) / (k*(k+1)) := by
    apply sum_congr rfl
    intro k hk
    rw [integerPrefixCardMax_twelve integral (mem_Icc.mp hk).2]
  rw [hs, integerPrefixReciprocalMax_twelve, sum_integerPrefix]
  norm_num [Finset.sum_range_succ, countsTwelve]

end GRHArticle.ProgressionFree
