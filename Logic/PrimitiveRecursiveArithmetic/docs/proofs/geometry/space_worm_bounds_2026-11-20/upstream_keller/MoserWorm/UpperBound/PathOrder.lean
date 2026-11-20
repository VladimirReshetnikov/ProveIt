import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Tactic.SplitIfs
import MoserWorm.UpperBound.FiniteWitness
import MoserWorm.Common.Area

/-!
# Finite Hamiltonian paths and completed contact prefixes

The block reversal and 2-opt calculation are adapted from
`MoserUB/Reduction/Path.lean`. They are proved here over the common complex
plane, with no dependency on the old polygonal-arc or crosscut development.
-/

open Set Metric

noncomputable section

namespace MoserWorm.UpperBound

/-- No three distinct indices are collinear. Extreme vertex families will
satisfy this without perturbation. -/
def InGenPos {ι : Type*} (v : ι → Plane) : Prop :=
  ∀ a b c, a ≠ b → a ≠ c → b ≠ c →
    ¬ Collinear ℝ ({v a, v b, v c} : Set Plane)

/-- The index reversal of the block `[j+1, j']`. -/
def blockRev (j j' : ℕ) : ℕ → ℕ := fun i =>
  if j + 1 ≤ i ∧ i ≤ j' then j + 1 + j' - i else i

lemma blockRev_of_mem {j j' i : ℕ} (h : j + 1 ≤ i ∧ i ≤ j') :
    blockRev j j' i = j + 1 + j' - i := if_pos h

lemma blockRev_of_not_mem {j j' i : ℕ} (h : ¬(j + 1 ≤ i ∧ i ≤ j')) :
    blockRev j j' i = i := if_neg h

lemma blockRev_le {j j' k : ℕ} (h : j' ≤ k) (i : ℕ) (hi : i ≤ k) :
    blockRev j j' i ≤ k := by
  unfold blockRev
  split <;> omega

/-- The 2-opt exchange identity (additive form). -/
lemma exchange_sum (u : ℕ → Plane) {j j' k : ℕ} (h1 : j + 1 ≤ j') (h2 : j' + 1 ≤ k) :
    pathLen (fun i => u (blockRev j j' i)) k
      + dist (u j) (u (j + 1)) + dist (u j') (u (j' + 1))
    = pathLen u k + dist (u j) (u j') + dist (u (j + 1)) (u (j' + 1)) := by
  have hsplit : ∀ w : ℕ → Plane, pathLen w k
      = (∑ i ∈ Finset.Ico 0 j, dist (w i) (w (i + 1)))
        + dist (w j) (w (j + 1))
        + (∑ i ∈ Finset.Ico (j + 1) j', dist (w i) (w (i + 1)))
        + dist (w j') (w (j' + 1))
        + (∑ i ∈ Finset.Ico (j' + 1) k, dist (w i) (w (i + 1))) := by
    intro w
    rw [pathLen, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (by omega : 0 ≤ j) (by omega : j ≤ k),
      ← Finset.sum_Ico_consecutive _ (by omega : j ≤ j' + 1) (by omega : j' + 1 ≤ k),
      ← Finset.sum_Ico_consecutive _ (by omega : j ≤ j + 1) (by omega : j + 1 ≤ j' + 1),
      ← Finset.sum_Ico_consecutive _ (by omega : j + 1 ≤ j') (by omega : j' ≤ j' + 1)]
    rw [Nat.Ico_succ_singleton, Nat.Ico_succ_singleton,
      Finset.sum_singleton, Finset.sum_singleton]
    ring
  set w' : ℕ → Plane := fun i => u (blockRev j j' i) with hw'
  rw [hsplit w', hsplit u]
  -- chunk 1: unchanged
  have c1 : (∑ i ∈ Finset.Ico 0 j, dist (w' i) (w' (i + 1)))
      = ∑ i ∈ Finset.Ico 0 j, dist (u i) (u (i + 1)) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_Ico] at hi
    rw [hw']
    simp only
    rw [blockRev_of_not_mem (by omega), blockRev_of_not_mem (by omega)]
  -- chunk 5: unchanged
  have c5 : (∑ i ∈ Finset.Ico (j' + 1) k, dist (w' i) (w' (i + 1)))
      = ∑ i ∈ Finset.Ico (j' + 1) k, dist (u i) (u (i + 1)) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_Ico] at hi
    rw [hw']
    simp only
    rw [blockRev_of_not_mem (by omega), blockRev_of_not_mem (by omega)]
  -- singletons
  have c2a : w' j = u j := by
    rw [hw']
    simp only
    rw [blockRev_of_not_mem (by omega)]
  have c2b : w' (j + 1) = u j' := by
    rw [hw']
    simp only
    rw [blockRev_of_mem (by omega)]
    congr 1
    omega
  have c4a : w' j' = u (j + 1) := by
    rw [hw']
    simp only
    rw [blockRev_of_mem (by omega)]
    congr 1
    omega
  have c4b : w' (j' + 1) = u (j' + 1) := by
    rw [hw']
    simp only
    rw [blockRev_of_not_mem (by omega)]
  -- chunk 3: the reversed middle block
  have c3 : (∑ i ∈ Finset.Ico (j + 1) j', dist (w' i) (w' (i + 1)))
      = ∑ i ∈ Finset.Ico (j + 1) j', dist (u i) (u (i + 1)) := by
    set n : ℕ := j' - (j + 1) with hn
    rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
    have hL : ∀ m < j' - (j + 1),
        dist (w' (j + 1 + m)) (w' (j + 1 + m + 1))
        = dist (u (j' - 1 - m)) (u (j' - m)) := by
      intro m hm
      rw [hw']
      simp only
      rw [blockRev_of_mem (by omega), blockRev_of_mem (by omega)]
      rw [show j + 1 + j' - (j + 1 + m) = j' - m by omega,
        show j + 1 + j' - (j + 1 + m + 1) = j' - 1 - m by omega]
      exact dist_comm _ _
    have hR : ∀ m < j' - (j + 1),
        dist (u (j + 1 + m)) (u (j + 1 + m + 1))
        = (fun m => dist (u (j + 1 + m)) (u (j + 2 + m))) m := by
      intro m _
      simp only
      rw [show j + 1 + m + 1 = j + 2 + m by omega]
    calc (∑ m ∈ Finset.range (j' - (j + 1)),
            dist (w' (j + 1 + m)) (w' (j + 1 + m + 1)))
        = ∑ m ∈ Finset.range (j' - (j + 1)),
            (fun m => dist (u (j + 1 + m)) (u (j + 2 + m))) (j' - (j+1) - 1 - m) := by
          refine Finset.sum_congr rfl (fun m hm => ?_)
          rw [Finset.mem_range] at hm
          rw [hL m hm]
          simp only
          rw [show j + 1 + (j' - (j+1) - 1 - m) = j' - 1 - m by omega,
            show j + 2 + (j' - (j+1) - 1 - m) = j' - m by omega]
      _ = ∑ m ∈ Finset.range (j' - (j + 1)),
            dist (u (j + 1 + m)) (u (j + 2 + m)) :=
          Finset.sum_range_reflect
            (fun m => dist (u (j + 1 + m)) (u (j + 2 + m))) (j' - (j + 1))
      _ = ∑ m ∈ Finset.range (j' - (j + 1)),
            dist (u (j + 1 + m)) (u (j + 1 + m + 1)) := by
          refine Finset.sum_congr rfl (fun m hm => ?_)
          rw [show j + 2 + m = j + 1 + m + 1 by omega]
  rw [c1, c2a, c2b, c3, c4a, c4b, c5]
  ring

/-- Collinearity merge: two collinear triples sharing the pair `{x, b}`,
`x ≠ b`, force the outer triple collinear. -/
lemma collinear_merge {a b c x : Plane} (hxb : x ≠ b)
    (h1 : Collinear ℝ ({a, x, b} : Set Plane))
    (h2 : Collinear ℝ ({c, x, b} : Set Plane)) :
    Collinear ℝ ({a, b, c} : Set Plane) := by
  have h3 : Collinear ℝ (insert c ({a, x, b} : Set Plane)) :=
    (h1.collinear_insert_iff_of_ne (p₁ := c) (p₂ := x) (p₃ := b)
      (by simp) (by simp) hxb).mpr h2
  refine h3.subset ?_
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
  tauto

section

variable {k : ℕ} (v : Fin (k + 1) → Plane)

theorem permChain_eq (σ : Equiv.Perm (Fin (k + 1))) {m : ℕ} (hm : m ≤ k) :
    permChain v σ m = v (σ ⟨m, by omega⟩) := by
  exact natExt_of_le (v ∘ σ) hm

lemma permChain_injOn (hinj : Function.Injective v) (σ : Equiv.Perm (Fin (k + 1)))
    {m m' : ℕ} (hm : m ≤ k) (hm' : m' ≤ k)
    (h : permChain v σ m = permChain v σ m') : m = m' := by
  rw [permChain_eq v σ hm, permChain_eq v σ hm'] at h
  have := σ.injective (hinj h)
  simpa [Fin.ext_iff] using this

lemma permChain_gen (hgen : InGenPos v) (σ : Equiv.Perm (Fin (k + 1))) {m m' m'' : ℕ}
    (hm : m ≤ k) (hm' : m' ≤ k) (hm'' : m'' ≤ k)
    (h1 : m ≠ m') (h2 : m ≠ m'') (h3 : m' ≠ m'') :
    ¬ Collinear ℝ ({permChain v σ m, permChain v σ m',
      permChain v σ m''} : Set Plane) := by
  rw [permChain_eq v σ hm, permChain_eq v σ hm', permChain_eq v σ hm'']
  refine hgen _ _ _ ?_ ?_ ?_ <;>
    (intro h; apply_fun σ.symm at h;
      simp only [Equiv.symm_apply_apply, Fin.mk.injEq] at h; omega)

/-- Step 1: consecutive edges of any chain in general position meet only in
the shared node. -/
lemma eq_shared_node_of_mem_consecutive_segments
    (hgen : InGenPos v) (σ : Equiv.Perm (Fin (k + 1))) {i : ℕ} (hik : i + 2 ≤ k) {x : Plane}
    (hx1 : x ∈ segment ℝ (permChain v σ i) (permChain v σ (i + 1)))
    (hx2 : x ∈ segment ℝ (permChain v σ (i + 1)) (permChain v σ (i + 2))) :
    x = permChain v σ (i + 1) := by
  by_contra hne
  set u := permChain v σ with hu
  have h1 : Collinear ℝ ({u i, x, u (i + 1)} : Set Plane) :=
    (mem_segment_iff_wbtw.mp hx1).collinear
  have h2 : Collinear ℝ ({u (i + 1), x, u (i + 2)} : Set Plane) :=
    (mem_segment_iff_wbtw.mp hx2).collinear
  have h2' : Collinear ℝ ({u (i + 2), x, u (i + 1)} : Set Plane) :=
    h2.subset (by intro y hy; simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff] at hy ⊢; tauto)
  have hcol : Collinear ℝ ({u i, u (i + 1), u (i + 2)} : Set Plane) :=
    collinear_merge hne h1 h2'
  exact permChain_gen v hgen σ (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) hcol

/-- The block-reversal permutation of `Fin (k+1)`. -/
def blockRevPerm (j j' : ℕ) (hj' : j' ≤ k) : Equiv.Perm (Fin (k + 1)) :=
  Function.Involutive.toPerm
    (fun i => ⟨blockRev j j' i.val, by
      have := i.isLt
      unfold blockRev
      split <;> omega⟩)
    (by
      intro i
      rw [Fin.ext_iff]
      change blockRev j j' (blockRev j j' i.val) = i.val
      unfold blockRev
      split_ifs <;> omega)

/-- Step 2: for a minimal permutation, non-adjacent edges are disjoint. -/
lemma min_edges_disjoint (hgen : InGenPos v) {σ : Equiv.Perm (Fin (k + 1))}
    (hmin : ∀ τ, pathLen (permChain v σ) k ≤ pathLen (permChain v τ) k)
    {j j' : ℕ} (hjj' : j + 2 ≤ j') (hj'k : j' + 1 ≤ k) {x : Plane}
    (hx1 : x ∈ segment ℝ (permChain v σ j) (permChain v σ (j + 1))) :
    x ∉ segment ℝ (permChain v σ j') (permChain v σ (j' + 1)) := by
  intro hx2
  set u := permChain v σ with hu
  -- x is none of the four nodes: a node on the other edge would give a
  -- collinear triple in general position
  have node_case : ∀ m a b : ℕ, m ≤ k → a ≤ k → b ≤ k → m ≠ a → m ≠ b → a ≠ b →
      x ∈ segment ℝ (u a) (u b) → x ≠ u m := by
    intro m a b hm ha hb hma hmb hab hseg hxm
    subst hxm
    exact permChain_gen v hgen σ ha hm hb hma.symm hab hmb
      (mem_segment_iff_wbtw.mp hseg).collinear
  have hxj : x ≠ u j := node_case j j' (j' + 1) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) hx2
  -- x interior to the j-edge — 2-opt exchange
  -- the exchanged chain agrees with u ∘ blockRev on [0, k]
  set ρ := blockRevPerm (k := k) j j' (by omega) with hρ
  have hagree : ∀ i ≤ k, permChain v (σ * ρ) i = u (blockRev j j' i) := by
    intro i hi
    have hbr : blockRev j j' i ≤ k := blockRev_le (by omega) i hi
    rw [permChain_eq v (σ * ρ) hi, hu, permChain_eq v σ hbr]
    change v (σ (ρ ⟨i, by omega⟩)) = v (σ ⟨blockRev j j' i, by omega⟩)
    congr 2
  have hexch := exchange_sum u (j := j) (j' := j') (by omega) hj'k
  have hτ := hmin (σ * ρ)
  have hcomp : pathLen (permChain v (σ * ρ)) k
      = pathLen (fun i => u (blockRev j j' i)) k :=
    pathLen_congr (fun i hi => hagree i hi)
  rw [hcomp] at hτ
  -- distances
  have d1 : dist (u j) x + dist x (u (j + 1)) = dist (u j) (u (j + 1)) :=
    dist_add_dist_of_mem_segment hx1
  have d2 : dist (u j') x + dist x (u (j' + 1)) = dist (u j') (u (j' + 1)) :=
    dist_add_dist_of_mem_segment hx2
  have tA : dist (u j) (u j') ≤ dist (u j) x + dist x (u j') := dist_triangle _ _ _
  have tB : dist (u (j + 1)) (u (j' + 1)) ≤ dist (u (j + 1)) x + dist x (u (j' + 1)) :=
    dist_triangle _ _ _
  -- equality is forced
  have hAeq : dist (u j) (u j') = dist (u j) x + dist x (u j') := by
    have hc1 : dist (u (j + 1)) x = dist x (u (j + 1)) := dist_comm _ _
    have hc2 : dist (u j') x = dist x (u j') := dist_comm _ _
    linarith [hexch, hτ, d1, d2, tA, tB]
  -- so x is between u j and u j'
  have hwA : Wbtw ℝ (u j) x (u j') := dist_add_dist_eq_iff.mp hAeq.symm
  have hcolA : Collinear ℝ ({u j, x, u j'} : Set Plane) := hwA.collinear
  have hcol1 : Collinear ℝ ({u j, x, u (j + 1)} : Set Plane) :=
    (mem_segment_iff_wbtw.mp hx1).collinear
  -- merge on the pair (x, u j)
  have hcol1' : Collinear ℝ ({u (j + 1), x, u j} : Set Plane) :=
    hcol1.subset (by intro y hy; simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff] at hy ⊢; tauto)
  have hcolA' : Collinear ℝ ({u j', x, u j} : Set Plane) :=
    hcolA.subset (by intro y hy; simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff] at hy ⊢; tauto)
  have hfinal : Collinear ℝ ({u (j + 1), u j, u j'} : Set Plane) :=
    collinear_merge hxj hcol1' hcolA'
  exact permChain_gen v hgen σ (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) hfinal


end

/-- Signed area of an ordered triple, using the common determinant. -/
def turn (a b c : Plane) : ℝ := cross (b - a) (c - a)

theorem turn_rotate (a b c : Plane) : turn a b c = turn b c a := by
  simp only [turn, cross_apply, Complex.sub_re, Complex.sub_im]
  ring

theorem turn_swap (a b c : Plane) : turn b a c = -turn a b c := by
  simp only [turn, cross_apply, Complex.sub_re, Complex.sub_im]
  ring

theorem collinear_of_turn_eq_zero {a b c : Plane} (h : turn a b c = 0) :
    Collinear ℝ ({a, b, c} : Set Plane) := by
  by_cases hab : a = b
  · subst b
    simpa using collinear_pair ℝ a c
  rw [collinear_iff_of_mem (show a ∈ ({a, b, c} : Set Plane) by simp)]
  refine ⟨b - a, ?_⟩
  intro x hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩
  · have he : (b.re - a.re) * (x.im - a.im) -
        (b.im - a.im) * (x.re - a.re) = 0 := h
    by_cases hRe : b.re - a.re = 0
    · have hIm : b.im - a.im ≠ 0 := by
        intro hi
        exact hab (Complex.ext (by linarith) (by linarith))
      refine ⟨(x.im - a.im) / (b.im - a.im), ?_⟩
      change x = ((x.im - a.im) / (b.im - a.im)) • (b - a) + a
      apply Complex.ext
      · simp only [Complex.add_re, Complex.smul_re, Complex.sub_re, smul_eq_mul, hRe,
          mul_zero, zero_add]
        have hh : (b.im - a.im) * (x.re - a.re) = 0 := by rw [hRe] at he; nlinarith [he]
        have := (mul_eq_zero.mp hh).resolve_left hIm
        linarith
      · simp only [Complex.add_im, Complex.smul_im, Complex.sub_im, smul_eq_mul]
        rw [div_mul_cancel₀ _ hIm]
        ring
    · refine ⟨(x.re - a.re) / (b.re - a.re), ?_⟩
      change x = ((x.re - a.re) / (b.re - a.re)) • (b - a) + a
      apply Complex.ext
      · simp only [Complex.add_re, Complex.smul_re, Complex.sub_re, smul_eq_mul]
        rw [div_mul_cancel₀ _ hRe]
        ring
      · simp only [Complex.add_im, Complex.smul_im, Complex.sub_im, smul_eq_mul]
        field_simp
        nlinarith [he]

/-- A line through two distinct extreme points meets the convex set only
between them. This is the elementary geometric replacement for a crosscut. -/
theorem mem_segment_of_extreme_collinear {Q : Set Plane} {a b x : Plane}
    (ha : a ∈ extremePoints ℝ Q) (hb : b ∈ extremePoints ℝ Q)
    (hab : a ≠ b) (hx : x ∈ Q) (hcol : Collinear ℝ ({a, x, b} : Set Plane)) :
    x ∈ segment ℝ a b := by
  have ha' := mem_extremePoints_iff_forall_segment.mp ha
  have hb' := mem_extremePoints_iff_forall_segment.mp hb
  rcases hcol.wbtw_or_wbtw_or_wbtw with h | h | h
  · exact mem_segment_iff_wbtw.mpr h
  · rcases hb'.2 x hx a ha'.1 (mem_segment_iff_wbtw.mpr h) with he | he
    · subst x; exact right_mem_segment ℝ a b
    · exact False.elim (hab he)
  · rcases ha'.2 b hb'.1 x hx (mem_segment_iff_wbtw.mpr h) with he | he
    · exact False.elim (hab he.symm)
    · subst x; exact left_mem_segment ℝ a b

/-- A segment whose endpoints lie on opposite sides of an extreme-vertex
chord actually crosses that chord, not an extension of its line. -/
theorem segments_intersect_of_opposite_turns {Q : Set Plane} (hQ : Convex ℝ Q)
    {a b c d : Plane} (ha : a ∈ extremePoints ℝ Q) (hb : b ∈ extremePoints ℝ Q)
    (hc : c ∈ Q) (hd : d ∈ Q) (hneg : turn a b c < 0) (hpos : 0 < turn a b d) :
    (segment ℝ a b ∩ segment ℝ c d).Nonempty := by
  let u := turn a b c
  let v := turn a b d
  have hden : 0 < v - u := by dsimp [u, v]; linarith
  let t := -u / (v - u)
  have ht0 : 0 ≤ t := div_nonneg (by dsimp [u]; linarith) hden.le
  have ht1 : t ≤ 1 := (div_le_one hden).mpr (by dsimp [u, v]; linarith)
  let x := (1 - t) • c + t • d
  have hxcd : x ∈ segment ℝ c d :=
    ⟨1 - t, t, sub_nonneg.mpr ht1, ht0, by ring, rfl⟩
  have htx : turn a b x = (1 - t) * u + t * v := by
    simp only [turn, cross_apply, x, u, v, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
    ring
  have hzero : turn a b x = 0 := by
    rw [htx]
    dsimp [t]
    field_simp
    ring
  have hab : a ≠ b := by
    intro he
    subst b
    simp [turn, cross_apply] at hneg
  have hcol : Collinear ℝ ({a, x, b} : Set Plane) := by
    have h := collinear_of_turn_eq_zero hzero
    exact h.subset (by intro z hz; simp only [mem_insert_iff, mem_singleton_iff] at hz ⊢; tauto)
  exact ⟨x, mem_segment_of_extreme_collinear ha hb hab
    ((hQ.segment_subset hc hd) hxcd) hcol, hxcd⟩

/-- Extreme vertices are automatically in general position. -/
theorem inGenPos_of_extreme {ι : Type*} {v : ι → Plane} {Q : Set Plane}
    (hinj : Function.Injective v) (hV : ∀ i, v i ∈ extremePoints ℝ Q) :
    InGenPos v := by
  intro a b c hab hac hbc hcol
  have ha := mem_extremePoints_iff_forall_segment.mp (hV a)
  have hb := mem_extremePoints_iff_forall_segment.mp (hV b)
  have hc := mem_extremePoints_iff_forall_segment.mp (hV c)
  rcases hcol.wbtw_or_wbtw_or_wbtw with h | h | h
  · rcases hb.2 _ ha.1 _ hc.1 (mem_segment_iff_wbtw.mpr h) with h | h
    · exact hab (hinj h)
    · exact hbc (hinj h.symm)
  · rcases hc.2 _ hb.1 _ ha.1 (mem_segment_iff_wbtw.mpr h) with h | h
    · exact hbc (hinj h)
    · exact hac (hinj h)
  · rcases ha.2 _ hc.1 _ hb.1 (mem_segment_iff_wbtw.mpr h) with h | h
    · exact hac (hinj h.symm)
    · exact hab (hinj h.symm)

/-- Non-adjacent edges of the actual minimizing path through extreme vertices
are disjoint. This is the uncrossing endpoint used by the finite proof. -/
theorem ShortestVertexPath.nonAdjacent_edges_disjoint {V : Set Plane}
    (P : ShortestVertexPath V) (hV : V ⊆ extremePoints ℝ (convexHull ℝ V))
    {j j' : ℕ} (hjj' : j + 2 ≤ j') (hj'k : j' + 1 ≤ P.edges) :
    Disjoint (segment ℝ (natExt P.vertex j) (natExt P.vertex (j + 1)))
      (segment ℝ (natExt P.vertex j') (natExt P.vertex (j' + 1))) := by
  have hgen : InGenPos P.vertex := inGenPos_of_extreme P.injective fun i =>
    hV (P.range_eq.subset (mem_range_self i))
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact min_edges_disjoint P.vertex hgen
    (σ := 1) (by simpa only [permChain, Function.comp_def, Equiv.Perm.one_apply] using P.minimal)
    hjj' hj'k hx hy

/-- Completed prefixes group every label attached to the same visiting rank. -/
def completedPrefix {Label : Type*} (visit : Label → ℕ) (r : ℕ) : Set Label :=
  {l | visit l ≤ r}

theorem completedPrefix_tied {Label : Type*} {visit : Label → ℕ}
    {a b : Label} (h : visit a = visit b) (r : ℕ) :
    a ∈ completedPrefix visit r ↔ b ∈ completedPrefix visit r := by
  simp only [completedPrefix, mem_ofPred_eq, h]

/-- A cyclic interval, characterized by absence of four alternating members
and nonmembers. This includes the empty and full intervals. -/
def IsBoundaryInterval {n : ℕ} (S : Set (Fin n)) : Prop :=
  ∀ a b c d : Fin n, a < b → b < c → c < d →
    ¬ (a ∈ S ∧ b ∉ S ∧ c ∈ S ∧ d ∉ S) ∧
    ¬ (a ∉ S ∧ b ∈ S ∧ c ∉ S ∧ d ∈ S)

theorem IsBoundaryInterval.compl {n : ℕ} {S : Set (Fin n)}
    (h : IsBoundaryInterval S) : IsBoundaryInterval Sᶜ := by
  intro a b c d hab hbc hcd
  simpa only [mem_compl_iff, not_not, and_comm] using h a b c d hab hbc hcd

/-- Weakly ordered labels preserve boundary intervals. Equality of geometric
vertices is allowed: an alternating membership pattern itself forces the
relevant inequalities to be strict. -/
theorem IsBoundaryInterval.preimage_monotone {n m : ℕ} {S : Set (Fin n)}
    (hS : IsBoundaryInterval S) (f : Fin m → Fin n) (hf : Monotone f) :
    IsBoundaryInterval (f ⁻¹' S) := by
  intro a b c d hab hbc hcd
  have hab' := hf hab.le
  have hbc' := hf hbc.le
  have hcd' := hf hcd.le
  constructor
  · rintro ⟨ha, hb, hc, hd⟩
    simp only [mem_preimage] at ha hb hc hd
    have fab : f a < f b := lt_of_le_of_ne hab' (by
      intro he; exact hb (he ▸ ha))
    have fbc : f b < f c := lt_of_le_of_ne hbc' (by
      intro he; exact hb (he.symm ▸ hc))
    have fcd : f c < f d := lt_of_le_of_ne hcd' (by
      intro he; exact hd (he ▸ hc))
    exact (hS _ _ _ _ fab fbc fcd).1 ⟨ha, hb, hc, hd⟩
  · rintro ⟨ha, hb, hc, hd⟩
    simp only [mem_preimage] at ha hb hc hd
    have fab : f a < f b := lt_of_le_of_ne hab' (by
      intro he; exact ha (he.symm ▸ hb))
    have fbc : f b < f c := lt_of_le_of_ne hbc' (by
      intro he; exact hc (he ▸ hb))
    have fcd : f c < f d := lt_of_le_of_ne hcd' (by
      intro he; exact hc (he.symm ▸ hd))
    exact (hS _ _ _ _ fab fbc fcd).2 ⟨ha, hb, hc, hd⟩

/-- The two open arcs determined by two indices, cut at index zero. -/
def betweenIndices (a b x : ℕ) : Prop :=
  (a < x ∧ x < b) ∨ (b < x ∧ x < a)

/-- Strict alternation of the endpoints of two chords in boundary order. -/
def alternatingChords (a b c d : ℕ) : Prop :=
  ((betweenIndices a b c ∧ ¬betweenIndices a b d) ∨
    (¬betweenIndices a b c ∧ betweenIndices a b d)) ∧
    a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d

theorem alternatingChords_symm {a b c d : ℕ} :
    alternatingChords a b c d ↔ alternatingChords c d a b := by
  unfold alternatingChords betweenIndices
  omega

private theorem exists_adjacent_change (f : ℕ → Bool) {a b : ℕ}
    (hab : a ≤ b) (hchange : f a ≠ f b) :
    ∃ j, a ≤ j ∧ j < b ∧ f j ≠ f (j + 1) := by
  induction b with
  | zero =>
      have : a = 0 := by omega
      subst a
      exact False.elim (hchange rfl)
  | succ b ih =>
      by_cases he : a = b + 1
      · subst a; exact False.elim (hchange rfl)
      by_cases hf : f a = f b
      · exact ⟨b, by omega, by omega, fun h => hchange (hf.trans h)⟩
      · obtain ⟨j, hj, hjb, hjf⟩ := ih (by omega) hf
        exact ⟨j, hj, by omega, hjf⟩

def indexPath {k : ℕ} (σ : Equiv.Perm (Fin (k + 1))) (i : ℕ) : ℕ :=
  (σ ⟨min i k, by omega⟩).val

private theorem indexPath_eq {k : ℕ} (σ : Equiv.Perm (Fin (k + 1)))
    {i : ℕ} (hi : i ≤ k) :
    indexPath σ i = (σ ⟨i, by omega⟩).val := by
  simp only [indexPath, Nat.min_eq_left hi]

private theorem indexPath_inj {k : ℕ} (σ : Equiv.Perm (Fin (k + 1)))
    {i j : ℕ} (hi : i ≤ k) (hj : j ≤ k) (h : indexPath σ i = indexPath σ j) :
    i = j := by
  rw [indexPath_eq σ hi, indexPath_eq σ hj] at h
  exact Fin.mk.inj (σ.injective (Fin.ext h))

private theorem indexPath_symm {k : ℕ} (σ : Equiv.Perm (Fin (k + 1)))
    (a : Fin (k + 1)) : indexPath σ (σ.symm a).val = a.val := by
  rw [indexPath_eq σ (by omega)]
  simp

/-- Purely finite noncrossing-path argument. If a prefix had alternating
visited and unvisited boundary vertices, the prefix must cross the chord
joining the two unvisited vertices; the continuation must then cross that
prefix edge. Both crossings are obtained by finite adjacent sign changes. -/
theorem permutation_prefix_boundaryInterval {k : ℕ}
    (σ : Equiv.Perm (Fin (k + 1)))
    (hnocross : ∀ j j' : ℕ, j + 2 ≤ j' → j' + 1 ≤ k →
      ¬alternatingChords (indexPath σ j) (indexPath σ (j + 1))
        (indexPath σ j') (indexPath σ (j' + 1))) (r : ℕ) :
    IsBoundaryInterval (completedPrefix (fun i => (σ.symm i).val) r) := by
  classical
  have core (a b c d : Fin (k + 1))
      (hx : alternatingChords a.val c.val b.val d.val)
      (ha : (σ.symm a).val ≤ r) (hc : (σ.symm c).val ≤ r)
      (hb : r < (σ.symm b).val) (hd : r < (σ.symm d).val) : False := by
    let side : ℕ → Bool := fun i => decide
      (betweenIndices b.val d.val (indexPath σ i))
    have hside : side (σ.symm a).val ≠ side (σ.symm c).val := by
      have hh := alternatingChords_symm.mp hx
      simp only [side, indexPath_symm]
      rcases hh.1 with hh | hh <;> simp [hh.1, hh.2]
    have hchange : side (min (σ.symm a).val (σ.symm c).val) ≠
        side (max (σ.symm a).val (σ.symm c).val) := by
      rcases le_total (σ.symm a).val (σ.symm c).val with h | h
      · simpa [min_eq_left h, max_eq_right h] using hside
      · simpa [min_eq_right h, max_eq_left h] using hside.symm
    obtain ⟨j, hja, hjc, hj⟩ := exists_adjacent_change side min_le_max hchange
    have hjr : j + 1 ≤ r := by omega
    have hjk : j + 1 ≤ k := by omega
    have hends (e : ℕ) (he : e ≤ r) (hek : e ≤ k)
        (x : Fin (k + 1)) (hx : r < (σ.symm x).val) :
        indexPath σ e ≠ x.val := by
      intro hh
      have hhi : indexPath σ e = indexPath σ (σ.symm x).val := by
        rw [indexPath_symm]; exact hh
      have := indexPath_inj σ hek (by omega) hhi
      omega
    have hcross : alternatingChords (indexPath σ j) (indexPath σ (j + 1))
        b.val d.val := by
      apply alternatingChords_symm.mpr
      refine ⟨?_, (hends j (by omega) (by omega) b hb).symm,
        (hends (j + 1) hjr hjk b hb).symm,
        (hends j (by omega) (by omega) d hd).symm,
        (hends (j + 1) hjr hjk d hd).symm⟩
      dsimp [side] at hj
      by_cases h₁ : betweenIndices b.val d.val (indexPath σ j) <;>
        by_cases h₂ : betweenIndices b.val d.val (indexPath σ (j + 1)) <;>
        simp_all
    let side' : ℕ → Bool := fun i => decide
      (betweenIndices (indexPath σ j) (indexPath σ (j + 1)) (indexPath σ i))
    have hside' : side' (σ.symm b).val ≠ side' (σ.symm d).val := by
      simp only [side', indexPath_symm]
      rcases hcross.1 with hh | hh <;> simp [hh.1, hh.2]
    have hchange' : side' (min (σ.symm b).val (σ.symm d).val) ≠
        side' (max (σ.symm b).val (σ.symm d).val) := by
      rcases le_total (σ.symm b).val (σ.symm d).val with h | h
      · simpa [min_eq_left h, max_eq_right h] using hside'
      · simpa [min_eq_right h, max_eq_left h] using hside'.symm
    obtain ⟨j', hj'b, hj'd, hj'⟩ :=
      exists_adjacent_change side' min_le_max hchange'
    have hj'k : j' + 1 ≤ k := by omega
    have hjjr : j + 2 ≤ j' := by omega
    apply hnocross j j' hjjr hj'k
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · dsimp [side'] at hj'
      by_cases h₁ : betweenIndices (indexPath σ j) (indexPath σ (j + 1)) (indexPath σ j') <;>
        by_cases h₂ : betweenIndices (indexPath σ j) (indexPath σ (j + 1))
          (indexPath σ (j' + 1)) <;> simp_all
    all_goals
      intro he
      have := indexPath_inj σ (by omega) (by omega) he
      omega
  intro a b c d hab hbc hcd
  constructor
  · rintro ⟨ha, hb, hc, hd⟩
    apply core a b c d
    · unfold alternatingChords betweenIndices
      change a.val < b.val at hab
      change b.val < c.val at hbc
      change c.val < d.val at hcd
      omega
    · exact ha
    · exact hc
    · exact Nat.lt_of_not_ge hb
    · exact Nat.lt_of_not_ge hd
  · rintro ⟨ha, hb, hc, hd⟩
    apply core b a d c
    · unfold alternatingChords betweenIndices
      change a.val < b.val at hab
      change b.val < c.val at hbc
      change c.val < d.val at hcd
      omega
    · exact hb
    · exact hd
    · exact Nat.lt_of_not_ge ha
    · exact Nat.lt_of_not_ge hc

/-- Close a boundary enumeration by repeating its first vertex at the end.
This handles contact labels at `P₋` on both sides of the displayed cyclic cut. -/
def closedBoundaryIndex (k : ℕ) (i : Fin (k + 2)) : Fin (k + 1) :=
  ⟨if i.val = k + 1 then 0 else i.val, by split_ifs <;> omega⟩

theorem closedBoundaryIndex_of_lt {k : ℕ} (i : Fin (k + 2)) (hi : i.val < k + 1) :
    (closedBoundaryIndex k i).val = i.val := by
  simp only [closedBoundaryIndex, if_neg (by omega : i.val ≠ k + 1)]

/-- Repeating the first vertex at the end preserves the cyclic interval
property, including intervals passing through the displayed cut. -/
theorem IsBoundaryInterval.preimage_closedBoundary {k : ℕ} {S : Set (Fin (k + 1))}
    (hS : IsBoundaryInterval S) :
    IsBoundaryInterval (closedBoundaryIndex k ⁻¹' S) := by
  intro a b c d hab hbc hcd
  have ha : a.val < k + 1 := by omega
  have hb : b.val < k + 1 := by omega
  have hc : c.val < k + 1 := by omega
  have hab' : closedBoundaryIndex k a < closedBoundaryIndex k b := by
    change (closedBoundaryIndex k a).val < (closedBoundaryIndex k b).val
    rw [closedBoundaryIndex_of_lt a ha, closedBoundaryIndex_of_lt b hb]
    exact hab
  have hbc' : closedBoundaryIndex k b < closedBoundaryIndex k c := by
    change (closedBoundaryIndex k b).val < (closedBoundaryIndex k c).val
    rw [closedBoundaryIndex_of_lt b hb, closedBoundaryIndex_of_lt c hc]
    exact hbc
  by_cases hd : d.val < k + 1
  · have hcd' : closedBoundaryIndex k c < closedBoundaryIndex k d := by
      change (closedBoundaryIndex k c).val < (closedBoundaryIndex k d).val
      rw [closedBoundaryIndex_of_lt c hc, closedBoundaryIndex_of_lt d hd]
      exact hcd
    exact hS _ _ _ _ hab' hbc' hcd'
  · have hd' : closedBoundaryIndex k d = 0 := by
      apply Fin.ext
      simp [closedBoundaryIndex, show d.val = k + 1 by omega]
    by_cases ha0 : a.val = 0
    · have he : closedBoundaryIndex k a = closedBoundaryIndex k d := by
        rw [hd']
        apply Fin.ext
        simpa only [closedBoundaryIndex_of_lt a ha, Fin.val_zero] using ha0
      constructor
      · rintro ⟨haS, _, _, hdS⟩
        apply hdS
        change closedBoundaryIndex k d ∈ S
        rw [← he]
        exact haS
      · rintro ⟨haS, _, _, hdS⟩
        apply haS
        change closedBoundaryIndex k a ∈ S
        rw [he]
        exact hdS
    · have hda' : closedBoundaryIndex k d < closedBoundaryIndex k a := by
        rw [hd']
        change 0 < (closedBoundaryIndex k a).val
        rw [closedBoundaryIndex_of_lt a ha]
        omega
      have h := hS (closedBoundaryIndex k d) (closedBoundaryIndex k a)
        (closedBoundaryIndex k b) (closedBoundaryIndex k c) hda' hab' hbc'
      constructor
      · rintro ⟨haS, hbS, hcS, hdS⟩
        exact h.2 ⟨hdS, haS, hbS, hcS⟩
      · rintro ⟨haS, hbS, hcS, hdS⟩
        exact h.1 ⟨hdS, haS, hbS, hcS⟩

/-- Geometric version of the finite prefix theorem. The supplied boundary
enumeration must satisfy the explicit chord-intersection property of convex
boundary order. This theorem does not assume prefix order. -/
theorem ShortestVertexPath.prefix_boundaryInterval {V : Set Plane}
    (P : ShortestVertexPath V) (hV : V ⊆ extremePoints ℝ (convexHull ℝ V))
    (boundary : Fin (P.edges + 1) → Plane) (σ : Equiv.Perm (Fin (P.edges + 1)))
    (hvertex : ∀ i, P.vertex i = boundary (σ i))
    (hboundary : ∀ a b c d : Fin (P.edges + 1),
      alternatingChords a.val b.val c.val d.val →
      (segment ℝ (boundary a) (boundary b) ∩
        segment ℝ (boundary c) (boundary d)).Nonempty) (r : ℕ) :
    IsBoundaryInterval (completedPrefix (fun i => (σ.symm i).val) r) := by
  apply permutation_prefix_boundaryInterval σ
  intro j j' hjj' hj'k hcross
  have hjk : j + 1 ≤ P.edges := by omega
  have hmap {i : ℕ} (hi : i ≤ P.edges) :
      natExt P.vertex i = boundary (σ ⟨i, by omega⟩) := by
    rw [natExt_of_le P.vertex hi, hvertex]
  have hcross' : alternatingChords
      (σ ⟨j, by omega⟩).val (σ ⟨j + 1, by omega⟩).val
      (σ ⟨j', by omega⟩).val (σ ⟨j' + 1, by omega⟩).val := by
    simpa only [indexPath_eq σ (by omega : j ≤ P.edges), indexPath_eq σ hjk,
      indexPath_eq σ (by omega : j' ≤ P.edges), indexPath_eq σ hj'k] using hcross
  obtain ⟨x, hx, hy⟩ := hboundary _ _ _ _ hcross'
  have hd := P.nonAdjacent_edges_disjoint hV hjj' hj'k
  apply Set.disjoint_left.mp hd
  · simpa only [hmap (by omega : j ≤ P.edges), hmap hjk] using hx
  · simpa only [hmap (by omega : j' ≤ P.edges), hmap hj'k] using hy

/-- Completed contact prefixes, with weakly ordered contacts and coincident
labels including the repeated floor vertex. The contact map is into the
closed boundary list, so it is allowed to take the final index as well as zero. -/
theorem ShortestVertexPath.contact_prefix_boundaryInterval {V : Set Plane}
    (P : ShortestVertexPath V) (hV : V ⊆ extremePoints ℝ (convexHull ℝ V))
    (boundary : Fin (P.edges + 1) → Plane) (σ : Equiv.Perm (Fin (P.edges + 1)))
    (hvertex : ∀ i, P.vertex i = boundary (σ i))
    (hboundary : ∀ a b c d : Fin (P.edges + 1),
      alternatingChords a.val b.val c.val d.val →
      (segment ℝ (boundary a) (boundary b) ∩
        segment ℝ (boundary c) (boundary d)).Nonempty)
    {N : ℕ} (contact : Fin N → Fin (P.edges + 2)) (hcontact : Monotone contact) (r : ℕ) :
    IsBoundaryInterval (completedPrefix
      (fun l => (σ.symm (closedBoundaryIndex P.edges (contact l))).val) r) := by
  exact IsBoundaryInterval.preimage_monotone
    (P.prefix_boundaryInterval hV boundary σ hvertex hboundary r).preimage_closedBoundary
    contact hcontact

/-- Contact indices in *boundary* order:
`P₋, P₊, R₀, ..., R_(kR-1), P₀, L₀, ..., L_(kL-1)`.
This order differs from a coefficient array that stores all three anchors
first; such an array must be reindexed before using the following lemmas. -/
abbrev ContactIndex (kR kL : ℕ) := Fin (kR + kL + 3)

def floorMinus (kR kL : ℕ) : ContactIndex kR kL := ⟨0, by omega⟩
def floorPlus (kR kL : ℕ) : ContactIndex kR kL := ⟨1, by omega⟩
def topIndex (kR kL : ℕ) : ContactIndex kR kL := ⟨kR + 2, by omega⟩
def rightIndex {kR : ℕ} (kL : ℕ) (i : Fin kR) : ContactIndex kR kL :=
  ⟨i.val + 2, by omega⟩
def leftIndex (kR : ℕ) {kL : ℕ} (j : Fin kL) : ContactIndex kR kL :=
  ⟨kR + 3 + j.val, by omega⟩

/-- The max-rank argument from the paper, with ties retained exactly. -/
theorem contact_rank_bounds {kR kL : ℕ} (t : ContactIndex kR kL → ℕ)
    (hprefix : ∀ r, IsBoundaryInterval (completedPrefix t r))
    (hminus : t (floorMinus kR kL) < t (topIndex kR kL))
    (hplus : t (topIndex kR kL) < t (floorPlus kR kL)) :
    (∀ i : Fin kR, t (topIndex kR kL) ≤ t (rightIndex kL i)) ∧
      (∀ j : Fin kL, t (leftIndex kR j) ≤ t (topIndex kR kL)) := by
  constructor
  · intro i
    by_contra hi
    have hi' : t (rightIndex kL i) < t (topIndex kR kL) := by omega
    let r := max (t (rightIndex kL i)) (t (floorMinus kR kL))
    have hr : r < t (topIndex kR kL) := max_lt hi' hminus
    have h := (hprefix r (floorMinus kR kL) (floorPlus kR kL)
      (rightIndex kL i) (topIndex kR kL)
      (by change (0 : ℕ) < 1; omega)
      (by change 1 < i.val + 2; omega)
      (by change i.val + 2 < kR + 2; omega)).1
    apply h
    simp only [completedPrefix, mem_ofPred_eq]
    exact ⟨le_max_right _ _, by omega, le_max_left _ _, by omega⟩
  · intro j
    by_contra hj
    have h := (hprefix (t (topIndex kR kL))
      (floorMinus kR kL) (floorPlus kR kL) (topIndex kR kL) (leftIndex kR j)
      (by change (0 : ℕ) < 1; omega)
      (by change 1 < kR + 2; omega)
      (by change kR + 2 < kR + 3 + j.val; omega)).1
    apply h
    simp only [completedPrefix, mem_ofPred_eq]
    exact ⟨hminus.le, by omega, le_rfl, by omega⟩

private theorem exists_initial_segment {k : ℕ} (P : Fin k → Prop)
    (hdown : ∀ i j : Fin k, i ≤ j → P j → P i) :
    ∃ p : ℕ, p ≤ k ∧ ∀ i : Fin k, i.val < p ↔ P i := by
  classical
  have hex : ∃ p : ℕ, ∀ i : Fin k, p ≤ i.val → ¬P i :=
    ⟨k, fun i hi => by omega⟩
  let p := Nat.find hex
  have hcut : ∀ i : Fin k, p ≤ i.val → ¬P i := Nat.find_spec hex
  have hpk : p ≤ k := Nat.find_min' hex (fun i hi => by omega)
  refine ⟨p, hpk, ?_⟩
  intro i
  constructor
  · intro hi
    by_contra hn
    have hcuti : ∀ j : Fin k, i.val ≤ j.val → ¬P j :=
      fun j hij hj => hn (hdown i j hij hj)
    have : p ≤ i.val := Nat.find_min' hex hcuti
    omega
  · intro hi
    by_contra hn
    exact hcut i (by omega) hi

/-- The split exists with the paper's endpoint conventions, including all
coincident contacts. `p` counts right contacts at or after `P₊`; `q` counts
left contacts strictly after `P₋`. -/
theorem exists_contact_split {kR kL : ℕ} (t : ContactIndex kR kL → ℕ)
    (hprefix : ∀ r, IsBoundaryInterval (completedPrefix t r))
    (hminus : t (floorMinus kR kL) < t (topIndex kR kL))
    (hplus : t (topIndex kR kL) < t (floorPlus kR kL)) :
    ∃ p q : ℕ, p ≤ kR ∧ q ≤ kL ∧
      (∀ i : Fin kR, i.val < p ↔ t (floorPlus kR kL) ≤ t (rightIndex kL i)) ∧
      (∀ j : Fin kL, j.val < q ↔ t (floorMinus kR kL) < t (leftIndex kR j)) := by
  have hdR : ∀ i j : Fin kR, i ≤ j →
      t (floorPlus kR kL) ≤ t (rightIndex kL j) →
      t (floorPlus kR kL) ≤ t (rightIndex kL i) := by
    intro i j hij hj
    rcases eq_or_lt_of_le hij with rfl | hij
    · exact hj
    by_contra hi
    let r := t (floorPlus kR kL) - 1
    have ht : t (topIndex kR kL) ≤ r := by dsimp [r]; omega
    have hri : t (rightIndex kL i) ≤ r := by dsimp [r]; omega
    have hrp : r < t (floorPlus kR kL) := by dsimp [r]; omega
    have h := (hprefix r (floorPlus kR kL) (rightIndex kL i)
      (rightIndex kL j) (topIndex kR kL)
      (by change 1 < i.val + 2; omega)
      (by change i.val + 2 < j.val + 2; exact Nat.add_lt_add_right hij _)
      (by change j.val + 2 < kR + 2; omega)).2
    apply h
    simp only [completedPrefix, mem_ofPred_eq]
    exact ⟨by omega, hri, by omega, ht⟩
  have hdL : ∀ i j : Fin kL, i ≤ j →
      t (floorMinus kR kL) < t (leftIndex kR j) →
      t (floorMinus kR kL) < t (leftIndex kR i) := by
    intro i j hij hj
    rcases eq_or_lt_of_le hij with rfl | hij
    · exact hj
    by_contra hi
    have h := (hprefix (t (floorMinus kR kL))
      (floorMinus kR kL) (floorPlus kR kL) (leftIndex kR i) (leftIndex kR j)
      (by change (0 : ℕ) < 1; omega)
      (by change 1 < kR + 3 + i.val; omega)
      (by change kR + 3 + i.val < kR + 3 + j.val; exact Nat.add_lt_add_left hij _)).1
    apply h
    simp only [completedPrefix, mem_ofPred_eq]
    exact ⟨le_rfl, by omega, by omega, by omega⟩
  obtain ⟨p, hp, hsp⟩ := exists_initial_segment _ hdR
  obtain ⟨q, hq, hsq⟩ := exists_initial_segment _ hdL
  exact ⟨p, q, hp, hq, hsp, hsq⟩

/-- Cutting a cyclic interval at an excluded zero leaves a linear interval. -/
theorem IsBoundaryInterval.ordConnected_of_zero_not_mem {n : ℕ} {S : Set (Fin (n + 1))}
    (hS : IsBoundaryInterval S) (hzero : (0 : Fin (n + 1)) ∉ S) :
    Set.OrdConnected S := by
  constructor
  intro a ha c hc b hb
  by_contra hn
  have hza : (0 : Fin (n + 1)) < a := by
    have : a ≠ 0 := fun he => hzero (he ▸ ha)
    exact lt_of_le_of_ne (Fin.zero_le a) this.symm
  have hab : a < b := lt_of_le_of_ne hb.1 (by intro he; exact hn (he ▸ ha))
  have hbc : b < c := lt_of_le_of_ne hb.2 (by intro he; exact hn (he.symm ▸ hc))
  exact (hS 0 a b c hza hab hbc).2 ⟨hzero, ha, hn, hc⟩

private theorem exists_interval_endpoints {n : ℕ} {S : Set (Fin n)}
    (hne : S.Nonempty) (hS : Set.OrdConnected S) :
    ∃ a b : Fin n, a ∈ S ∧ b ∈ S ∧ S = Set.Icc a b := by
  classical
  let F := S.toFinite.toFinset
  have hF : ∀ x, x ∈ F ↔ x ∈ S := fun x => Set.Finite.mem_toFinset _
  have hFn : F.Nonempty := by obtain ⟨x, hx⟩ := hne; exact ⟨x, (hF x).mpr hx⟩
  obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image F id hFn
  obtain ⟨b, hb, hmax⟩ := Finset.exists_max_image F id hFn
  refine ⟨a, b, (hF a).mp ha, (hF b).mp hb, Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    exact ⟨hmin x ((hF x).mpr hx), hmax x ((hF x).mpr hx)⟩
  · exact hS.out ((hF a).mp ha) ((hF b).mp hb)

theorem contactIndex_cases {kR kL : ℕ} (x : ContactIndex kR kL) :
    x = floorMinus kR kL ∨ x = floorPlus kR kL ∨
      (∃ i : Fin kR, x = rightIndex kL i) ∨ x = topIndex kR kL ∨
      (∃ j : Fin kL, x = leftIndex kR j) := by
  by_cases h0 : x.val = 0
  · exact Or.inl (Fin.ext h0)
  by_cases h1 : x.val = 1
  · exact Or.inr (Or.inl (Fin.ext h1))
  by_cases hR : x.val < kR + 2
  · exact Or.inr (Or.inr (Or.inl ⟨⟨x.val - 2, by omega⟩, Fin.ext (by
      simp only [rightIndex]; omega)⟩))
  by_cases hT : x.val = kR + 2
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext hT))))
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨x.val - (kR + 3), by omega⟩,
    Fin.ext (by simp only [leftIndex]; omega)⟩)))

/-- The paper's four families, in zero-based contact indices. The first
two constructors are visited sets and the last two are unvisited sets. -/
def FourFamily (kR kL pLo pHi qLo qHi : ℕ) (S : Set (ContactIndex kR kL)) : Prop :=
  (∃ a b : ℕ, qLo ≤ a ∧ a ≤ b ∧ b ≤ kL ∧
    S = {x | kR + 3 + a ≤ x.val ∧ x.val < kR + 3 + b}) ∨
  (∃ j : ℕ, j ≤ qHi ∧ S = {x | x.val = 0 ∨ kR + 3 + j ≤ x.val}) ∨
  (∃ s : ℕ, pLo ≤ s ∧ s ≤ kR ∧ S = {x | x.val = 1 ∨ 2 ≤ x.val ∧ x.val < 2 + s}) ∨
  (∃ a b : ℕ, a ≤ b ∧ b ≤ pHi ∧
    S = {x | 2 + a ≤ x.val ∧ x.val < 2 + b})

/-- Semantic bridge to the four norm-test families. Its boundary-prefix
hypothesis is local combinatorial input, not an axiom about geometric
witnesses. The geometric path/order theorem supplies that input. -/
theorem completedPrefix_four_families {kR kL : ℕ} (t : ContactIndex kR kL → ℕ)
    (hprefix : ∀ r, IsBoundaryInterval (completedPrefix t r))
    (hminus : t (floorMinus kR kL) < t (topIndex kR kL))
    (hplus : t (topIndex kR kL) < t (floorPlus kR kL))
    {p q pLo pHi qLo qHi : ℕ} (hp : p ≤ kR) (_hq : q ≤ kL)
    (hpLo : pLo ≤ p) (hpHi : p ≤ pHi) (hqLo : qLo ≤ q) (hqHi : q ≤ qHi)
    (hsplitR : ∀ i : Fin kR, i.val < p ↔ t (floorPlus kR kL) ≤ t (rightIndex kL i))
    (hsplitL : ∀ j : Fin kL, j.val < q ↔ t (floorMinus kR kL) < t (leftIndex kR j))
    (r : ℕ) (hne : (completedPrefix t r).Nonempty)
    (hproper : (completedPrefix t r)ᶜ.Nonempty) :
    FourFamily kR kL pLo pHi qLo qHi (completedPrefix t r) ∨
      FourFamily kR kL pLo pHi qLo qHi (completedPrefix t r)ᶜ := by
  classical
  obtain ⟨hR, hL⟩ := contact_rank_bounds t hprefix hminus hplus
  let S := completedPrefix t r
  have hm (x : ContactIndex kR kL) : x ∈ S ↔ t x ≤ r := Iff.rfl
  have hcm (x : ContactIndex kR kL) : x ∈ Sᶜ ↔ r < t x := by
    simp only [S, completedPrefix, mem_compl_iff, mem_ofPred_eq, not_le]
  by_cases hstage1 : r < t (floorMinus kR kL)
  · have hzero : (0 : ContactIndex kR kL) ∉ S := by
      change ¬t (floorMinus kR kL) ≤ r
      omega
    obtain ⟨a, b, ha, hb, hEq⟩ :=
      exists_interval_endpoints hne ((hprefix r).ordConnected_of_zero_not_mem hzero)
    have hleft (x : ContactIndex kR kL) (hx : x ∈ S) :
        kR + 3 + qLo ≤ x.val := by
      have ht := (hm x).mp hx
      rcases contactIndex_cases x with he | he | ⟨i, he⟩ | he | ⟨j, he⟩
      · subst x; omega
      · subst x; omega
      · subst x; have := hR i; omega
      · subst x; omega
      · subst x
        have hj : q ≤ j.val := by
          by_contra hn
          have := (hsplitL j).mp (by omega)
          omega
        simp only [leftIndex]
        omega
    have ha' := hleft a ha
    have hb' := hleft b hb
    have hab : a.val ≤ b.val := by
      have : a ∈ Set.Icc a b := hEq ▸ ha
      exact this.2
    refine Or.inl (Or.inl ⟨a.val - (kR + 3), b.val - (kR + 3) + 1,
      by omega, by omega, by omega, ?_⟩)
    rw [hEq]
    ext x
    simp only [mem_Icc, Fin.le_def, mem_ofPred_eq]
    omega
  · have hrminus : t (floorMinus kR kL) ≤ r := by omega
    have hzero : (0 : ContactIndex kR kL) ∉ Sᶜ := by
      change ¬¬t (floorMinus kR kL) ≤ r
      exact not_not.mpr hrminus
    obtain ⟨a, b, ha, hb, hEq⟩ := exists_interval_endpoints hproper
      ((hprefix r).compl.ordConnected_of_zero_not_mem hzero)
    have hab : a.val ≤ b.val := by
      have : a ∈ Set.Icc a b := hEq ▸ ha
      exact this.2
    have haPos : 0 < a.val := by
      by_contra hn
      have he : a = (0 : ContactIndex kR kL) := by
        apply Fin.ext
        change a.val = 0
        omega
      exact hzero (he ▸ ha)
    by_cases hstage2 : r < t (topIndex kR kL)
    · have h1 : floorPlus kR kL ∈ Sᶜ := (hcm _).mpr (by omega)
      have ht : topIndex kR kL ∈ Sᶜ := (hcm _).mpr hstage2
      have ha1 : a.val = 1 := by
        have hh : floorPlus kR kL ∈ Set.Icc a b := hEq ▸ h1
        have : a.val ≤ 1 := hh.1
        omega
      have hbTop : kR + 2 ≤ b.val := by
        have hh : topIndex kR kL ∈ Set.Icc a b := hEq ▸ ht
        exact hh.2
      have hbq : b.val - (kR + 2) ≤ q := by
        by_contra hn
        let j : Fin kL := ⟨b.val - (kR + 3), by omega⟩
        have he : leftIndex kR j = b := Fin.ext (by simp [leftIndex, j]; omega)
        have hj : ¬j.val < q := by dsimp [j]; omega
        have htj : t (leftIndex kR j) ≤ t (floorMinus kR kL) := by
          have := (hsplitL j).not.mp hj
          omega
        have htb := (hcm b).mp hb
        rw [he] at htj
        omega
      refine Or.inl (Or.inr (Or.inl ⟨b.val - (kR + 2), by omega, ?_⟩))
      have hs : completedPrefix t r = (Set.Icc a b)ᶜ := by
        rw [← hEq]
        simp
      rw [hs]
      ext x
      simp only [mem_compl_iff, mem_Icc, Fin.le_def, mem_ofPred_eq]
      omega
    · have hrtop : t (topIndex kR kL) ≤ r := by omega
      by_cases hstage3 : r < t (floorPlus kR kL)
      · have h1 : floorPlus kR kL ∈ Sᶜ := (hcm _).mpr hstage3
        have ha1 : a.val = 1 := by
          have hh : floorPlus kR kL ∈ Set.Icc a b := hEq ▸ h1
          have : a.val ≤ 1 := hh.1
          omega
        have hbTop : b.val < kR + 2 := by
          have ht := (hcm b).mp hb
          rcases contactIndex_cases b with he | he | ⟨i, he⟩ | he | ⟨j, he⟩
          · subst b; omega
          · subst b; change 1 < kR + 2; omega
          · subst b; change i.val + 2 < kR + 2; omega
          · subst b; omega
          · subst b; have := hL j; omega
        have hpb : p ≤ b.val - 1 := by
          by_contra hn
          let i : Fin kR := ⟨b.val - 1, by omega⟩
          have hit := (hsplitR i).mp (by dsimp [i]; omega)
          have him : rightIndex kL i ∈ Sᶜ := (hcm _).mpr (by omega)
          have hh : rightIndex kL i ∈ Set.Icc a b := hEq ▸ him
          have := hh.2
          simp only [Fin.le_def, rightIndex, i] at this
          omega
        refine Or.inr (Or.inr (Or.inr (Or.inl ⟨b.val - 1, by omega, by omega, ?_⟩)))
        rw [hEq]
        ext x
        simp only [mem_Icc, Fin.le_def, mem_ofPred_eq]
        omega
      · have hrplus : t (floorPlus kR kL) ≤ r := by omega
        have hright (x : ContactIndex kR kL) (hx : x ∈ Sᶜ) :
            2 ≤ x.val ∧ x.val < 2 + p := by
          have ht := (hcm x).mp hx
          rcases contactIndex_cases x with he | he | ⟨i, he⟩ | he | ⟨j, he⟩
          · subst x; omega
          · subst x; omega
          · subst x
            have hi := (hsplitR i).mpr (by omega)
            simp only [rightIndex]
            omega
          · subst x; omega
          · subst x; have := hL j; omega
        have ha' := hright a ha
        have hb' := hright b hb
        refine Or.inr (Or.inr (Or.inr (Or.inr ⟨a.val - 2, b.val - 1,
          by omega, by omega, ?_⟩)))
        rw [hEq]
        ext x
        simp only [mem_Icc, Fin.le_def, mem_ofPred_eq]
        omega

/-- Three radially ordered extreme vertices turn strictly counterclockwise.
Otherwise the middle vertex is a convex combination of the other three.
The proof uses mathlib's convexity of a convex set with an extreme point removed. -/
theorem turn_pos_of_radial_order {Q : Set Plane} (hQ : Convex ℝ Q)
    {a b c d : Plane} (ha : a ∈ Q) (hb : b ∈ Q)
    (hc : c ∈ extremePoints ℝ Q) (hd : d ∈ Q)
    (hbc : 0 < turn a b c) (hcd : 0 < turn a c d) (hbd : 0 < turn a b d) :
    0 < turn b c d := by
  by_contra h
  have hle : turn b c d ≤ 0 := le_of_not_gt h
  let D := turn a b d
  let β := turn a c d / D
  let γ := turn a b c / D
  have hD : 0 < D := hbd
  have hβ : 0 ≤ β := (div_pos hcd hD).le
  have hγ : 0 ≤ γ := (div_pos hbc hD).le
  have hid : turn b c d = turn a c d + turn a b c - D := by
    simp only [D, turn, cross_apply, Complex.sub_re, Complex.sub_im]; ring
  have hs : β + γ ≤ 1 := by
    dsimp [β, γ]
    rw [← add_div, div_le_one hD]
    linarith
  have hrep : (1 - β - γ) • a + β • b + γ • d = c := by
    apply Complex.ext <;>
      simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
        smul_eq_mul, β, γ]
    all_goals
      field_simp [ne_of_gt hD]
      simp only [D, turn, cross_apply, Complex.sub_re, Complex.sub_im]
      ring
  have hca : c ≠ a := by
    intro he
    have hz : turn a b c = 0 := by rw [he]; simp [turn, cross_apply]
    linarith
  have hcb : c ≠ b := by
    intro he
    have hz : turn a b c = 0 := by rw [he]; simp [turn, cross_apply, mul_comm]
    linarith
  have hcd' : c ≠ d := by
    intro he
    have hz : turn a c d = 0 := by rw [he]; simp [turn, cross_apply, mul_comm]
    linarith
  have hremove := (hQ.mem_extremePoints_iff_convex_sdiff.mp hc).2
  let w : Fin 3 → ℝ := ![1 - β - γ, β, γ]
  let z : Fin 3 → Plane := ![a, b, d]
  have hm : (∑ i : Fin 3, w i • z i) ∈ Q \ {c} := by
    apply hremove.sum_mem
    · intro i _; fin_cases i <;> simp [w] <;> linarith
    · simp [w, Fin.sum_univ_succ]
    · intro i _; fin_cases i <;> simp [z, ha, hb, hd, Ne.symm hca, Ne.symm hcb, Ne.symm hcd']
  have he : (∑ i : Fin 3, w i • z i) = c := by
    simpa [w, z, Fin.sum_univ_succ, add_assoc] using hrep
  rw [he] at hm
  exact hm.2 rfl

private structure KeyIndex (n : ℕ) where
  index : Fin n
  deriving Fintype

/-- Sort an injective key without replacing the standard order on `Fin n`. -/
theorem exists_sorted_permutation {n : ℕ} {α : Type*} [LinearOrder α]
    (key : Fin n → α) (hinj : Function.Injective key) :
    ∃ e : Equiv.Perm (Fin n), StrictMono (key ∘ e) := by
  let : LinearOrder (KeyIndex n) :=
    LinearOrder.lift' (fun i => key i.index) (fun ⟨i⟩ ⟨j⟩ h => congrArg KeyIndex.mk (hinj h))
  let q : KeyIndex n ≃ Fin n := ⟨KeyIndex.index, KeyIndex.mk, by intro x; rfl, by intro x; rfl⟩
  let e := Fintype.orderIsoFinOfCardEq (KeyIndex n)
    (by simpa using Fintype.card_congr q)
  let σ : Equiv.Perm (Fin n) := e.toEquiv.trans q
  refine ⟨σ, ?_⟩
  intro i j h
  change key (e i).index < key (e j).index
  have hh : e i < e j := e.lt_iff_lt.mpr h
  exact hh

/-- Strictly counterclockwise triples imply the explicit alternating-chord
intersection property used by the finite path proof. -/
theorem alternating_segments_intersect {n : ℕ} (v : Fin n → Plane)
    (hex : ∀ i, v i ∈ extremePoints ℝ (convexHull ℝ (Set.range v)))
    (hturn : ∀ a b c, a < b → b < c → 0 < turn (v a) (v b) (v c))
    {a b c d : Fin n} (halt : alternatingChords a.val b.val c.val d.val) :
    (segment ℝ (v a) (v b) ∩ segment ℝ (v c) (v d)).Nonempty := by
  have cyc (i j k : Fin n) (h : i < j ∧ j < k ∨ j < k ∧ k < i ∨ k < i ∧ i < j) :
      0 < turn (v i) (v j) (v k) := by
    rcases h with h | h | h
    · exact hturn _ _ _ h.1 h.2
    · rw [turn_rotate]; exact hturn _ _ _ h.1 h.2
    · rw [turn_rotate, turn_rotate]; exact hturn _ _ _ h.1 h.2
  have orient (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      (0 < turn (v i) (v j) (v k) ↔
        (i.val < j.val ∧ j.val < k.val ∨ j.val < k.val ∧ k.val < i.val ∨
          k.val < i.val ∧ i.val < j.val)) := by
    constructor
    · intro ht
      by_contra h
      have h' : j < i ∧ i < k ∨ i < k ∧ k < j ∨ k < j ∧ j < i := by
        simp only [Ne, Fin.ext_iff] at hij hik hjk
        change (j.val < i.val ∧ i.val < k.val ∨ i.val < k.val ∧ k.val < j.val ∨
          k.val < j.val ∧ j.val < i.val)
        omega
      have hh := cyc j i k h'
      rw [turn_swap] at hh
      linarith
    · exact cyc i j k
  have hn : a ≠ b ∧ c ≠ d := by
    unfold alternatingChords betweenIndices at halt
    constructor <;> intro h <;> subst_vars <;> omega
  have ho : (0 < turn (v a) (v b) (v c) ∧ turn (v a) (v b) (v d) < 0) ∨
      (turn (v a) (v b) (v c) < 0 ∧ 0 < turn (v a) (v b) (v d)) := by
    have hac : a ≠ c := fun h => halt.2.1 (congrArg Fin.val h)
    have had : a ≠ d := fun h => halt.2.2.1 (congrArg Fin.val h)
    have hbc : b ≠ c := fun h => halt.2.2.2.1 (congrArg Fin.val h)
    have hbd : b ≠ d := fun h => halt.2.2.2.2 (congrArg Fin.val h)
    have h₁ := orient a b c hn.1 hac hbc
    have h₂ := orient a b d hn.1 had hbd
    have h₃ := orient b a c hn.1.symm hbc hac
    have h₄ := orient b a d hn.1.symm hbd had
    rw [turn_swap] at h₃ h₄
    have hal := halt
    unfold alternatingChords betweenIndices at hal
    by_cases h : 0 < turn (v a) (v b) (v c)
    · left; refine ⟨h, ?_⟩
      have : 0 < -turn (v a) (v b) (v d) := h₄.mpr (by
        have := h₁.mp h; omega)
      linarith
    · right
      have hh : 0 < -turn (v a) (v b) (v c) := h₃.mpr (by
        have := mt h₁.mpr h; omega)
      refine ⟨by linarith, h₂.mpr ?_⟩
      have := h₃.mp hh
      omega
  rcases ho with h | h
  · have hh := segments_intersect_of_opposite_turns (convex_convexHull ℝ _) (hex a) (hex b)
      (hex d).1 (hex c).1 h.2 h.1
    simpa only [segment_symm ℝ (v d) (v c)] using hh
  · exact segments_intersect_of_opposite_turns (convex_convexHull ℝ _) (hex a) (hex b)
      (hex c).1 (hex d).1 h.1 h.2

end MoserWorm.UpperBound
