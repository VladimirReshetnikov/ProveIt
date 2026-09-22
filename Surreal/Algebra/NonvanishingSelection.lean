import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Preorder.Finite

/-!
# Simultaneous nonvanishing selection

This file proves `meas:lem:global` in
`docs/surreal/hahn-valued-measures-and-probability/article.tex`: given finitely
supported functionals `L_n(A) = ∑_{x ∈ F_n ∩ A} c_{n,x}`, each with a nonzero
coefficient, some set `A` makes infinitely many of them nonzero. The set can be
chosen inside `⋃ F_n`.

The source argues probabilistically. The proof here is deterministic. If
infinitely many of the nonzero-coefficient supports lie in one finite set, a
single point of that set works for infinitely many functionals by the pigeonhole
principle. Otherwise every finite set misses the nonzero support of all but
finitely many functionals, so one can choose indices `n_0 < n_1 < ⋯` and fresh
points `x_k` with nonzero coefficient for `L_{n_k}` outside all earlier supports.
Including `x_k` exactly when the earlier chosen points contribute zero to
`L_{n_k}` makes every `L_{n_k}` nonzero.
-/

namespace Surreal.Selection

open Finset

variable {X k : Type*} [AddCommGroup k]

noncomputable section

/-- The finitely supported functional `A ↦ ∑_{x ∈ F ∩ A} c x`. -/
def supportedSum (F : Finset X) (c : X → k) (A : Set X) : k := by
  classical
  exact ∑ x ∈ F.filter (· ∈ A), c x

/-- `meas:lem:global`: some set `A ⊆ ⋃ F_n` makes infinitely many of the functionals
nonzero. -/
theorem exists_infinite_ne_zero (F : ℕ → Finset X) (c : ℕ → X → k)
    (hne : ∀ n, ∃ x ∈ F n, c n x ≠ 0) :
    ∃ A : Set X, A ⊆ ⋃ n, (F n : Set X) ∧ {n | supportedSum (F n) (c n) A ≠ 0}.Infinite := by
  classical
  let G : ℕ → Finset X := fun n => (F n).filter fun x => c n x ≠ 0
  have hG : ∀ n, (G n).Nonempty := fun n => by
    obtain ⟨x, hx, hc⟩ := hne n
    exact ⟨x, Finset.mem_filter.mpr ⟨hx, hc⟩⟩
  have hsingle : ∀ n x, x ∈ G n → supportedSum (F n) (c n) {x} = c n x := by
    intro n x hx
    have hxF : x ∈ F n := (Finset.mem_filter.mp hx).1
    have hfilter : (F n).filter (· ∈ ({x} : Set X)) = {x} := by
      ext y
      simp only [Finset.mem_filter, Set.mem_singleton_iff, Finset.mem_singleton]
      exact ⟨fun h => h.2, fun h => ⟨h ▸ hxF, h⟩⟩
    rw [supportedSum]
    convert Finset.sum_singleton (c n) x
    convert hfilter
  by_cases hcase : ∃ T : Finset X, {n | G n ⊆ T}.Infinite
  · -- Pigeonhole: one point is a nonzero-coefficient point for infinitely many indices.
    obtain ⟨T, hT⟩ := hcase
    haveI : Infinite {n // G n ⊆ T} := hT.to_subtype
    let f : {n // G n ⊆ T} → T := fun n => ⟨(hG n.1).choose, n.2 (hG n.1).choose_spec⟩
    obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber f
    refine ⟨{y.1}, ?_, ?_⟩
    · obtain ⟨n, hn⟩ := (Set.infinite_coe_iff.mp hy).nonempty
      have hyn : y.1 = (hG n.1).choose := (congrArg Subtype.val hn).symm
      exact Set.singleton_subset_iff.mpr (Set.mem_iUnion.mpr ⟨n.1, by
        rw [hyn]; exact (Finset.mem_filter.mp (hG n.1).choose_spec).1⟩)
    · refine ((Set.infinite_coe_iff.mp hy).image Subtype.val_injective.injOn).mono ?_
      rintro _ ⟨n, hn, rfl⟩
      have hyn : y.1 = (hG n.1).choose := (congrArg Subtype.val hn).symm
      show supportedSum (F n.1) (c n.1) {y.1} ≠ 0
      rw [hyn, hsingle _ _ (hG n.1).choose_spec]
      exact (Finset.mem_filter.mp (hG n.1).choose_spec).2
  · -- Every finite set contains the nonzero support of only finitely many functionals.
    push Not at hcase
    have hfresh : ∀ (T : Finset X) (m : ℕ), ∃ p : ℕ × X, m < p.1 ∧ p.2 ∈ G p.1 ∧ p.2 ∉ T := by
      intro T m
      obtain ⟨b, hb⟩ := (hcase T).bddAbove
      obtain ⟨x, hxG, hxT⟩ : ∃ x ∈ G (max m b + 1), x ∉ T := by
        by_contra h
        push Not at h
        have := hb (show max m b + 1 ∈ {n | G n ⊆ T} from fun x hx => h x hx)
        omega
      exact ⟨(max m b + 1, x), by omega, hxG, hxT⟩
    choose nxt hnxt using hfresh
    -- The state records the union of the supports used so far and the last index.
    let st : ℕ → Finset X × ℕ := fun k => Nat.rec (∅, 0)
      (fun _ s => (s.1 ∪ F (nxt s.1 s.2).1, (nxt s.1 s.2).1)) k
    let n : ℕ → ℕ := fun k => (nxt (st k).1 (st k).2).1
    let x : ℕ → X := fun k => (nxt (st k).1 (st k).2).2
    have hst_succ : ∀ k, st (k + 1) = ((st k).1 ∪ F (n k), n k) := fun k => rfl
    have hn_lt : ∀ k, (st k).2 < n k := fun k => (hnxt _ _).1
    have hxG : ∀ k, x k ∈ G (n k) := fun k => (hnxt _ _).2.1
    have hxF : ∀ k, x k ∈ F (n k) := fun k => (Finset.mem_filter.mp (hxG k)).1
    have hxc : ∀ k, c (n k) (x k) ≠ 0 := fun k => (Finset.mem_filter.mp (hxG k)).2
    have hxT : ∀ k, x k ∉ (st k).1 := fun k => (hnxt _ _).2.2
    have hmono : ∀ j k, j ≤ k → (st j).1 ⊆ (st k).1 := by
      intro j k hjk
      induction hjk with
      | refl => exact le_rfl
      | step _ ih => exact ih.trans (by rw [hst_succ]; exact Finset.subset_union_left)
    have hFsub : ∀ j k, j < k → F (n j) ⊆ (st k).1 := fun j k hjk =>
      (by rw [hst_succ]; exact Finset.subset_union_right : F (n j) ⊆ (st (j + 1)).1).trans
        (hmono _ _ hjk)
    have hn_strict : StrictMono n := by
      refine strictMono_nat_of_lt_succ fun k => ?_
      have := hn_lt (k + 1)
      rwa [hst_succ] at this
    -- Later points avoid earlier supports; in particular the points are distinct.
    have hxnot : ∀ j k, k < j → x j ∉ F (n k) := fun j k hkj hx => hxT j (hFsub k j hkj hx)
    have hxinj : Function.Injective x := by
      intro i j hij
      by_contra hne'
      rcases lt_or_gt_of_ne hne' with h | h
      · exact hxnot j i h (hij ▸ hxF i)
      · exact hxnot i j h (hij.symm ▸ hxF j)
    -- Include `x k` exactly when the earlier included points contribute zero.
    let partialSum : Finset ℕ → ℕ → k := fun K k =>
      ∑ j ∈ K.filter (fun j => x j ∈ F (n k)), c (n k) (x j)
    let Kst : ℕ → Finset ℕ := fun k => Nat.rec ∅
      (fun k K => if partialSum K k = 0 then insert k K else K) k
    have hK_succ : ∀ k, Kst (k + 1) =
        if partialSum (Kst k) k = 0 then insert k (Kst k) else Kst k := fun k => rfl
    have hK_range : ∀ k, Kst k ⊆ range k := by
      intro k
      induction k with
      | zero => exact Finset.empty_subset _
      | succ k ih =>
        rw [hK_succ]
        split_ifs
        · exact Finset.insert_subset (Finset.mem_range.mpr (Nat.lt_succ_self k))
            (ih.trans (Finset.range_subset_range.mpr (Nat.le_succ k)))
        · exact ih.trans (Finset.range_subset_range.mpr (Nat.le_succ k))
    have hK_stable : ∀ j k, j < k → (j ∈ Kst k ↔ j ∈ Kst (j + 1)) := by
      intro j k hjk
      induction k, hjk using Nat.le_induction with
      | base => exact Iff.rfl
      | succ m hm ih =>
        rw [← ih, hK_succ]
        split_ifs
        · rw [Finset.mem_insert]
          exact ⟨fun h => h.resolve_left (by omega), Or.inr⟩
        · exact Iff.rfl
    let A : Set X := x '' {j | j ∈ Kst (j + 1)}
    refine ⟨A, ?_, (Set.infinite_range_of_injective hn_strict.injective).mono ?_⟩
    · rintro _ ⟨j, -, rfl⟩
      exact Set.mem_iUnion.mpr ⟨n j, hxF j⟩
    · rintro _ ⟨k, rfl⟩
      show supportedSum (F (n k)) (c (n k)) A ≠ 0
      -- The chosen points in `F (n k)` are exactly those decided by stage `k + 1`.
      have hfilter : (F (n k)).filter (· ∈ A) =
          ((Kst (k + 1)).filter fun j => x j ∈ F (n k)).image x := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_image, A, Set.mem_image, Set.mem_setOf_eq]
        constructor
        · rintro ⟨hyF, j, hj, rfl⟩
          have hjk : j ≤ k := by
            by_contra h
            exact hxnot j k (by omega) hyF
          refine ⟨j, ⟨?_, hyF⟩, rfl⟩
          rcases hjk.lt_or_eq with h | rfl
          · exact (hK_stable j (k + 1) (by omega)).mpr hj
          · exact hj
        · rintro ⟨j, ⟨hj, hjF⟩, rfl⟩
          refine ⟨hjF, j, ?_, rfl⟩
          have hjk : j < k + 1 := Finset.mem_range.mp (hK_range _ hj)
          rcases (Nat.lt_succ_iff.mp hjk).lt_or_eq with h | rfl
          · exact (hK_stable j (k + 1) (by omega)).mp hj
          · exact hj
      rw [supportedSum, hfilter, Finset.sum_image fun i _ j _ h => hxinj h, hK_succ]
      have hk_notin : k ∉ Kst k := fun h => by simpa using hK_range k h
      split_ifs with hzero
      · rw [Finset.filter_insert, if_pos (hxF k), Finset.sum_insert
          (fun h => hk_notin (Finset.mem_filter.mp h).1)]
        change c (n k) (x k) + partialSum (Kst k) k ≠ 0
        rw [hzero, add_zero]
        exact hxc k
      · exact hzero

end

end Surreal.Selection
