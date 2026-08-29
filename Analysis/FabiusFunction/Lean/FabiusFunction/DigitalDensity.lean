import FabiusFunction.ThueMorseLucasSupport

/-!
# The digital density of a submask condition

The exponent-sequence volume's sparse-Prouhet corollary rests on a
counting statement: among a full dyadic block, the naturals whose
binary expansion contains a fixed mask `d` have density `2^{-s₂(d)}`.
Equivalently, for `d < 2^m`,

`#{n < 2^m | bitSupport d ⊆ bitSupport n} = 2^{m - w(d)}`.

Through the corpus's dyadic-code dictionary this is a statement about
subsets: the subsets of `range m` containing a fixed `S` are exactly
the subsets of `range m \ S` with `S` adjoined, so there are
`2^{m - |S|}` of them.  Mathlib has the *graded* form of that
bijection (`Finset.filter_powersetCard_subset`) but not the ungraded
one, so it is proved here — it is shorter than the graded version,
having no cardinality bookkeeping.

Combined with the corpus's Lucas criterion
`odd_choose_iff_bitSupport_subset`, the count is the density of the
odd binomial coefficients in a row block.

* `filter_powerset_subset` — the ungraded superset bijection;
* `card_filter_powerset_subset` — its cardinality, `2^{|t| - |s|}`;
* `card_filter_bitSupport_subset` — **the digital density**;
* `card_filter_odd_choose` — the Lucas reading.
-/

set_option autoImplicit false

open Finset

namespace Fabius

variable {α : Type*} [DecidableEq α]

/-- **The subsets of `t` containing `s`** are the subsets of `t \ s`
with `s` adjoined.  This is the ungraded companion of Mathlib's
`Finset.filter_powersetCard_subset`. -/
theorem filter_powerset_subset {s t : Finset α} (hst : s ⊆ t) :
    t.powerset.filter (s ⊆ ·) = (t \ s).powerset.image (· ∪ s) := by
  ext x
  simp only [mem_filter, mem_powerset, mem_image]
  constructor
  · rintro ⟨hxt, hsx⟩
    refine ⟨x \ s, ?_, sdiff_union_of_subset hsx⟩
    intro y hy
    rw [mem_sdiff] at hy ⊢
    exact ⟨hxt hy.1, hy.2⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨union_subset (hy.trans sdiff_subset) hst,
      subset_union_right⟩

/-- The count: there are `2 ^ (|t| - |s|)` subsets of `t` containing
`s`. -/
theorem card_filter_powerset_subset {s t : Finset α} (hst : s ⊆ t) :
    #(t.powerset.filter (s ⊆ ·)) = 2 ^ (#t - #s) := by
  have hinj : Set.InjOn (· ∪ s) ((t \ s).powerset : Set (Finset α)) := by
    intro u hu v hv huv
    rw [mem_coe, mem_powerset] at hu hv
    have hdu : Disjoint u s :=
      Finset.disjoint_of_subset_left hu disjoint_sdiff_self_left
    have hdv : Disjoint v s :=
      Finset.disjoint_of_subset_left hv disjoint_sdiff_self_left
    have h : (u ∪ s) \ s = (v ∪ s) \ s := by rw [huv]
    rwa [Finset.union_sdiff_cancel_right hdu,
      Finset.union_sdiff_cancel_right hdv] at h
  rw [filter_powerset_subset hst, Finset.card_image_of_injOn hinj,
    Finset.card_powerset, Finset.card_sdiff_of_subset hst]

/-- **The digital density.**  Among the naturals below `2 ^ m`, those
whose binary expansion contains the mask of `d` number exactly
`2 ^ (m - w(d))` — a density of `2 ^ (-w(d))`. -/
theorem card_filter_bitSupport_subset (m : ℕ) {d : ℕ}
    (hd : d < 2 ^ m) :
    #({n ∈ range (2 ^ m) | bitSupport d ⊆ bitSupport n}) =
      2 ^ (m - binaryWeight d) := by
  classical
  have hsub : bitSupport d ⊆ range m :=
    (bitSupport_subset_range_iff_lt_two_pow d m).mpr hd
  have hcard : #({n ∈ range (2 ^ m) | bitSupport d ⊆ bitSupport n}) =
      ∑ n ∈ range (2 ^ m),
        if bitSupport d ⊆ bitSupport n then 1 else 0 :=
    Finset.card_filter _ _
  have hpow : (∑ n ∈ range (2 ^ m),
      if bitSupport d ⊆ bitSupport n then 1 else 0) =
      ∑ T ∈ (range m).powerset,
        if bitSupport d ⊆ T then 1 else 0 := by
    rw [← sum_powerset_two_pow m
      (fun n => if bitSupport d ⊆ bitSupport n then 1 else 0)]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [bitSupport_sum_two_pow]
  rw [hcard, hpow, ← Finset.card_filter,
    card_filter_powerset_subset hsub, Finset.card_range,
    card_bitSupport]

/-- The Lucas reading: the binomial coefficients `C(n, d)` that are
odd, for `n` in a full dyadic block, have the same count. -/
theorem card_filter_odd_choose (m : ℕ) {d : ℕ} (hd : d < 2 ^ m) :
    #({n ∈ range (2 ^ m) | Odd (n.choose d)}) =
      2 ^ (m - binaryWeight d) := by
  classical
  rw [← card_filter_bitSupport_subset m hd]
  congr 1
  exact Finset.filter_congr fun n _ =>
    odd_choose_iff_bitSupport_subset n d

end Fabius
