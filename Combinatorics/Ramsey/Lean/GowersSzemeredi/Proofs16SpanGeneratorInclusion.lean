import GowersSzemeredi.Proofs16SpanSumCounting

/-! Increasing a generator set preserves bounded-span membership.
Combining two column spans adds their coefficient cutoffs. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem boundedFrequencySpan_mono_generators {N : Nat} [NeZero N]
    (K L : Finset (ZMod N)) (R : Nat) (hKL : K ⊆ L) :
    boundedFrequencySpan (fun k : K => (k : ZMod N)) R ⊆
      boundedFrequencySpan (fun k : L => (k : ZMod N)) R := by
  intro x hx
  obtain ⟨f,hf,hx⟩ := (mem_boundedFrequencySpan_iff K R x).mp hx
  let g (k : ZMod N) := if k ∈ K then f k else 0
  apply (mem_boundedFrequencySpan_iff L R x).mpr
  refine ⟨g,?_,hx.trans ?_⟩
  · intro k hk
    by_cases h : k ∈ K
    · simpa only [g,if_pos h] using hf k h
    · simp [g,h,centeredAbs]
  · calc (∑ k ∈ K, f k*k) = ∑ k ∈ K, g k*k := by
           apply Finset.sum_congr rfl
           intro k hk
           simp only [g,if_pos hk]
      _ = ∑ k ∈ L, g k*k := Finset.sum_subset hKL (fun k _ hk => by simp [g,hk])

theorem sub_mem_union_boundedFrequencySpan {N : Nat} [NeZero N]
    (K L : Finset (ZMod N)) (R S : Nat) {x y : ZMod N}
    (hx : x ∈ boundedFrequencySpan (fun k : K => (k : ZMod N)) R)
    (hy : y ∈ boundedFrequencySpan (fun k : L => (k : ZMod N)) S) :
    x-y ∈ boundedFrequencySpan (fun k : ↥(K ∪ L) => (k : ZMod N)) (R+S) := by
  have hx' := boundedFrequencySpan_mono_generators K (K ∪ L) R Finset.subset_union_left hx
  have hy' := boundedFrequencySpan_mono_generators L (K ∪ L) S Finset.subset_union_right hy
  simpa only [sub_eq_add_neg] using add_mem_boundedFrequencySpan (K ∪ L) R S hx'
    (neg_mem_boundedFrequencySpan (K ∪ L) S hy')

end LeanProofs.GowersSzemeredi
