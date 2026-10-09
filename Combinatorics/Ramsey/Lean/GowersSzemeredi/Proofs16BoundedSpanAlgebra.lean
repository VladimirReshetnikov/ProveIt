import GowersSzemeredi.Proofs16BohrSumUniformParameters

/-! Algebra of bounded frequency spans for the row selection argument. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Express bounded-span membership using coefficients on the ambient group. -/
theorem mem_boundedFrequencySpan_iff {N : Nat} [NeZero N]
    (K : Finset (ZMod N)) (R : Nat) (x : ZMod N) :
    x ∈ boundedFrequencySpan (fun k : K => (k : ZMod N)) R ↔
      ∃ f : ZMod N → ZMod N, (∀ k ∈ K, centeredAbs (f k) ≤ R) ∧
        x = ∑ k ∈ K, f k * k := by
  classical
  constructor
  · intro hx
    obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hx
    let f : ZMod N → ZMod N := fun k => if hk : k ∈ K then (v ⟨k, hk⟩ : ZMod N) else 0
    refine ⟨f, ?_, ?_⟩
    · intro k hk
      simp only [f, dif_pos hk]
      exact (Finset.mem_filter.mp (v ⟨k, hk⟩).property).2
    · rw [← heq]
      conv_rhs => rw [← Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro k hk
      simp [f, k.property]
  · rintro ⟨f, hf, rfl⟩
    let v : K → centeredBall N R := fun k => ⟨f k, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hf k k.property⟩⟩
    unfold boundedFrequencySpan
    apply Finset.mem_image.mpr
    refine ⟨v, ?_, ?_⟩
    · simp only [Finset.mem_univ]
    · exact Finset.sum_coe_sort K (fun k => f k * k)

/-- Bounded frequency spans are symmetric. -/
theorem neg_mem_boundedFrequencySpan {N : Nat} [NeZero N]
    (K : Finset (ZMod N)) (R : Nat) {x : ZMod N}
    (hx : x ∈ boundedFrequencySpan (fun k : K => (k : ZMod N)) R) :
    -x ∈ boundedFrequencySpan (fun k : K => (k : ZMod N)) R := by
  obtain ⟨f, hf, rfl⟩ := (mem_boundedFrequencySpan_iff K R x).mp hx
  apply (mem_boundedFrequencySpan_iff K R _).mpr
  refine ⟨fun k => -f k, fun k hk => ?_, ?_⟩
  · simpa only [centeredAbs_neg] using hf k hk
  · simp only [neg_mul, Finset.sum_neg_distrib]

/-- A span of a union splits as a difference of the individual spans,
without increasing the coefficient cutoff even when the sets overlap. -/
theorem boundedFrequencySpan_union_difference {N : Nat} [NeZero N]
    (K L : Finset (ZMod N)) (R : Nat) {x : ZMod N}
    (hx : x ∈ boundedFrequencySpan (fun k : ↥(K ∪ L) => (k : ZMod N)) R) :
    ∃ u ∈ boundedFrequencySpan (fun k : K => (k : ZMod N)) R,
      ∃ v ∈ boundedFrequencySpan (fun l : L => (l : ZMod N)) R, x = u - v := by
  obtain ⟨f, hf, rfl⟩ := (mem_boundedFrequencySpan_iff (K ∪ L) R x).mp hx
  let g : ZMod N → ZMod N := fun l => if l ∈ K then 0 else -f l
  refine ⟨∑ k ∈ K, f k * k, ?_, ∑ l ∈ L, g l * l, ?_, ?_⟩
  · exact (mem_boundedFrequencySpan_iff K R _).mpr
      ⟨f, fun k hk => hf k (Finset.mem_union_left _ hk), rfl⟩
  · apply (mem_boundedFrequencySpan_iff L R _).mpr
    refine ⟨g, fun l hl => ?_, rfl⟩
    by_cases hk : l ∈ K
    · simp [g, hk, centeredAbs]
    · simpa only [g, if_neg hk, centeredAbs_neg] using hf l (Finset.mem_union_right _ hl)
  · have hgsum : (∑ l ∈ L, g l * l) = -(∑ l ∈ L \ K, f l * l) := by
      rw [← Finset.sum_neg_distrib]
      simp only [g, ite_mul, zero_mul, neg_mul]
      rw [Finset.sdiff_eq_filter]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro l hl
      by_cases hk : l ∈ K <;> simp [hk]
    rw [hgsum, sub_neg_eq_add]
    have hdisj : Disjoint K (L \ K) := Finset.disjoint_left.mpr
      (fun k hk hk' => (Finset.mem_sdiff.mp hk').2 hk)
    have hsplit := Finset.sum_union hdisj (f := fun k => f k * k)
    simpa only [Finset.union_sdiff_self_eq_union] using hsplit

end LeanProofs.GowersSzemeredi
