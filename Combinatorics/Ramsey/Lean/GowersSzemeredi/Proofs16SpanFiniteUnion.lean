import GowersSzemeredi.Proofs16SpanGeneratorInclusion

/-! Finite union spans split without enlarging the coefficient bound.
In the converse direction repeated generators can occur in several
summands, so the resulting cutoff includes the number of summands. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem boundedFrequencySpan_union_sum {N : Nat} [NeZero N]
    (K L : Finset (ZMod N)) (R : Nat) {x : ZMod N}
    (hx : x ∈ boundedFrequencySpan (fun k : ↥(K ∪ L) => (k : ZMod N)) R) :
    ∃ u ∈ boundedFrequencySpan (fun k : K => (k : ZMod N)) R,
      ∃ v ∈ boundedFrequencySpan (fun k : L => (k : ZMod N)) R, x = u+v := by
  obtain ⟨u,hu,v,hv,he⟩ := boundedFrequencySpan_union_difference K L R hx
  exact ⟨u,hu,-v,neg_mem_boundedFrequencySpan L R hv,by simpa only [sub_eq_add_neg] using he⟩

theorem boundedFrequencySpan_biUnion_sum {N : Nat} [NeZero N] {I : Type*}
    (S : Finset I) (T : I → Finset (ZMod N)) (R : Nat) {x : ZMod N}
    (hx : x ∈ boundedFrequencySpan (fun k : S.biUnion T => (k : ZMod N)) R) :
    ∃ v : I → ZMod N, (∀ i ∈ S, v i ∈ boundedFrequencySpan (fun k : T i => (k : ZMod N)) R) ∧
      x = ∑ i ∈ S, v i := by
  induction S using Finset.induction_on generalizing x with
  | empty =>
    simp only [Finset.biUnion_empty] at hx
    obtain ⟨v,_,hv⟩ := (mem_boundedFrequencySpan_iff ∅ R x).mp hx
    exact ⟨fun _ => 0,by simp,by simpa using hv⟩
  | @insert i S hi ih =>
    rw [Finset.biUnion_insert] at hx
    obtain ⟨u,hu,w,hw,huw⟩ := boundedFrequencySpan_union_sum (T i) (S.biUnion T) R hx
    obtain ⟨v,hv,hwv⟩ := ih hw
    refine ⟨Function.update v i u,?_,?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simpa only [Function.update_self] using hu
      · have hji : j ≠ i := fun h => hi (h ▸ hj)
        simpa only [Function.update_of_ne hji] using hv j hj
    · rw [Finset.sum_insert hi,Function.update_self]
      have he : (∑ j ∈ S, Function.update v i u j) = ∑ j ∈ S, v j := by
        apply Finset.sum_congr rfl
        intro j hj
        have hji : j ≠ i := fun h => hi (h ▸ hj)
        exact Function.update_of_ne hji u v
      rw [he,← hwv]
      exact huw

/-- The cutoff accounts for repeated frequencies across different sets. -/
theorem sum_mem_biUnion_boundedFrequencySpan {N : Nat} [NeZero N] {I : Type*}
    (S : Finset I) (T : I → Finset (ZMod N)) (R : Nat) (v : I → ZMod N)
    (hv : ∀ i ∈ S, v i ∈ boundedFrequencySpan (fun k : T i => (k : ZMod N)) R) :
    (∑ i ∈ S, v i) ∈ boundedFrequencySpan (fun k : S.biUnion T => (k : ZMod N)) (S.card*R) := by
  apply sum_mem_boundedFrequencySpan
  intro i hi
  exact boundedFrequencySpan_mono_generators (T i) (S.biUnion T) R
    (fun k hk => Finset.mem_biUnion.mpr ⟨i,hi,hk⟩) (hv i hi)

theorem exists_escape_of_sum_not_mem_biUnion_span {N : Nat} [NeZero N] {I : Type*}
    (S : Finset I) (T : I → Finset (ZMod N)) (R : Nat) (v : I → ZMod N)
    (h : (∑ i ∈ S, v i) ∉ boundedFrequencySpan (fun k : S.biUnion T => (k : ZMod N)) (S.card*R)) :
    ∃ i ∈ S, v i ∉ boundedFrequencySpan (fun k : T i => (k : ZMod N)) R := by
  by_contra hn
  push Not at hn
  exact h (sum_mem_biUnion_boundedFrequencySpan S T R v hn)

end LeanProofs.GowersSzemeredi
