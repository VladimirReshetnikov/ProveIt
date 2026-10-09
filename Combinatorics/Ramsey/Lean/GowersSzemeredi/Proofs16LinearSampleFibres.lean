import GowersSzemeredi.Definitions

/-! A nonzero linear combination of independent samples in a prime cyclic
group has at most `|Z|*N^(r-1)` samples landing in a prescribed set `Z`.
The count is proved by recovering one coordinate from the others. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def linearSampleValue {N r : Nat} (c e : Fin r → ZMod N) : ZMod N := ∑ i, c i * e i

theorem linear_sample_preimage_card_le {N r : Nat} [NeZero N] [Fact N.Prime]
    (c : Fin r → ZMod N) (j : Fin r) (hc : c j ≠ 0) (Z : Finset (ZMod N)) :
    (Finset.univ.filter fun e : Fin r → ZMod N => linearSampleValue c e ∈ Z).card ≤
      Z.card*N^(r-1) := by
  let J := {i : Fin r // i ≠ j}
  let P : Finset (ZMod N × (J → ZMod N)) := Z ×ˢ Finset.univ
  have hcardJ : Fintype.card J = r-1 := by
    rw [Fintype.card_subtype]
    have he : (Finset.univ.filter fun i : Fin r => i ≠ j) = Finset.univ.erase j := by
      ext i
      simp [eq_comm]
    rw [he, Finset.card_erase_of_mem (Finset.mem_univ j)]
    simp
  have hcount := Finset.card_le_card_of_injOn
    (s := Finset.univ.filter fun e : Fin r → ZMod N => linearSampleValue c e ∈ Z)
    (t := P) (fun e => (linearSampleValue c e, fun i : J => e i))
    (by intro e he; exact Finset.mem_product.mpr ⟨(Finset.mem_filter.mp he).2, Finset.mem_univ _⟩)
    (by
      intro e he f hf hpair
      have hvalue := congrArg Prod.fst hpair
      have hrest : ∀ i : Fin r, i ≠ j → e i = f i := by
        intro i hi
        exact congrFun (congrArg Prod.snd hpair) ⟨i, hi⟩
      have hsum : ∑ i ∈ Finset.univ.erase j, c i*e i =
          ∑ i ∈ Finset.univ.erase j, c i*f i := by
        exact Finset.sum_congr rfl fun i hi => congrArg (fun z => c i*z)
          (hrest i (Finset.mem_erase.mp hi).1)
      have heq : c j*e j = c j*f j := by
        change (∑ i, c i*e i) = (∑ i, c i*f i) at hvalue
        rw [←Finset.add_sum_erase Finset.univ (fun i => c i*e i) (Finset.mem_univ j),
          ←Finset.add_sum_erase Finset.univ (fun i => c i*f i) (Finset.mem_univ j), hsum] at hvalue
        exact add_right_cancel hvalue
      have hj := mul_left_cancel₀ hc heq
      funext i
      by_cases hi : i = j
      · simpa [hi] using hj
      · exact hrest i hi)
  simpa only [P, Finset.card_product, Finset.card_univ, Fintype.card_fun, ZMod.card, hcardJ] using hcount

/-- A union over nonzero coefficient vectors costs only their number. -/
theorem linear_samples_union_card_le {N r : Nat} [NeZero N] [Fact N.Prime]
    (C : Finset (Fin r → ZMod N)) (Z : Finset (ZMod N))
    (hC : ∀ c ∈ C, ∃ j, c j ≠ 0) :
    (Finset.univ.filter fun e : Fin r → ZMod N =>
      ∃ c ∈ C, linearSampleValue c e ∈ Z).card ≤ C.card*Z.card*N^(r-1) := by
  have hsub : (Finset.univ.filter fun e : Fin r → ZMod N =>
      ∃ c ∈ C, linearSampleValue c e ∈ Z) ⊆
      C.biUnion (fun c => Finset.univ.filter fun e : Fin r → ZMod N => linearSampleValue c e ∈ Z) := by
    intro e he
    obtain ⟨c, hc, hce⟩ := (Finset.mem_filter.mp he).2
    exact Finset.mem_biUnion.mpr ⟨c, hc, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hce⟩⟩
  calc _ ≤ ∑ c ∈ C, (Finset.univ.filter fun e : Fin r → ZMod N => linearSampleValue c e ∈ Z).card :=
      (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ ≤ ∑ _c ∈ C, Z.card*N^(r-1) := Finset.sum_le_sum fun c hc => by
      obtain ⟨j, hj⟩ := hC c hc
      exact linear_sample_preimage_card_le c j hj Z
    _ = _ := by simp [Nat.mul_assoc]

end LeanProofs.GowersSzemeredi
