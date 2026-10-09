import GowersSzemeredi.Proofs16SpanFiniteUnion

/-! A common span of eight columns splits into four endpoint differences
with the original coefficient cutoff, including when columns overlap. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def eightFrequencyUnion {N : Nat} (K : Fin 8 → Finset (ZMod N)) : Finset (ZMod N) :=
  Finset.univ.biUnion K

def fourPairDifferenceSum {N : Nat} (v : Fin 8 → ZMod N) : ZMod N :=
  (v 0-v 1)+(v 2-v 3)+(v 4-v 5)+(v 6-v 7)

theorem eightFrequencyUnion_card_le {N d : Nat} (K : Fin 8 → Finset (ZMod N))
    (hK : ∀ i, (K i).card ≤ d) : (eightFrequencyUnion K).card ≤ 8*d := by
  calc (eightFrequencyUnion K).card ≤ ∑ i, (K i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin 8, d := Finset.sum_le_sum (fun i _ => hK i)
    _ = 8*d := by simp

theorem boundedFrequencySpan_eight_union_differences {N : Nat} [NeZero N]
    (K : Fin 8 → Finset (ZMod N)) (R : Nat) {q : ZMod N}
    (hq : q ∈ boundedFrequencySpan (fun k : eightFrequencyUnion K => (k : ZMod N)) R) :
    ∃ v : Fin 8 → ZMod N,
      (∀ i, v i ∈ boundedFrequencySpan (fun k : K i => (k : ZMod N)) R) ∧
      q = fourPairDifferenceSum v := by
  obtain ⟨w,hw,hq⟩ := boundedFrequencySpan_biUnion_sum Finset.univ K R hq
  have hw' (i : Fin 8) := hw i (Finset.mem_univ _)
  refine ⟨![w 0,-w 1,w 2,-w 3,w 4,-w 5,w 6,-w 7],?_,?_⟩
  · intro i
    fin_cases i
    · exact hw' 0
    · exact neg_mem_boundedFrequencySpan (K 1) R (hw' 1)
    · exact hw' 2
    · exact neg_mem_boundedFrequencySpan (K 3) R (hw' 3)
    · exact hw' 4
    · exact neg_mem_boundedFrequencySpan (K 5) R (hw' 5)
    · exact hw' 6
    · exact neg_mem_boundedFrequencySpan (K 7) R (hw' 7)
  · dsimp [fourPairDifferenceSum]
    norm_num [Fin.sum_univ_succ,Fin.succ,add_assoc] at hq
    simp only [sub_neg_eq_add,add_assoc]
    exact hq

end LeanProofs.GowersSzemeredi
