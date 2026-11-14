import PA194OccurrenceCore

/-! Coverage extracted from a stable PA194 occurrence history. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA194OccurrenceCoverage
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194OccurrenceCore PA194PackedDescent
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

def occurrence (history : V → V) (n v : V) : Prop :=
  bitDef.val.Evalb ![pair n v,history (pair n v + 1)]

/-- A stable history satisfying its update equation has the exact decoder's
one-step occurrence coverage. All quantifiers include nonstandard elements. -/
theorem staged_coverage (history : V → V)
    (hrec : ∀ x, bitDef.val.Evalb ![x,history (x+1)] ↔
      occurrenceCore.val.Evalb ![x,history x])
    (hstable : ∀ t x, x < t →
      (bitDef.val.Evalb ![x,history t] ↔ bitDef.val.Evalb ![x,history (x+1)]))
    (n v : V) (h : occurrence history n v) :
    0 < n ∧ (v = first (n/4) ∨ v = second (n/4) ∨
      occurrence history (first (n/4)) v ∨ occurrence history (second (n/4)) v) := by
  have hh := (hrec (pair n v)).mp h
  rw [occurrenceCore_eval_rec] at hh
  simp only [coreRecMeaning, pi₁_pair, pi₂_pair] at hh
  obtain ⟨hn, hh⟩ := hh
  have hd := packed_children_lt n v hn
  refine ⟨hn, ?_⟩
  rcases hh with h0 | h1 | h2
  · rcases h0.2 with hfirst | hsecond
    · exact Or.inr (Or.inr (Or.inl ((hstable _ _ hd.1).mp hfirst)))
    · exact Or.inr (Or.inr (Or.inr ((hstable _ _ hd.2).mp hsecond)))
  · rcases h1.2 with hfirst | hsecond
    · exact Or.inl hfirst
    · exact Or.inr (Or.inl hsecond)
  · rcases h2.2 with hlabel | hchild
    · exact Or.inr (Or.inl hlabel)
    · exact Or.inr (Or.inr (Or.inl ((hstable _ _ hd.1).mp hchild)))
#print axioms staged_coverage
end PA194OccurrenceCoverage
