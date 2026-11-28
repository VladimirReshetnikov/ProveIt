import GRHArticle.ProgressionFree.GreedyLengthExponents
import GRHArticle.ProgressionFree.Rankin

/-!
# The three-term greedy rule is the ternary Rankin rule

A rejected ternary vector has a positive-step witness ending at it.
Replace each digit two by zero and one to obtain the first two members.
-/

namespace GRHArticle.ProgressionFree

/-- An exponent with a ternary digit two is the end of a strictly increasing
progression whose first two terms satisfy the Rankin condition. -/
theorem exists_threeAP_greedyExponents_of_notMem {n : ℕ} (hn : n ∉ greedyExponents) :
    ∃ a b : ℕ, a ∈ greedyExponents ∧ b ∈ greedyExponents ∧ a < b ∧ b < n ∧ a+n = b+b := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hpos : 0 < n := Nat.pos_of_ne_zero (fun h ↦ hn (h.symm ▸ zero_mem_greedyExponents))
    by_cases hq : n/3 ∈ greedyExponents
    · have hd : n % 3 = 2 := by
        by_contra h
        exact hn ((mem_greedyExponents_iff n).mpr ⟨by omega,hq⟩)
      refine ⟨3*(n/3),3*(n/3)+1,?_,?_,by omega,by omega,by omega⟩
      · rw [mem_greedyExponents_iff]
        exact ⟨by omega,by simpa using hq⟩
      · rw [mem_greedyExponents_iff]
        exact ⟨by omega,(show (3*(n/3)+1)/3 = n/3 by omega).symm ▸ hq⟩
    · obtain ⟨a,b,ha,hb,hab,hbn,he⟩ := ih (n/3) (by omega) hq
      by_cases hd : n % 3 = 2
      · refine ⟨3*a,3*b+1,?_,?_,by omega,by omega,by omega⟩
        · rw [mem_greedyExponents_iff]
          exact ⟨by omega,by simpa using ha⟩
        · rw [mem_greedyExponents_iff]
          exact ⟨by omega,(show (3*b+1)/3 = b by omega).symm ▸ hb⟩
      · have hd' : n % 3 ≤ 1 := by omega
        refine ⟨3*a+n%3,3*b+n%3,?_,?_,by omega,by omega,by omega⟩
        · rw [mem_greedyExponents_iff]
          refine ⟨by omega,?_⟩
          rwa [show (3*a+n%3)/3 = a by omega]
        · rw [mem_greedyExponents_iff]
          refine ⟨by omega,?_⟩
          rwa [show (3*b+n%3)/3 = b by omega]

/-- Specializing the abstract greedy rule at length three gives the ternary
digit rule defining Rankin's set. -/
theorem greedyLengthExponents_three_eq_greedyExponents :
    greedyLengthExponents 3 = greedyExponents := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    constructor
    · intro hg
      by_contra h
      obtain ⟨a,b,ha,hb,hab,hbn,he⟩ := exists_threeAP_greedyExponents_of_notMem h
      let d := n-b
      have hd : 0 < d := by omega
      apply (not_mem_greedyLengthExponents_iff (by decide : 2 ≤ 3)).mpr _ hg
      refine ⟨d,hd,by dsimp [d]; omega,?_⟩
      intro i hi
      have hi' : i = 0 ∨ i = 1 := by omega
      rcases hi' with rfl | rfl
      · have hA : n-(3-1-0)*d = a := by dsimp [d]; omega
        exact hA.symm ▸ (ih a (by omega)).mpr ha
      · have hB : n-(3-1-1)*d = b := by dsimp [d]; omega
        exact hB.symm ▸ (ih b hbn).mpr hb
    · intro h
      by_contra hg
      obtain ⟨d,hd,hdn,hprev⟩ := (not_mem_greedyLengthExponents_iff (by decide : 2 ≤ 3)).mp hg
      let a := n-2*d
      let b := n-d
      have ha : a ∈ greedyExponents := (ih a (by dsimp [a]; omega)).mp (hprev 0 (by decide))
      have hb : b ∈ greedyExponents := (ih b (by dsimp [b]; omega)).mp
        (by simpa only [b,Nat.reduceSub,Nat.one_mul] using hprev 1 (by decide))
      have he := threeAPFree_greedyExponents ha hb h (by dsimp [a,b]; omega)
      dsimp [a,b] at he
      omega

/-- The length-three greedy product, on actual positive integers, is Rankin's set. -/
theorem integerGreedyLengthSet_three_eq_rankinSet : integerGreedyLengthSet 3 = rankinSet := by
  simp only [integerGreedyLengthSet,integerIndependentExponentSet,rankinSet,
    greedyLengthExponents_three_eq_greedyExponents]

end GRHArticle.ProgressionFree
