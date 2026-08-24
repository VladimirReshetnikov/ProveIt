import Sharma2012.OppositeClassConsequences

/-!
# Hypothesis-minimal interleaving-class bounds

The class-counting argument does not require the two prescribed traces to
come with a separately chosen `Theta₁₂` word.  If the class is nonempty, one
of its members supplies such a word; if it is empty, every cardinality bound
is immediate.  This observation makes the binomial upper bound available for
arbitrary trace pairs.

We also separate Sharma's small finite optimization from the geometric
end-block arguments.  The resulting class-size theorem needs only the four
length implications actually used in the optimization, rather than the
paper's standing endpoint and commutation hypotheses.
-/

set_option autoImplicit false

open Finset

namespace LeanProofs.Sharma2012

/-- Every odd/even trace pair has the usual binomial upper bound, without a
representability hypothesis.  A nonempty class provides its own `Theta₁₂`
representative, while an unrepresentable trace pair defines the empty class.
-/
theorem interleavingClass_card_le_choose_general
    (n : Nat) (gammaOdd gammaEven : List Nat) :
    (interleavingClass n gammaOdd gammaEven).card ≤
      Nat.choose
        ((epilogue n gammaOdd).length + (prologue n gammaEven).length)
        (prologue n gammaEven).length := by
  classical
  by_cases hempty : interleavingClass n gammaOdd gammaEven = ∅
  · simp [hempty]
  · obtain ⟨sigma, hsigma⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hsigmaData : IsTheta12 n (permutationWord sigma) ∧
        oddTrace (permutationWord sigma) = gammaOdd ∧
        evenTrace (permutationWord sigma) = gammaEven := by
      simpa [interleavingClass] using hsigma
    have hbound := any_interleavingClass_card_le_choose hsigmaData.1
    simpa only [hsigmaData.2.1, hsigmaData.2.2] using hbound

/-- The finite numerical core of Sharma's twenty-element bound.  The
constant is sharp: the admissible pair `u = v = 3` gives `choose 6 3 = 20`.
-/
theorem choose_le_twenty_of_sharma_endblock_constraints
    {u v : Nat} (hu : u ≤ 19) (hv : v ≤ 19)
    (hfour : (4 ≤ u → v ≤ 2) ∧ (4 ≤ v → u ≤ 2))
    (hfive : (5 ≤ u → v ≤ 1) ∧ (5 ≤ v → u ≤ 1)) :
    Nat.choose (u + v) v ≤ 20 := by
  by_cases huFive : 5 ≤ u
  · have hvOne : v ≤ 1 := hfive.1 huFive
    interval_cases v
    · simp
    · simp only [Nat.choose_one_right]
      omega
  · by_cases hvFive : 5 ≤ v
    · have huOne : u ≤ 1 := hfive.2 hvFive
      interval_cases u
      · simp
      · simpa only [Nat.add_comm, Nat.choose_succ_self_right] using
          (show v + 1 ≤ 20 by omega)
    · have hsum : u + v ≤ 6 := by
        by_cases huFour : 4 ≤ u
        · have hvTwo : v ≤ 2 := hfour.1 huFour
          omega
        · by_cases hvFour : 4 ≤ v
          · have huTwo : u ≤ 2 := hfour.2 hvFour
            omega
          · omega
      calc
        Nat.choose (u + v) v ≤ Nat.choose 6 v :=
          Nat.choose_le_choose v hsum
        _ ≤ Nat.choose 6 (6 / 2) := Nat.choose_le_middle v 6
        _ = 20 := by norm_num [Nat.choose]

/-- Equality in the twenty-element numerical bound occurs exactly at the
balanced active blocks `(3, 3)` or at one of the two extreme pairs `(19, 1)`
and `(1, 19)`.  The equality itself forces the relevant length caps, so the
classification needs only the `length ≥ 5` implications; both the explicit
caps and the stronger `length ≥ 4` implications used for the upper bound are
unnecessary here. -/
theorem choose_eq_twenty_iff_of_sharma_large_endblock_constraints
    {u v : Nat} (hfive : (5 ≤ u → v ≤ 1) ∧ (5 ≤ v → u ≤ 1)) :
    Nat.choose (u + v) v = 20 ↔
      (u = 3 ∧ v = 3) ∨ (u = 19 ∧ v = 1) ∨ (u = 1 ∧ v = 19) := by
  constructor
  · intro hchoose
    by_cases huFive : 5 ≤ u
    · have hvOne : v ≤ 1 := hfive.1 huFive
      interval_cases v
      · norm_num at hchoose
      · simp only [Nat.choose_one_right] at hchoose
        exact Or.inr (Or.inl ⟨by omega, rfl⟩)
    · by_cases hvFive : 5 ≤ v
      · have huOne : u ≤ 1 := hfive.2 hvFive
        interval_cases u
        · norm_num at hchoose
        · have hchoose' : v + 1 = 20 := by
            simpa only [Nat.add_comm, Nat.choose_succ_self_right] using hchoose
          exact Or.inr (Or.inr ⟨rfl, by omega⟩)
      · have huFour : u ≤ 4 := by omega
        have hvFour : v ≤ 4 := by omega
        interval_cases u <;> interval_cases v
        all_goals norm_num [Nat.choose] at hchoose
        all_goals simp
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      norm_num [Nat.choose]

/-- The numerical bound is optimal under the weakened end-block constraints:
the pair `(3, 3)` satisfies them and has exactly twenty interleavings. -/
theorem sharma_endblock_constraints_twenty_is_sharp :
    ∃ u v : Nat,
      u ≤ 19 ∧ v ≤ 19 ∧
        ((4 ≤ u → v ≤ 2) ∧ (4 ≤ v → u ≤ 2)) ∧
        ((5 ≤ u → v ≤ 1) ∧ (5 ≤ v → u ≤ 1)) ∧
        Nat.choose (u + v) v = 20 := by
  refine ⟨3, 3, by norm_num, by norm_num, ?_, ?_, by norm_num [Nat.choose]⟩
  · omega
  · omega

/-- The ambient length cap `19` in the numerical theorem cannot be raised to
`20` without another hypothesis: `(u, v) = (20, 1)` satisfies all four
end-block implications but has twenty-one interleavings. -/
theorem sharma_endblock_length_cap_nineteen_is_sharp :
    ∃ u v : Nat,
      u ≤ 20 ∧ v ≤ 20 ∧
        ((4 ≤ u → v ≤ 2) ∧ (4 ≤ v → u ≤ 2)) ∧
        ((5 ≤ u → v ≤ 1) ∧ (5 ≤ v → u ≤ 1)) ∧
        Nat.choose (u + v) v = 21 := by
  refine ⟨20, 1, by norm_num, by norm_num, ?_, ?_, by norm_num⟩
  · omega
  · omega

/-- An arbitrary trace pair has at most twenty realizations as soon as its
active end-block lengths satisfy Sharma's four implication constraints.  No
explicit length cap is needed: a member of a nonempty class supplies an
`IsTheta₁₂` word, whose odd epilogue and even prologue both have length at
most six; an empty class is trivial.  In particular, no endpoint witnesses,
commutation orientation, or ambient representative is required from callers.
-/
theorem interleavingClass_card_le_twenty_of_endblock_constraints
    {n : Nat} {gammaOdd gammaEven : List Nat}
    (hfour :
      (4 ≤ (epilogue n gammaOdd).length →
          (prologue n gammaEven).length ≤ 2) ∧
        (4 ≤ (prologue n gammaEven).length →
          (epilogue n gammaOdd).length ≤ 2))
    (hfive :
      (5 ≤ (epilogue n gammaOdd).length →
          (prologue n gammaEven).length ≤ 1) ∧
        (5 ≤ (prologue n gammaEven).length →
          (epilogue n gammaOdd).length ≤ 1)) :
    (interleavingClass n gammaOdd gammaEven).card ≤ 20 := by
  classical
  by_cases hempty : interleavingClass n gammaOdd gammaEven = ∅
  · simp [hempty]
  · obtain ⟨sigma, hsigma⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hsigmaData : IsTheta12 n (permutationWord sigma) ∧
        oddTrace (permutationWord sigma) = gammaOdd ∧
        evenTrace (permutationWord sigma) = gammaEven := by
      simpa [interleavingClass] using hsigma
    have huSix : (epilogue n gammaOdd).length ≤ 6 := by
      simpa only [hsigmaData.2.1] using
        epilogue_oddTrace_length_le_six hsigmaData.1.1
    have hvSix : (prologue n gammaEven).length ≤ 6 := by
      simpa only [hsigmaData.2.2] using
        prologue_evenTrace_length_le_six hsigmaData.1.1
    exact (interleavingClass_card_le_choose_general n gammaOdd gammaEven).trans
      (choose_le_twenty_of_sharma_endblock_constraints
        (huSix.trans (by norm_num)) (hvSix.trans (by norm_num)) hfour hfive)

end LeanProofs.Sharma2012
