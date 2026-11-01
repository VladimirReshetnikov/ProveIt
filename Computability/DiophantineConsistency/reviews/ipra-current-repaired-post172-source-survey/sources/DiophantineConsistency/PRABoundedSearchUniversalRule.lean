import DiophantineConsistency.PRABoundedSearchMinimal

/-! The universal search conditions imply the Boolean induction rule. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRABoundedSearchUniversalRule

/-- The two search conditions, Boolean range and successor exhaustion imply
induction for the represented predicate. This purely logical lemma does not
assume the candidate PRA theory or an induction principle on the carrier. -/
theorem inductionFromSearch {M : Type} (zero one : M) (succ pred good find : M → M)
    (hOneNeZero : one ≠ zero)
    (hExhaustion : ∀ x, x = zero ∨ succ (pred x) = x)
    (hBit : ∀ x, good x = zero ∨ good x = one)
    (hCandidate : ∀ x, good (find x) = zero ∨ find x = x)
    (hMinimal : ∀ x, find x = zero ∨ good (pred (find x)) ≠ zero)
    (hBase : good zero = one)
    (hStep : ∀ x, good x = one → good (succ x) = one) :
    ∀ x, good x = one := by
  intro x
  by_contra hnot
  have hbad : good x = zero := (hBit x).resolve_right hnot
  have hfound : good (find x) = zero := by
    rcases hCandidate x with h | h
    · exact h
    · rw [h]
      exact hbad
  rcases hMinimal x with hzero | hprev
  · rw [hzero, hBase] at hfound
    exact hOneNeZero hfound
  · have hnonzero : find x ≠ zero := by
      intro hzero
      rw [hzero, hBase] at hfound
      exact hOneNeZero hfound
    have hsucc := (hExhaustion (find x)).resolve_left hnonzero
    have hgoodPrev := (hBit (pred (find x))).resolve_left hprev
    have hgood := hStep _ hgoodPrev
    rw [hsucc] at hgood
    exact hOneNeZero (hgood.symm.trans hfound)

end DiophantineConsistency.PRABoundedSearchUniversalRule
