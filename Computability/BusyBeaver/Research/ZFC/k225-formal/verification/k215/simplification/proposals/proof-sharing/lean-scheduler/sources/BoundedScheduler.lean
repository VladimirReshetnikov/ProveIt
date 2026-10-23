import CofinalScheduler

/-!
Bounded refinement of the repository's Source194 scheduler.

This module is an optional quantitative extension. It does not replace the
more general lexicographic theorem: that theorem permits unbounded refill
sizes. Here `refill` records the extra bound already supplied by K215's
`decode_le`. The endpoint simplification is adoption of Source194; the
additional theorem gives an explicit successful-prefix bound.
-/

namespace SetTheory.BusyBeaver.ZFC.BoundedScheduler

universe u

/-- Sum of the positive integers through n. -/
def triangle : Nat → Nat
  | 0 => 0
  | n + 1 => triangle n + (n + 1)

theorem triangle_mono {a b : Nat} (h : a ≤ b) : triangle a ≤ triangle b := by
  induction b with
  | zero =>
      have ha : a = 0 := by omega
      subst a
      exact Nat.le_refl _
  | succ b ih =>
      by_cases hab : a ≤ b
      · have ht := ih hab
        simp only [triangle]
        omega
      · have ha : a = b + 1 := by omega
        subst a
        exact Nat.le_refl _

/-- The successful-prefix budget to the boundary for `target`. -/
def potential {S : Type u} (pending index : S → Nat) (target : Nat) (s : S) : Nat :=
  triangle target - triangle (index s) + pending s

open CofinalScheduler

section

variable {S : Type u} (M : Dynamics S) {pending index : S → Nat}
  (L : M.Laws pending index)
  (refill : ∀ s t, M.step s = some t → pending s = 0 → pending t ≤ index s)

include L refill

/-- Until the requested boundary, every successful step spends at least one
    unit of budget and never skips the target index. -/
theorem potential_step (target : Nat) (s t : S)
    (hle : index s ≤ target) (hnot : ¬(pending s = 0 ∧ index s = target))
    (hs : M.step s = some t) :
    index t ≤ target ∧ potential pending index target t < potential pending index target s := by
  by_cases hp : pending s = 0
  · have hi := L.advance s t hs hp
    have hb := refill s t hs hp
    have hlt : index s < target := by omega
    have hbound := triangle_mono (show index s + 1 ≤ target by omega)
    simp only [triangle] at hbound
    constructor
    · omega
    · simp only [potential, hi, triangle, hp]
      omega
  · obtain ⟨hd, hi⟩ := L.descend s t hs hp
    constructor
    · omega
    · simp only [potential, hi]
      omega

/-- Within the budget, a successful finite prefix reaches either a state
    whose next step halts or the target boundary. The halting step itself is
    not included in n. No invariant on the working payload is assumed. -/
theorem find_bounded (target : Nat) (s : S) (hle : index s ≤ target) :
    ∃ n t, n ≤ potential pending index target s ∧ M.run n s = some t ∧
      (M.step t = none ∨ pending t = 0 ∧ index t = target) := by
  by_cases htarget : pending s = 0 ∧ index s = target
  · exact ⟨0, s, Nat.zero_le _, M.zero s, Or.inr htarget⟩
  · cases hs : M.step s with
    | none => exact ⟨0, s, Nat.zero_le _, M.zero s, Or.inl hs⟩
    | some t =>
        obtain ⟨hle', hd⟩ := potential_step M L refill target s t hle htarget hs
        obtain ⟨n, v, hn, hr, hv⟩ := find_bounded target t hle'
        exact ⟨n + 1, v, by omega, M.prepend hs hr, hv⟩
termination_by potential pending index target s
decreasing_by exact hd

end

#print axioms triangle_mono
#print axioms potential_step
#print axioms find_bounded

end SetTheory.BusyBeaver.ZFC.BoundedScheduler
