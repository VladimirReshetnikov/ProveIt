import PA194IndexedNumerals

set_option autoImplicit false

namespace PA194IndexedRunRestriction
open ConPA.Machine (PackedConf)
open PA194BRows (Action)
open PA194IndexedNumerals (indexedNext indexedRunFrom)

/-- Record whether the run reads a row at one of the excluded controls. -/
def restrictedRun (rows : List Action) (excluded : List Nat)
    (initial : PackedConf) (steps : Nat) : Bool × PackedConf :=
  Nat.rec (true, initial)
    (fun _ prev => (prev.1 && !(excluded.contains prev.2.1), indexedNext rows prev.2))
    steps

theorem transfer (rows other : List Action) (excluded : List Nat)
    (agree : ∀ q b : Nat, q < 194 → b < 2 → excluded.contains q = false →
      rows.getD (2 * q + b) (0, 0, 194) = other.getD (2 * q + b) (0, 0, 194))
    (initial : PackedConf) (steps : Nat)
    (checked : (restrictedRun rows excluded initial steps).1 = true) :
    indexedRunFrom other initial steps = (restrictedRun rows excluded initial steps).2 := by
  induction steps with
  | zero => rfl
  | succ n ih =>
    let prev := restrictedRun rows excluded initial n
    change (prev.1 && !excluded.contains prev.2.1) = true at checked
    obtain ⟨past, current⟩ := Bool.and_eq_true_iff.mp checked
    have ok : excluded.contains prev.2.1 = false := by
      cases h : excluded.contains prev.2.1 <;> simp_all
    change indexedNext other (indexedRunFrom other initial n) = indexedNext rows prev.2
    rw [ih past]
    change indexedNext other prev.2 = indexedNext rows prev.2
    by_cases q : prev.2.1 < 194
    · have hrow := agree prev.2.1 (prev.2.2.2 % 2) q (Nat.mod_lt _ (by decide)) ok
      simp only [indexedNext, q, if_pos]
      rw [hrow]
    · simp [indexedNext, q]

theorem append (rows : List Action) (excluded : List Nat) (initial : PackedConf)
    (a b : Nat) (checked : (restrictedRun rows excluded initial a).1 = true) :
    restrictedRun rows excluded initial (a + b) =
      restrictedRun rows excluded (restrictedRun rows excluded initial a).2 b := by
  induction b with
  | zero =>
    change restrictedRun rows excluded initial a =
      (true, (restrictedRun rows excluded initial a).2)
    exact Prod.ext checked rfl
  | succ b ih =>
    rw [Nat.add_succ]
    let lhs := restrictedRun rows excluded initial (a + b)
    let rhs := restrictedRun rows excluded (restrictedRun rows excluded initial a).2 b
    change (lhs.1 && !excluded.contains lhs.2.1, indexedNext rows lhs.2) =
      (rhs.1 && !excluded.contains rhs.2.1, indexedNext rows rhs.2)
    have joined : lhs = rhs := ih
    rw [joined]

#print axioms transfer
#print axioms append
end PA194IndexedRunRestriction
