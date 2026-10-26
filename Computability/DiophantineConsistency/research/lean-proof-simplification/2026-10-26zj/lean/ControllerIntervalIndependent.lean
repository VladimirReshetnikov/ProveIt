import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Range

namespace IndependentControllerReview

theorem interval_injOn {T : ℕ} [NeZero T] (start : ZMod T) (a : ℕ) (ha : a ≤ T) :
    Set.InjOn (fun j : ℕ => start + (j : ZMod T)) (Finset.range a) := by
  intro j hj k hk he
  exact ((ZMod.natCast_eq_natCast_iff j k T).mp (add_left_cancel he)).eq_of_lt_of_lt
    ((Finset.mem_range.mp hj).trans_le ha) ((Finset.mem_range.mp hk).trans_le ha)

example (start : ZMod 6) :
    Set.InjOn (fun j : ℕ => start + (j : ZMod 6)) (Finset.range 6) :=
  interval_injOn start 6 (by decide)

example (start : ZMod 1) :
    Set.InjOn (fun j : ℕ => start + (j : ZMod 1)) (Finset.range 1) :=
  interval_injOn start 1 (by decide)

example (start : ZMod 5) :
    Set.InjOn (fun j : ℕ => start + (j : ZMod 5)) (Finset.range 0) :=
  interval_injOn start 0 (by decide)

#print axioms interval_injOn

end IndependentControllerReview
