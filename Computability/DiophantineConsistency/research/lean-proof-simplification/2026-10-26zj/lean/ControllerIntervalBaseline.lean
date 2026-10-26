import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Intervals
namespace ControllerIntervalBaseline
theorem interval_injOn {T : ℕ} [NeZero T] (start : ZMod T) (a : ℕ) (ha : a ≤ T) :
    Set.InjOn (fun j : ℕ => start+(j : ZMod T)) (Finset.range a) := by
  intro j hj k hk he
  have hjT : j < T := (Finset.mem_range.mp hj).trans_le ha
  have hkT : k < T := (Finset.mem_range.mp hk).trans_le ha
  have hc : (j : ZMod T) = (k : ZMod T) := add_left_cancel he
  have hv := congrArg ZMod.val hc
  simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt hjT,Nat.mod_eq_of_lt hkT] using hv


#print axioms interval_injOn
end ControllerIntervalBaseline
