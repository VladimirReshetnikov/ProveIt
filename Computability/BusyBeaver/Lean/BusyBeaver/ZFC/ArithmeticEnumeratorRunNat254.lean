import BusyBeaver.ZFC.ArithmeticEnumeratorRun254

/-!
Ordinary-Nat comparison with the literal Enum254.run scheduler.
The arithmetic run composes steps at the end of a time interval, while the
native partial run consumes its first step before recursing. The checked
semigroup law aligns these orders for every Nat time and every six-field
state, including arbitrary dirty registers. Zero represents native none;
every native live state has a positive code. This adapter does not identify
nonstandard arithmetic indices with external finite native runs.

-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRunNat254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticCommandStep254
open ArithmeticEnumeratorStep254 ArithmeticEnumeratorRun254
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[simp] theorem encodeSt_ne_zero (s : Enum254.St) : encodeSt s ≠ 0 := by
  simp [encodeSt]

@[simp] theorem encodeResult_eq_zero (s : Option Enum254.St) :
    ArithmeticEnumeratorStep254.encodeResult s = 0 ↔ s = none := by
  cases s with
  | none => simp [ArithmeticEnumeratorStep254.encodeResult]
  | some s => simp [ArithmeticEnumeratorStep254.encodeResult]

/-- Arithmetic iteration expressed with its first step before the tail run. -/
lemma run_succ_first (time initial : Nat) :
    run (time + 1) initial = run time (step initial) := by
  rw [show time + 1 = 1 + time by omega, run_add, run_one]

/-- Exact native comparison for all ordinary times and all dirty states. -/
theorem run_encode_nat (time : Nat) (s : Enum254.St) :
    run time (encodeSt s) = ArithmeticEnumeratorStep254.encodeResult (Enum254.run time s) := by
  induction time generalizing s with
  | zero => simp [Enum254.run, ArithmeticEnumeratorStep254.encodeResult]
  | succ time ih =>
    rw [run_succ_first, step_encode_nat]
    cases hs : Enum254.enumStep s with
    | none => simp [hs, Enum254.run, ArithmeticEnumeratorStep254.encodeResult]
    | some s' =>
      simpa only [Enum254.run, hs, ArithmeticEnumeratorStep254.encodeResult] using ih s'

/-- The fixed graph agrees with actual native execution on every Nat input. -/
theorem runDef_encode_nat (out time : Nat) (s : Enum254.St) :
    runDef.val.Evalb ![out,time,encodeSt s] ↔
      out = ArithmeticEnumeratorStep254.encodeResult (Enum254.run time s) := by
  simp [run_encode_nat]

/-- Native none is exactly absorbing scalar halt0, not a failed decode. -/
theorem run_zero_iff_native_none (time : Nat) (s : Enum254.St) :
    run time (encodeSt s) = 0 ↔ Enum254.run time s = none := by
  rw [run_encode_nat, encodeResult_eq_zero]

/-- Recover the actual halting edge from a native partial run returning none.
This uses the literal run recursion, not a semantic stuck-state convention. -/
theorem haltsFrom_of_run_none (time : Nat) (s : Enum254.St)
    (h : Enum254.run time s = none) : EnumSafeStart254.HaltsFrom s := by
  induction time generalizing s with
  | zero => simp only [Enum254.run] at h; cases h
  | succ time ih =>
    cases hs : Enum254.enumStep s with
    | none => exact ⟨0, s, rfl, hs⟩
    | some s' =>
      obtain ⟨k, out, hr, hh⟩ := ih s' (by simpa only [Enum254.run, hs] using h)
      exact ⟨k+1, out, by simpa only [Enum254.run, hs] using hr, hh⟩

/-- Every native halting edge gives a none result at the next clock tick. -/
theorem run_none_of_haltsFrom (s : Enum254.St) (h : EnumSafeStart254.HaltsFrom s) :
    ∃ time, Enum254.run time s = none := by
  obtain ⟨time, out, hr, hh⟩ := h
  refine ⟨time+1, ?_⟩
  rw [Enum254.run_add time 1 s out hr]
  simp only [Enum254.run, hh]

/-- Halting comparison for every ordinary native state, not only the blank one. -/
theorem halts_iff_native (s : Enum254.St) :
    (∃ time : Nat, run time (encodeSt s) = 0) ↔ EnumSafeStart254.HaltsFrom s := by
  constructor
  · rintro ⟨time, h⟩
    exact haltsFrom_of_run_none time s ((run_zero_iff_native_none time s).mp h)
  · intro h
    obtain ⟨time, hr⟩ := run_none_of_haltsFrom s h
    exact ⟨time, (run_zero_iff_native_none time s).mpr hr⟩

/-- The literal zero six-register state is the positive scalar state1. -/
@[simp] theorem encodeSt_s0 : encodeSt Enum254.s0 = 1 := by
  simp [encodeSt, Enum254.s0, Enum254.toW, encodeW, liveValue, cantor_nat,
    Code254.P, SetTheory.Cantor.toNat, SetTheory.Cantor.tri]

/-- Exact blank halting comparison with the actual Enum254.Halts definition. -/
theorem blank_halts_iff :
    (∃ time : Nat, run time 1 = 0) ↔ Enum254.Halts := by
  simpa only [encodeSt_s0, EnumSafeStart254.HaltsFrom, Enum254.Halts] using
    halts_iff_native Enum254.s0

end SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRunNat254
