import CM215Invariant
import PositiveStutter

set_option maxRecDepth 100000

namespace CM215

@[simp] theorem old52false : old 52 false = some ⟨false,true,149⟩ := rfl
@[simp] theorem old52true : old 52 true = some ⟨true,true,145⟩ := rfl
@[simp] theorem old170false : old 170 false = some ⟨false,true,163⟩ := rfl
@[simp] theorem old170true : old 170 true = some ⟨true,true,145⟩ := rfl
@[simp] theorem new52false : new 52 false = some ⟨false,false,170⟩ := rfl
@[simp] theorem new52true : new 52 true = some ⟨true,true,145⟩ := rfl
@[simp] theorem new170false : new 170 false = some ⟨false,true,178⟩ := rfl
@[simp] theorem new170true : new 170 true = some ⟨true,true,125⟩ := rfl
@[simp] theorem new125false : new 125 false = some ⟨false,true,149⟩ := rfl
@[simp] theorem new178false : new 178 false = some ⟨false,true,163⟩ := rfl

open PositiveStutter

theorem marker_one_block (t : Tape) (h : Int)
    (hb : t h = false) (hm : t (h-1) = true) :
    run (step new) 3 ⟨52,h,t⟩ = some ⟨149,h+1,t⟩ := by
  have hx : h + -1 = h - 1 := by omega
  have hy : h - 1 + 1 = h := by omega
  have hw := write_of_read t h false hb
  have hv := write_of_read t (h-1) true hm
  simp [run, step, act, move, hb, hm, hx, hy, hw, hv]

theorem marker_zero_block (t : Tape) (h : Int)
    (hb : t h = false) (hm : t (h-1) = false) :
    run (step new) 3 ⟨52,h,t⟩ = some ⟨163,h+1,t⟩ := by
  have hx : h + -1 = h - 1 := by omega
  have hy : h - 1 + 1 = h := by omega
  have hw := write_of_read t h false hb
  have hv := write_of_read t (h-1) false hm
  simp [run, step, act, move, hb, hm, hx, hy, hw, hv]

theorem source52zero (t : Tape) (h : Int) (hb : t h = false) :
    step old ⟨52,h,t⟩ = some ⟨149,h+1,t⟩ := by
  simp [step, act, move, hb, write_of_read t h false hb]

theorem source170zero (t : Tape) (h : Int) (hb : t h = false) :
    step old ⟨170,h,t⟩ = some ⟨163,h+1,t⟩ := by
  simp [step, act, move, hb, write_of_read t h false hb]

theorem source52one (t : Tape) (h : Int) (hb : t h = true) :
    step old ⟨52,h,t⟩ = some ⟨145,h+1,t⟩ := by
  simp [step, act, move, hb, write_of_read t h true hb]

theorem source170one (t : Tape) (h : Int) (hb : t h = true) :
    step old ⟨170,h,t⟩ = some ⟨145,h+1,t⟩ := by
  simp [step, act, move, hb, write_of_read t h true hb]

theorem target_one (t : Tape) (h : Int) (hb : t h = true) :
    run (step new) 1 ⟨52,h,t⟩ = some ⟨145,h+1,t⟩ := by
  simp [run, step, act, move, hb, write_of_read t h true hb]

theorem local_advance (c c' : Config) (hc : Invariant c)
    (hs : step old c = some c') :
    ∃ k, 0 < k ∧ k ≤ 3 ∧
      run (step new) k (mapped c) = some (mapped c') := by
  rcases c with ⟨q,h,t⟩
  by_cases hq : q = 52
  · subst q
    cases hb : t h with
    | false =>
      have hm := hc.1 rfl
      rw [source52zero t h hb] at hs
      cases Option.some.inj hs
      refine ⟨3, by decide, by decide, ?_⟩
      simpa [mapped, phi] using marker_one_block t h hb hm
    | true =>
      rw [source52one t h hb] at hs
      cases Option.some.inj hs
      refine ⟨1, by decide, by decide, ?_⟩
      simpa [mapped, phi] using target_one t h hb
  · by_cases hr : q = 170
    · subst q
      cases hb : t h with
      | false =>
        have hm : t (h-1) = false := by
          rcases hc.2.1 rfl with ht | hm
          · simp [hb] at ht
          · exact hm
        rw [source170zero t h hb] at hs
        cases Option.some.inj hs
        refine ⟨3, by decide, by decide, ?_⟩
        simpa [mapped, phi] using marker_zero_block t h hb hm
      | true =>
        rw [source170one t h hb] at hs
        cases Option.some.inj hs
        refine ⟨1, by decide, by decide, ?_⟩
        simpa [mapped, phi] using target_one t h hb
    · refine ⟨1, by decide, by decide, ?_⟩
      simpa [run] using ordinary_step ⟨q,h,t⟩ c' hq hr hs

def Related (c d : Config) : Prop := Invariant c ∧ d = mapped c

theorem positiveSimulation : Simulation (step old) (step new) Related where
  terminal := by
    rintro a b ⟨_, rfl⟩
    exact halt_step_agrees a
  advance := by
    rintro a b a' ⟨ha, rfl⟩ hs
    obtain ⟨k, hk, _, hr⟩ := local_advance a a' ha hs
    exact ⟨k, mapped a', hk, hr, invariant_step a a' ha hs, rfl⟩

/-- The two *literal dense tables* are equihalting on every binary tape,
from designated control 0 and any initial head position. -/
theorem all_tapes_halts_iff (t : Tape) (h : Int) :
    Halts (step old) ⟨0,h,t⟩ ↔ Halts (step new) ⟨0,h,t⟩ := by
  apply positiveSimulation.halts_iff
  exact ⟨initial_invariant t h, rfl⟩

theorem all_tapes_nonhalting_iff (t : Tape) (h : Int) :
    (¬ Halts (step old) ⟨0,h,t⟩) ↔ (¬ Halts (step new) ⟨0,h,t⟩) :=
  not_congr (all_tapes_halts_iff t h)

theorem blank_halts_iff :
    Halts (step old) ⟨0,0,fun _ => false⟩ ↔
      Halts (step new) ⟨0,0,fun _ => false⟩ :=
  all_tapes_halts_iff _ _

/-- This final adapter deliberately exposes the inherited consistency
calibration as a premise; it does not axiomatize or reprove that premise. -/
theorem calibration_transfer (Refutation : Prop)
    (baseline : Halts (step old) ⟨0,0,fun _ => false⟩ ↔ Refutation) :
    Halts (step new) ⟨0,0,fun _ => false⟩ ↔ Refutation :=
  blank_halts_iff.symm.trans baseline

#print axioms all_tapes_halts_iff
#print axioms all_tapes_nonhalting_iff
#print axioms calibration_transfer

end CM215
