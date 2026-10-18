import Std

/-!
A command-level refinement for eliminating the preserved enumeration counter.

The old scheduler increments its candidate counter when it starts a candidate.
The new scheduler increments a geometric clock when it finishes that candidate.
`body q w` consumes a command code q and returns its unconsumed tail and state,
or returns `none` to halt. The theorem is uniform in body and in the state type.

This file does NOT supply a binary Turing-machine implementation of the loader,
the eight-register runtime, or an end-to-end consistency theorem.
-/

namespace GapClock

structure Legacy (W : Type) where
  next : Nat
  tail : Nat
  work : W
  deriving Repr, DecidableEq

structure Geometric (W : Type) where
  gap : Nat
  tail : Nat
  work : W
  deriving Repr, DecidableEq

variable {W : Type}

def observe (s : Geometric W) : Legacy W :=
  ⟨s.gap + (if s.tail = 0 then 0 else 1), s.tail, s.work⟩

def legacyStep (body : Nat → W → Option (Nat × W)) (s : Legacy W) : Option (Legacy W) :=
  let query := if s.tail = 0 then s.next else s.tail - 1
  let next := if s.tail = 0 then s.next + 1 else s.next
  (body query s.work).map fun p => ⟨next, p.1, p.2⟩

def geometricStep (body : Nat → W → Option (Nat × W))
    (s : Geometric W) : Option (Geometric W) :=
  let query := if s.tail = 0 then s.gap else s.tail - 1
  (body query s.work).map fun p =>
    ⟨s.gap + (if p.1 = 0 then 1 else 0), p.1, p.2⟩

/-- Exact command-level refinement, including halting, for every command body. -/
theorem step_refines (body : Nat → W → Option (Nat × W)) (s : Geometric W) :
    (geometricStep body s).map observe = legacyStep body (observe s) := by
  rcases s with ⟨g, l, w⟩
  by_cases hl : l = 0
  · subst l
    cases hb : body g w with
    | none => simp [geometricStep, legacyStep, observe, hb]
    | some p =>
      rcases p with ⟨t, v⟩
      by_cases ht : t = 0 <;> simp [geometricStep, legacyStep, observe, hb, ht]
  · cases hb : body (l - 1) w with
    | none => simp [geometricStep, legacyStep, observe, hl, hb]
    | some p =>
      rcases p with ⟨t, v⟩
      by_cases ht : t = 0 <;> simp [geometricStep, legacyStep, observe, hl, hb, ht]

def iterate {S : Type} (step : S → Option S) : Nat → S → Option S
  | 0, s => some s
  | n + 1, s => (step s).bind (iterate step n)

/-- All finite command traces agree under the observation map. -/
theorem iterate_refines (body : Nat → W → Option (Nat × W))
    (n : Nat) (s : Geometric W) :
    (iterate (geometricStep body) n s).map observe =
      iterate (legacyStep body) n (observe s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [iterate]
    have h := step_refines body s
    cases hg : geometricStep body s with
    | none =>
      simp only [hg, Option.map_none] at h
      simp only [Option.bind_none, Option.map_none, ← h]
    | some t =>
      simp only [hg, Option.map_some] at h
      simp only [Option.bind_some, ← h]
      exact ih t

def Halts {S : Type} (step : S → Option S) (s : S) : Prop :=
  ∃ n, iterate step n s = none

/-- No correctness, soundness, or termination hypothesis on body is needed. -/
theorem halts_iff (body : Nat → W → Option (Nat × W)) (s : Geometric W) :
    Halts (geometricStep body) s ↔ Halts (legacyStep body) (observe s) := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h := iterate_refines body n s
    simpa [hn] using h.symm
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h := iterate_refines body n s
    rw [hn] at h
    cases hg : iterate (geometricStep body) n s with
    | none => rfl
    | some t => simp [hg] at h

/-- A boundary start with clock g corresponds exactly to next candidate g. -/
theorem boundary_halts_iff (body : Nat → W → Option (Nat × W)) (g : Nat) (w : W) :
    Halts (geometricStep body) ⟨g, 0, w⟩ ↔
      Halts (legacyStep body) ⟨g, 0, w⟩ := by
  simpa [observe] using halts_iff body (Geometric.mk g 0 w)

/-- The logical next-candidate value can be recovered without storing it. -/
theorem counter_recovery (s : Geometric W) :
    (observe s).next = s.gap + (if s.tail = 0 then 0 else 1) := rfl

/-! The final phase-overlaid loader increments the physical gap at candidate
start instead. Its reported tape contract is (g,tail=0) -> (g+1,tail=g+1),
then the loop decrements tail before executing the body. This gives the
following *different* observation and exact source scheduler. These results
still do not prove the literal loader, register boxes, or blank bootstrap. -/

def eagerObserve (s : Geometric W) : Legacy W :=
  ⟨s.gap, s.tail, s.work⟩

def eagerStep (body : Nat → W → Option (Nat × W))
    (s : Geometric W) : Option (Geometric W) :=
  let query := if s.tail = 0 then s.gap else s.tail - 1
  let nextGap := if s.tail = 0 then s.gap + 1 else s.gap
  (body query s.work).map fun p => ⟨nextGap, p.1, p.2⟩

/-- A loader which increments the gap when a candidate starts stores exactly
the original logical next-candidate counter at every command boundary. -/
theorem eager_step_refines (body : Nat → W → Option (Nat × W))
    (s : Geometric W) :
    (eagerStep body s).map eagerObserve = legacyStep body (eagerObserve s) := by
  simp only [eagerStep, eagerObserve, legacyStep, Option.map_map]
  rfl

theorem eager_iterate_refines (body : Nat → W → Option (Nat × W))
    (n : Nat) (s : Geometric W) :
    (iterate (eagerStep body) n s).map eagerObserve =
      iterate (legacyStep body) n (eagerObserve s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [iterate]
    have h := eager_step_refines body s
    cases hg : eagerStep body s with
    | none =>
      simp only [hg, Option.map_none] at h
      simp only [Option.bind_none, Option.map_none, ← h]
    | some t =>
      simp only [hg, Option.map_some] at h
      simp only [Option.bind_some, ← h]
      exact ih t

theorem eager_halts_iff (body : Nat → W → Option (Nat × W))
    (s : Geometric W) :
    Halts (eagerStep body) s ↔ Halts (legacyStep body) (eagerObserve s) := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h := eager_iterate_refines body n s
    simpa [hn] using h.symm
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h := eager_iterate_refines body n s
    rw [hn] at h
    cases hg : iterate (eagerStep body) n s with
    | none => rfl
    | some t => simp [hg] at h

#print axioms step_refines
#print axioms iterate_refines
#print axioms halts_iff
#print axioms boundary_halts_iff
#print axioms eager_step_refines
#print axioms eager_iterate_refines
#print axioms eager_halts_iff

end GapClock
