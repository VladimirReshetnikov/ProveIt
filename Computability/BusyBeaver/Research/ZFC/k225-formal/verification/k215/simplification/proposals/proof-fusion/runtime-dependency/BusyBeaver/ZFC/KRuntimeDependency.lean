import BusyBeaver.ZFC.KHomeReady

/-!
Exact dependency transport for the maintained K-family symbolic executor.

This module completes the interpreter-local obligation left open by the
rocq-composition proposal. A direct footprint records all table lookups,
including absent rows and the fallback after an unsuccessful box oracle.
The Home wrapper is handled by an explicit equality of its readiness gates.
The concrete soundness corollary separately requires the target BoxLemmas.
-/

namespace SetTheory.BusyBeaver.ZFC.KRuntimeDependency

open KZip KRuntimeCore

abbrev Key := Nat × Bool

def Agrees (M N : TMN) (ks : List Key) : Prop :=
  ∀ k ∈ ks, M k.1 k.2 = N k.1 k.2

/-- Exact direct table lookups of the original symbolic stepper. -/
def stepReads (br : Branch) : SConf → List Key
  | (q, true, .run b _ _ :: _, _) => [(q, b)]
  | (q, false, _, .bit b :: _) => [(q, b)]
  | (q, false, _, .run b _ _ :: _) => [(q, b)]
  | (q, false, _, [.box x]) =>
      match oracle q br x with
      | none => [(q, false)]
      | some _ => []
  | _ => []

theorem sstep_local {M N : TMN} (br : Branch) (s : SConf)
    (h : Agrees M N (stepReads br s)) : sstep M br s = sstep N br s := by
  rcases s with ⟨q, onl, l, r⟩
  cases onl with
  | true =>
    cases l with
    | nil => rfl
    | cons x xs =>
      cases x with
      | bit b => rfl
      | box x => rfl
      | run b a c =>
        have he := h (q, b) (by simp [stepReads])
        simp only [sstep, he]
  | false =>
    cases r with
    | nil => rfl
    | cons x xs =>
      cases x with
      | bit b =>
        have he := h (q, b) (by simp [stepReads])
        simp only [sstep, he]
      | run b a c =>
        have he := h (q, b) (by simp [stepReads])
        simp only [sstep, he]
      | box x =>
        cases xs with
        | cons y ys => rfl
        | nil =>
          cases ho : oracle q br x with
          | some out => simp only [sstep, ho]
          | none =>
            have he := h (q, false) (by simp [stepReads, ho])
            simp only [sstep, ho, he]

/-- A fixed choice of Home acceleration. Actual callers choose `ready M`. -/
def next (fast : Bool) (M : TMN) (br : Branch) : SConf → Option (SConf × Bool) :=
  if fast then KHomeReady.homeStep M br else sstep M br

def reads (fast : Bool) (br : Branch) (s : SConf) : List Key :=
  if fast then
    match KHome.home s with
    | some _ => []
    | none => stepReads br s
  else stepReads br s

theorem next_local {M N : TMN} (fast : Bool) (br : Branch) (s : SConf)
    (h : Agrees M N (reads fast br s)) : next fast M br s = next fast N br s := by
  cases fast with
  | false => exact sstep_local br s h
  | true =>
    cases hh : KHome.home s with
    | some t => simp [next, KHomeReady.homeStep, hh]
    | none =>
      have hs := sstep_local br s (by simpa [reads, hh] using h)
      simpa [next, KHomeReady.homeStep, hh] using hs

/-- Collect exactly the direct reads performed before success, failure or fuel
exhaustion, using the source table. The initial progress flag is preserved. -/
def traceReads (fast : Bool) (M : TMN) (br : Branch) (tgt : SConf → Bool) :
    Nat → SConf → Bool → List Key
  | 0, _, _ => []
  | f + 1, s, moved =>
      if moved && tgt s then []
      else reads fast br s ++
        match next fast M br s with
        | none => []
        | some (s', m) => traceReads fast M br tgt f s' (moved || m)

theorem exec_transport {M N : TMN} (fast : Bool) (br : Branch)
    (tgt : SConf → Bool) (f : Nat) (s : SConf) (moved : Bool)
    (h : Agrees M N (traceReads fast M br tgt f s moved)) :
    execWith (next fast M br) tgt f s moved =
      execWith (next fast N br) tgt f s moved := by
  induction f generalizing s moved with
  | zero => rfl
  | succ f ih =>
    by_cases stop : (moved && tgt s) = true
    · simp only [execWith, stop, if_true]
    · have hhead : Agrees M N (reads fast br s) := by
        intro k hk
        exact h k (by simp [traceReads, stop, hk])
      have hn := next_local fast br s hhead
      simp only [execWith, stop, Bool.false_eq_true, if_false, ← hn]
      cases hs : next fast M br s with
      | none => rfl
      | some sm =>
        rcases sm with ⟨s', m⟩
        apply ih
        intro k hk
        exact h k (by simp [traceReads, stop, hs, hk])

/-- Transport the actual maintained Home-ready executor. Readiness agreement
is a separate, finite table check; it is not hidden in the trace footprint. -/
theorem home_exec_transport {M N : TMN}
    (hr : KHomeReady.ready M = KHomeReady.ready N)
    (br : Branch) (tgt : SConf → Bool) (f : Nat) (s : SConf) (moved : Bool)
    (h : Agrees M N (traceReads (KHomeReady.ready M) M br tgt f s moved)) :
    KHomeReady.exec M br tgt f s moved = KHomeReady.exec N br tgt f s moved := by
  have ht := exec_transport (M := M) (N := N) (KHomeReady.ready M) br tgt f s moved h
  simpa only [KHomeReady.exec, KHomeReady.stepper, next, hr] using ht

/-- A compact support may contain repeated or unused keys. Its coverage proof
is checked once for the source trace, then reused without replaying that trace. -/
theorem home_exec_transport_of_cover {M N : TMN}
    (hr : KHomeReady.ready M = KHomeReady.ready N)
    (br : Branch) (tgt : SConf → Bool) (f : Nat) (s : SConf) (moved : Bool)
    (support : List Key)
    (cover : ∀ k ∈ traceReads (KHomeReady.ready M) M br tgt f s moved, k ∈ support)
    (ha : Agrees M N support) :
    KHomeReady.exec M br tgt f s moved = KHomeReady.exec N br tgt f s moved :=
  home_exec_transport hr br tgt f s moved (fun k hk => ha k (cover k hk))

/-- The per-target check only compares the complete option-valued rows in the
saved support; it need not symbolically execute the target table. -/
def sameOn (M N : TMN) (support : List Key) : Bool :=
  support.all (fun k => decide (M k.1 k.2 = N k.1 k.2))

theorem sameOn_sound {M N : TMN} {support : List Key}
    (h : sameOn M N support = true) : Agrees M N support := by
  simpa only [sameOn, List.all_eq_true, decide_eq_true_eq, Agrees] using h

/-- Target-machine soundness of a reused successful source check. In
particular, progress remains positive when the initial flag is false. -/
theorem reused_exec_sound {M N : TMN} (BN : BoxLemmas N)
    (hr : KHomeReady.ready M = KHomeReady.ready N)
    {br : Branch} {tgt : SConf → Bool} (n : Nat) {vs : List Nat}
    (hv : Valid br vs) (f : Nat) (s : SConf) (moved : Bool) (t : SConf)
    (ha : Agrees M N (traceReads (KHomeReady.ready M) M br tgt f s moved))
    (hs : KHomeReady.exec M br tgt f s moved = some t) :
    tgt t = true ∧ Reach N (conc n vs s) (conc n vs t) ∧
      (moved = false → Reach1 N (conc n vs s) (conc n vs t)) := by
  apply KHomeReady.exec_sound BN n hv f s moved t
  rw [← home_exec_transport hr br tgt f s moved ha]
  exact hs

#print axioms sstep_local
#print axioms exec_transport
#print axioms home_exec_transport
#print axioms home_exec_transport_of_cover
#print axioms sameOn_sound
#print axioms reused_exec_sound

end SetTheory.BusyBeaver.ZFC.KRuntimeDependency
