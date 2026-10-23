import BusyBeaver.ZFC.EnumPerm
import BoundedScheduler

/-!
Concrete adapter for the maintained K215 `EnumPerm` source at
cbf94cb552a3b49509e0eee80e7455d4eb5974c6.

Status: source-reviewed integration draft unless accompanied by a successful
repository-toolchain receipt. `BoundedScheduler.lean` is independently testable.
The private `boundedDynamics` wrapper preserves the production run function.
-/

namespace SetTheory.BusyBeaver.ZFC.EnumPerm

open CofinalScheduler BoundedScheduler
open SetTheory.BusyBeaver.ZFC.KCode222

private abbrev boundedDynamics : Dynamics St where
  step := enumStep
  run := run
  zero := fun _ => rfl
  succ := fun n s => by cases h : enumStep s <;> simp only [run, h]

private theorem boundedLaws : boundedDynamics.Laws St.pl St.np where
  advance := by
    intro s t hs hp
    rw [(step_eq hs).2]
    simp only [fetch, hp, if_true]
  descend := by
    intro s t hs hp
    obtain ⟨h1, h2⟩ := step_eq hs
    have hd := decode_le (fetch s).1
    simp only [fetch, hp, if_false] at h1 h2 hd
    exact ⟨by omega, h2⟩

private theorem refill_bound (s t : St) (hs : enumStep s = some t)
    (hp : s.pl = 0) : t.pl ≤ s.np := by
  rw [(step_eq hs).1]
  simpa only [fetch, hp, if_true] using decode_le (fetch s).1

/-- Successful prefix bound; the optional final halting transition is excluded. -/
theorem find_candidate_bounded (target : Nat) (s : St) (hle : s.np ≤ target) :
    ∃ n t, n ≤ triangle target - triangle s.np + s.pl ∧ run n s = some t ∧
      (enumStep t = none ∨ t.pl = 0 ∧ t.np = target) :=
  find_bounded boundedDynamics boundedLaws refill_bound target s hle

/-- Completeness also holds inside a candidate, with arbitrary working payload.
    Its converse still requires the existing derivability invariant. -/
theorem complete_from (sd : St) (h : C222 Code254.F) : HaltsFrom sd := by
  obtain ⟨p, hp⟩ := build_c222 h
  let cs := p ++ [.drop, .nip, .nip]
  let target := encL (.ax 0 1 sd.np) cs
  have hN : sd.np ≤ target := encL_ge sd.np cs
  obtain ⟨n, s, _, hr, hf⟩ := find_candidate_bounded target sd hN
  rcases hf with hh | ⟨hpl, hnp⟩
  · exact ⟨n, s, hr, hh⟩
  · have hfetch : (fetch s).1 = encL (.ax 0 1 sd.np) cs := by
      simpa only [fetch, hpl, if_true, target] using hnp
    obtain ⟨k, s', hr', hs'⟩ :=
      exec_list cs (.ax 0 1 sd.np) s hfetch (program_none sd.np p hp _)
    exact ⟨n + k, s', by rwa [run_add n k sd s hr], hs'⟩

theorem halts_iff_from {s : St} (hs : Inv (toW s)) : HaltsFrom s ↔ C222 Code254.F :=
  ⟨sound hs, complete_from s⟩

#print axioms find_candidate_bounded
#print axioms complete_from
#print axioms halts_iff_from

end SetTheory.BusyBeaver.ZFC.EnumPerm
