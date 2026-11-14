import PA195RuntimeEngine

/-! Exact entry-site symbolic branch contracts on the unfolded parent.
The two symbolic equalities are checked on the full parent table, while the
semantic conclusions hold for arbitrary valid register files and gap sizes.
Binding these frames to the archive's source-program graph remains separate. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA195Site25
open M6.Zip M6.Runtime PA195RuntimeEngine

def frame (path : List Bool) (extra : Nat) (effect : Eff) : SConf :=
  (84, false, [.bit true], path.map Seg.bit ++
    [.run false 1 (48 + extra - path.length), .bit true, .box (.plain effect)])

def entry : SConf := frame [true, false, false, false, false, false] 0 .none
def zeroTarget : SConf := frame [true, false, false, false, true, false, false] 0 .none
def positiveTarget : SConf := frame [true, false, false, false, false, true] 1 (.dec 1)

def zeroBranch : Branch := some (1, true)
def positiveBranch : Branch := some (1, false)

theorem zero_exec : (exec machine zeroBranch (fun s => sMatches s zeroTarget) 1024 entry false).isSome = true := by decide +kernel

theorem positive_exec : (exec machine positiveBranch (fun s => sMatches s positiveTarget) 1024 entry false).isSome = true := by decide +kernel

theorem zero_reach (n : Nat) (vs : List Nat) (hv : Valid zeroBranch vs) :
    Reach1 machine (conc n vs entry) (conc n vs zeroTarget) := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp zero_exec
  obtain ⟨hmatch, _, hreach⟩ := symbolic_segment zeroBranch (fun s => sMatches s zeroTarget)
    n 1024 vs hv entry s hs
  have heq := sMatches_conc n vs hmatch
  rwa [heq] at hreach

theorem positive_reach (n : Nat) (vs : List Nat) (hv : Valid positiveBranch vs) :
    Reach1 machine (conc n vs entry) (conc n vs positiveTarget) := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp positive_exec
  obtain ⟨hmatch, _, hreach⟩ := symbolic_segment positiveBranch (fun s => sMatches s positiveTarget)
    n 1024 vs hv entry s hs
  have heq := sMatches_conc n vs hmatch
  rwa [heq] at hreach

#print axioms zero_exec
#print axioms positive_exec
#print axioms zero_reach
#print axioms positive_reach
end PA195Site25
