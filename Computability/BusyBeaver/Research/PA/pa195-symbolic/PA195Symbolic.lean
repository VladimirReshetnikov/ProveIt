import PA195RuntimeEngine

/-! Reusable symbolic-contract representation and semantic soundness. The
executable cases are generated separately from explicit source-site records;
their correspondence to the source program is a separate obligation. -/
set_option autoImplicit false
namespace PA195Symbolic
open M6.Zip M6.Runtime

structure Contract where
  branch : Branch
  start : SConf
  target : Option SConf

def frame (path : List Bool) (extra : Nat) (effect : Eff) : SConf :=
  (84, false, [.bit true], path.map Seg.bit ++
    [.run false 1 (48 + extra - path.length), .bit true, .box (.plain effect)])

def targetPredicate : Option SConf → SConf → Bool
  | none, s => s.1 == 254
  | some e, s => sMatches s e

def accepted (M : TMN) (c : Contract) : Bool :=
  (exec M c.branch (targetPredicate c.target) 1024 c.start false).isSome

/-- The finite Boolean test need not be trusted: when Lean checks it, the
upstream soundness theorem yields a positive run for every valid file and gap. -/
theorem accepted_sound (M : TMN) (B : BoxLemmas M) (c : Contract)
    (hc : accepted M c = true) (n : Nat) (vs : List Nat) (hv : Valid c.branch vs) :
    ∃ s, targetPredicate c.target s = true ∧ Reach1 M (conc n vs c.start) (conc n vs s) := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp hc
  obtain ⟨ht, _, hr⟩ := exec_sound B n hv 1024 c.start false s hs
  exact ⟨s, ht, hr rfl⟩

/-- When the target is a frame, normalization identifies the complete
physical endpoint with that frame, for every valid file and gap. -/
theorem accepted_frame_sound (M : TMN) (B : BoxLemmas M) (c : Contract)
    (e : SConf) (he : c.target = some e) (hc : accepted M c = true)
    (n : Nat) (vs : List Nat) (hv : Valid c.branch vs) :
    Reach1 M (conc n vs c.start) (conc n vs e) := by
  obtain ⟨s, ht, hr⟩ := accepted_sound M B c hc n vs hv
  rw [he] at ht
  have hs : sMatches s e = true := ht
  rw [sMatches_conc n vs hs] at hr
  exact hr

#print axioms accepted_sound
#print axioms accepted_frame_sound
end PA195Symbolic
