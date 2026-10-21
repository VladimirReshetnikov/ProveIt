import BusyBeaver.ZFC.KZip

/-! UNCOMPILED PROPOSAL. No claim that this file has passed Lean.
The existing scanL/scanR lemmas already supply the hard mathematical fact.
This file states the convenient right-head form and composes a generic macro checker.
The RLE implementation/refinement remains an obligation, not an axiom below.
-/
namespace SetTheory.BusyBeaver.ZFC.KBootSweepProposal
open KZip

/-- Right-head version of a leftward self-loop sweep, including the current cell. -/
theorem sweepLeftFromRight {M : TMN} {q : Nat} {b w : Bool}
    (h : M q b = some (w, false, q)) (n : Nat) (l r : List Bool) :
    Reach M (zc q (List.replicate n b ++ l) (b :: r))
      (zl q l (List.replicate (n + 1) w ++ r)) := by
  have first := Reach.of_step (zL (l := List.replicate n b ++ l) (r := r) h)
  have rest := scanL h n l (w :: r)
  have merge : List.replicate n w ++ w :: r = List.replicate (n + 1) w ++ r := by
    rw [List.replicate_succ']; simp
  exact first.trans (by simpa only [merge] using rest)

/-- A checker can use an arbitrary finite representation and arbitrary untrusted macro hints. -/
def check {S Hint : Type} (advance : Hint → S → Option S) : List Hint → S → Option S
  | [], s => some s
  | hint :: tail, s => (advance hint s).bind (check advance tail)

/-- This compositional theorem requires, rather than assumes away, each implementation's
complete-tape refinement theorem. It is not a claim that an RLE advance is already proved. -/
theorem check_sound {S Hint : Type} {M : TMN} (decode : S → Conf)
    (advance : Hint → S → Option S)
    (advance_sound : ∀ hint s t, advance hint s = some t → Reach M (decode s) (decode t)) :
    ∀ hints s t, check advance hints s = some t → Reach M (decode s) (decode t) := by
  intro hints
  induction hints with
  | nil =>
      intro s t h
      simp only [check, Option.some.injEq] at h
      subst t
      exact Reach.refl M _
  | cons hint tail ih =>
      intro s t h
      cases hs : advance hint s with
      | none => simp [check, hs] at h
      | some u =>
          have ht : check advance tail u = some t := by simpa [check, hs] using h
          exact (advance_sound hint s u hs).trans (ih u t ht)

end SetTheory.BusyBeaver.ZFC.KBootSweepProposal
