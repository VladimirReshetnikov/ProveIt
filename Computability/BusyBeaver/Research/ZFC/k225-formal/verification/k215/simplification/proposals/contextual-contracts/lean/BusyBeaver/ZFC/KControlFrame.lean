import BusyBeaver.ZFC.RegisterPath

/-!
Control actions that are confined to a suffix preserve every earlier prefix.
The option-valued functions reject underflow and carry out of the suffix.
They are proof-producing interfaces to the existing RegisterPath arithmetic,
not replacements for its definitions.
-/
namespace SetTheory.BusyBeaver.ZFC.KControlFrame
open RegisterPath

/-- Strip in least-significant-first order, failing if the suffix is too short. -/
def stripChecked (b : Bool) : Nat → List Bool → Option (List Bool)
  | 0, s => some s
  | _ + 1, [] => none
  | k + 1, x :: s =>
      if x = b then stripChecked b k s else stripChecked b (k + 1) s
termination_by structural _ s => s

/-- Increment in least-significant-first order, rejecting an escaping carry. -/
def incChecked : List Bool → Option (List Bool)
  | [] => none
  | false :: s => some (true :: s)
  | true :: s => (incChecked s).map (false :: ·)

theorem stripChecked_append {b : Bool} {k : Nat} {s t : List Bool}
    (h : stripChecked b k s = some t) (p : List Bool) :
    stripRev b k (s ++ p) = t ++ p := by
  induction s generalizing k t with
  | nil =>
      cases k with
      | zero => simpa [stripChecked, stripRev] using h
      | succ k => simp [stripChecked] at h
  | cons x s ih =>
      cases k with
      | zero =>
          simp only [stripChecked, Option.some.injEq] at h
          subst t
          rfl
      | succ k =>
          by_cases hx : x = b
          · simp only [stripChecked, hx, if_true] at h
            simpa only [List.cons_append, stripRev, hx, if_true] using ih h
          · simp only [stripChecked, hx, if_false] at h
            simpa only [List.cons_append, stripRev, hx, if_false] using ih h

theorem incChecked_append {s t : List Bool} (h : incChecked s = some t)
    (p : List Bool) : incRev (s ++ p) = t ++ p := by
  induction s generalizing t with
  | nil => simp [incChecked] at h
  | cons x s ih =>
      cases x with
      | false =>
          simp only [incChecked, Option.some.injEq] at h
          subst t
          rfl
      | true =>
          cases he : incChecked s with
          | none => simp [incChecked, he] at h
          | some u =>
              simp only [incChecked, he, Option.map_some, Option.some.injEq] at h
              subst t
              simpa only [List.cons_append, incRev] using congrArg (false :: ·) (ih he)

def stripSuffix (b : Bool) (k : Nat) (s : List Bool) : Option (List Bool) :=
  (stripChecked b k s.reverse).map List.reverse

def incSuffix (s : List Bool) : Option (List Bool) :=
  (incChecked s.reverse).map List.reverse

theorem stripSuffix_frame {b : Bool} {k : Nat} {s t : List Bool}
    (h : stripSuffix b k s = some t) (p : List Bool) :
    stripPath b k (p ++ s) = p ++ t := by
  cases he : stripChecked b k s.reverse with
  | none => simp [stripSuffix, he] at h
  | some u =>
      simp only [stripSuffix, he, Option.map_some, Option.some.injEq] at h
      subst t
      simp only [stripPath, List.reverse_append, stripChecked_append he,
        List.reverse_reverse]

theorem incSuffix_frame {s t : List Bool} (h : incSuffix s = some t)
    (p : List Bool) : incPath (p ++ s) = p ++ t := by
  cases he : incChecked s.reverse with
  | none => simp [incSuffix, he] at h
  | some u =>
      simp only [incSuffix, he, Option.map_some, Option.some.injEq] at h
      subst t
      simp only [incPath, List.reverse_append, incChecked_append he,
        List.reverse_reverse]

/-- A successful control suffix check certifies that neither stripping nor
    incrementing reaches the caller's prefix. -/
def controlSuffix : Edge → List Bool → Option (List Bool)
  | .cont k, s => stripSuffix true k s
  | .brk k, s => (stripSuffix false k s).bind incSuffix
  | _, _ => none

theorem controlSuffix_frame {e : Edge} {s t : List Bool}
    (h : controlSuffix e s = some t) (p : List Bool) (r : Registers) :
    execute e (p ++ s) r = some ⟨p ++ t, r⟩ := by
  cases e with
  | node _ | inc _ | decnz _ | halt => simp [controlSuffix] at h
  | cont k =>
      simp only [execute, continuePath, stripSuffix_frame h]
  | brk k =>
      cases hs : stripSuffix false k s with
      | none => simp [controlSuffix, hs] at h
      | some u =>
          have hi : incSuffix u = some t := by simpa [controlSuffix, hs] using h
          simp only [execute, breakPath, stripSuffix_frame hs, incSuffix_frame hi]

#print axioms stripChecked_append
#print axioms incChecked_append
#print axioms controlSuffix_frame

end SetTheory.BusyBeaver.ZFC.KControlFrame
