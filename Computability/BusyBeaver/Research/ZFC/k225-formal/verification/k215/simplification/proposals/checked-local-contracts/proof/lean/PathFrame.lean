import BusyBeaver.ZFC.RegisterPath

/-!
Local source-path arithmetic for framed K215 residual contracts.

A successful check proves the exact source operation for EVERY left prefix.
Failure means that stripping or carry would inspect that prefix.  In particular,
these checkers deliberately distinguish a local suffix exhausted with work left
from the total upstream operations, which silently finish at the end of a word.
The upstream RegisterPath definitions and statements are unchanged.
-/
namespace SetTheory.BusyBeaver.ZFC.PathFrame
open RegisterPath

/-- Work from the right end of a path, represented in reverse order. -/
def stripWithin (b : Bool) : Nat → List Bool → Option (List Bool)
  | 0, xs => some xs
  | _ + 1, [] => none
  | k + 1, x :: xs =>
      if x = b then stripWithin b k xs else stripWithin b (k + 1) xs
termination_by structural _ xs => xs

/-- Increment without allowing the carry to leave the explicit suffix. -/
def incWithin : List Bool → Option (List Bool)
  | [] => none
  | false :: xs => some (true :: xs)
  | true :: xs => (incWithin xs).map (false :: ·)

theorem stripWithin_frame (b : Bool) (xs rest : List Bool) :
    ∀ {k ys}, stripWithin b k xs = some ys →
      stripRev b k (xs ++ rest) = ys ++ rest := by
  induction xs with
  | nil =>
      intro k ys h
      cases k with
      | zero => cases h; simp [stripRev]
      | succ k => cases h
  | cons x xs ih =>
      intro k ys h
      cases k with
      | zero => cases h; rfl
      | succ k =>
          by_cases hx : x = b
          · simp only [stripWithin, hx, if_true] at h
            simpa only [List.cons_append, stripRev, hx, if_true] using ih h
          · simp only [stripWithin, hx, if_false] at h
            simpa only [List.cons_append, stripRev, hx, if_false] using ih h

theorem incWithin_frame (xs rest : List Bool) :
    ∀ {ys}, incWithin xs = some ys → incRev (xs ++ rest) = ys ++ rest := by
  induction xs with
  | nil => intro ys h; cases h
  | cons x xs ih =>
      cases x with
      | false => intro ys h; cases h; rfl
      | true =>
          intro ys h
          simp only [incWithin, Option.map_eq_some_iff] at h
          obtain ⟨zs, hz, rfl⟩ := h
          simpa only [List.cons_append, incRev] using congrArg (false :: ·) (ih hz)

/-- Checked stripping is independent of the arbitrary preserved prefix. -/
theorem stripPath_frame {b : Bool} {k : Nat} {suffix result : List Bool}
    (h : stripWithin b k suffix.reverse = some result.reverse) (P : List Bool) :
    stripPath b k (P ++ suffix) = P ++ result := by
  have hf := stripWithin_frame b suffix.reverse P.reverse h
  simpa only [stripPath, List.reverse_append, List.reverse_reverse] using
    congrArg List.reverse hf

theorem continuePath_frame {k : Nat} {suffix result : List Bool}
    (h : stripWithin true k suffix.reverse = some result.reverse) (P : List Bool) :
    continuePath k (P ++ suffix) = P ++ result :=
  stripPath_frame h P

/-- A successful local carry check excludes overflow into the prefix. -/
theorem incPath_frame {suffix result : List Bool}
    (h : incWithin suffix.reverse = some result.reverse) (P : List Bool) :
    incPath (P ++ suffix) = P ++ result := by
  have hf := incWithin_frame suffix.reverse P.reverse h
  simpa only [incPath, List.reverse_append, List.reverse_reverse] using
    congrArg List.reverse hf

theorem breakPath_frame {k : Nat} {suffix result middleRev : List Bool}
    (hs : stripWithin false k suffix.reverse = some middleRev)
    (hi : incWithin middleRev = some result.reverse) (P : List Bool) :
    breakPath k (P ++ suffix) = P ++ result := by
  have hs' : stripWithin false k suffix.reverse = some middleRev.reverse.reverse := by
    simpa only [List.reverse_reverse] using hs
  rw [breakPath, stripPath_frame hs' P]
  apply incPath_frame
  simpa only [List.reverse_reverse] using hi

/-- A single finite check packages both control operations. -/
def controlCheck (isContinue : Bool) (k : Nat) (suffix result : List Bool) : Bool :=
  let answer := if isContinue then stripWithin true k suffix.reverse
    else (stripWithin false k suffix.reverse).bind incWithin
  answer == some result.reverse

theorem controlCheck_sound {isContinue : Bool} {k : Nat} {suffix result : List Bool}
    (h : controlCheck isContinue k suffix result = true) (P : List Bool) :
    (if isContinue then continuePath k (P ++ suffix)
      else breakPath k (P ++ suffix)) = P ++ result := by
  cases isContinue with
  | true =>
      simp only [controlCheck, if_true, beq_iff_eq] at h
      exact continuePath_frame h P
  | false =>
      simp only [controlCheck, Bool.false_eq_true, if_false, beq_iff_eq] at h
      cases hs : stripWithin false k suffix.reverse with
      | none => simp [hs] at h
      | some middleRev =>
          have hi : incWithin middleRev = some result.reverse := by simpa [hs] using h
          exact breakPath_frame hs hi P

-- Concrete counterexamples to omitting the frame guards.
example : stripWithin true 1 [] = none := rfl
example : continuePath 1 ([true] ++ []) ≠ [true] ++ continuePath 1 [] := by decide
example : incWithin [true] = none := rfl
example : incPath ([false] ++ [true]) ≠ [false] ++ incPath [true] := by decide

#print axioms stripWithin_frame
#print axioms incWithin_frame
#print axioms controlCheck_sound
end SetTheory.BusyBeaver.ZFC.PathFrame
