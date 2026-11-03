# Finite Pell recurrence / model cast draft

This source defines the ordinary finite recurrence with offset `b`, i.e. Pell base `b+2`, and proposes an induction relating both coordinates to the represented recurrence in any IΣ₁ model. It is an unchecked source draft, with no Lean acceptance yet. It contains no finite seed calculation or graph theorem.

A separate standard-ℕ interval draft uses this recurrence. The seed's first ordinate uses offset `2*(X*Y*Y-1)+1` at index 16; its comparison ordinate uses offset `Y*(X+1)` at index 31. These are the explicit source hypotheses in the parametric boundary theorem, not the shifted graph ordinate. Both must remain distinct.

The [independent source review](../../reviews/trace74-boundary-recurrence-cast-draft-independent/README.md) checked the offset and index conventions. Its review does not constitute a Lean check.
