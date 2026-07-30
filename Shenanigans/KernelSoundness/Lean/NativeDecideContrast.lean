/-!
Loophole #1: `Lean.ofReduceBool` (a *standard* Lean axiom, shipped in `Init.Core`)
is unsound in the presence of the equally standard `@[implemented_by]` attribute.

No `sorry`, no user-declared axioms, no `unsafe` in the proof term.
-/

def evil : Bool := true

@[implemented_by evil]
def secret : Bool := false

-- The kernel unfolds `secret` to `false`.
theorem secret_false : secret = false := rfl

-- `native_decide` runs the *compiled* code, which is `evil = true`.
theorem secret_true : secret = true := by native_decide

theorem boom : False := by
  have h : (true : Bool) = false := secret_true.symm.trans secret_false
  exact Bool.noConfusion h

#print axioms boom

-- Same thing, but reaching `False` for an arbitrary proposition:
theorem anything (P : Prop) : P := boom.elim
#print axioms anything
