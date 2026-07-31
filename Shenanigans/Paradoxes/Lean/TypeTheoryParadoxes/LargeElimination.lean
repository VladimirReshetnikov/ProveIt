/-!
# The subsingleton-elimination barrier

Lean's `Prop` is impredicative *and* definitionally proof-irrelevant. Those two
choices are safe together only because the kernel refuses to let data escape a
`Prop`: `elim_only_at_universe_zero` (`src/kernel/inductive.cpp`) restricts an
inductive's recursor to `Prop` motives unless the type is a subsingleton by
construction.

This file proves that restriction is not defensive belt-and-braces. Grant *any*
data-carrying eliminator for a `Prop` with two distinguishable constructors, and
`False` follows in one line — because proof irrelevance has already identified
the two constructors, so the eliminator is being asked to distinguish terms the
kernel considers equal.

Everything here is axiom-free. Nothing here is a defect in Lean; each theorem is
a proof that the hypothesis it takes cannot be granted.
-/

namespace TypeTheoryParadoxes.LargeElimination

/-- `Or.inl` and `Or.inr` are *definitionally* equal: `True ∨ True` is a `Prop`,
and Lean's proof irrelevance identifies any two of its inhabitants. -/
example : (Or.inl trivial : True ∨ True) = Or.inr trivial := rfl

/-- **The barrier, stated as an implication.** A function out of `True ∨ True`
into `Bool` that computes differently on the two constructors gives `False`.

There is no cleverness in the proof: `hl` and `hr` are statements about the same
term, so `hl.symm.trans hr` type-checks and says `true = false`. -/
theorem no_large_elim_of_or
    (f : (True ∨ True) → Bool)
    (hl : f (Or.inl trivial) = true)
    (hr : f (Or.inr trivial) = false) : False :=
  Bool.noConfusion (hl.symm.trans hr)

/-- info: 'TypeTheoryParadoxes.LargeElimination.no_large_elim_of_or' does not depend on any axioms -/
#guard_msgs in #print axioms no_large_elim_of_or

/-- The same for `Exists`, whose witness is the data one most often wants back
out. A `choice`-like operator that is a *function* of the proof is fatal; Lean's
`Classical.choice` escapes this because it is a function of the *type*, not of
any proof of `Nonempty`. -/
theorem no_witness_extraction
    (w : (∃ _ : Bool, True) → Bool)
    (hw : ∀ b h, w ⟨b, h⟩ = b) : False :=
  Bool.noConfusion ((hw true trivial).symm.trans (hw false trivial))

/-- info: 'TypeTheoryParadoxes.LargeElimination.no_witness_extraction' does not depend on any axioms -/
#guard_msgs in #print axioms no_witness_extraction

/-! ## What Lean actually refuses

The restriction is not a check applied at use sites; it is built into the *type*
the kernel gives the recursor when it accepts the inductive. `Or` is a `Prop`
with two constructors, so `Or.rec`'s motive is fixed at `Prop`: -/

/--
info: @Or.rec : ∀ {a b : Prop} {motive : a ∨ b → Prop},
  (∀ (h : a), motive ⋯) → (∀ (h : b), motive ⋯) → ∀ (t : a ∨ b), motive t
-/
#guard_msgs in #check @Or.rec

/-! So the hypothesis of `no_large_elim_of_or` is unobtainable: there is no
motive to instantiate at `Bool`. -/

/--
error: Type mismatch
  Bool
has type
  Type
of sort `Type 1` but is expected to have type
  Prop
of sort `Type`
-/
#guard_msgs in
example (h : True ∨ True) : Bool :=
  @Or.rec True True (fun _ => Bool) (fun _ => true) (fun _ => false) h

/-! ## Why `Acc` and `Quot` are not exceptions

Both eliminate a `Prop` into `Type`, and both are sound, because both *satisfy*
the subsingleton criterion rather than bypass it:

* `Acc r x` has one constructor, so proof irrelevance identifies inhabitants that
  the recursor was already going to treat alike; the proof slot is inert in the
  model. The residual anomaly this creates in the kernel's *decision procedure*
  is measured in `Shenanigans/Audits/Lean/Metatheory/`.
* `Quot r` at `u = 0` has at most one element, so `Quot.lift` is trivially
  well-defined.

The unifying statement: Lean pairs impredicativity with proof irrelevance and
never with proof relevance. Every paradox in this family needs impredicativity
*plus* a data-carrying elimination out of the impredicative sort.
-/

end TypeTheoryParadoxes.LargeElimination
