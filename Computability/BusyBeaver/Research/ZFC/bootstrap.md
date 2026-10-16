# The remaining forward bootstrap steps

`Lean/BusyBeaver/ZFC/Bootstrap.lean` extends the shallow semantic results in
`PositiveClosure.lean`. It was checked with the repository's Lean 4.32.0 on
16 October 2026. Each closure assumption names one explicit relation; the
file does not quantify a closure axiom over arbitrary semantic relations.

`pairing_of_instance` uses the two-cycle
`(x=a ∧ y=b) ∨ (x=b ∧ y=a)`. Each fiber is empty or has one output, including
when `a=b`. Starting at `a` puts `b` in the positive hull; its next edge puts
`a` there. The support clause excludes any other members. Extensionality is
unnecessary for this existence argument.

`partial_replacement_of_instance` takes an at-most-single-valued relation
on `A`, an exact separated Russell subset `r` of `A`, and the already
constructed `⋃A`. The root is outside `A`. Consequently the relation
`(x=r ∧ y∈A) ∨ (x∈A ∧ R(x,y))` has a subset-bounded root fiber and empty or
singleton fibers elsewhere. Its positive hull covers every output of
`R` on `A`. The theorem then uses the explicitly supplied Separation
predicate `y∈C ∧ ∃x∈A R(x,y)` to form the exact partial image. It assumes
neither totality of `R` on `A` nor Collection or a family of chosen bounds.

`adjoin_of_pair_union` and `successors_of_pair_union` construct `A∪{t}` and
`x∪{x}` from the earlier singleton, Pairing and Union resources.
`infinity_of_instance` needs no Extensionality: any two successors have the
same members, so every successor is a subset of any chosen successor.
It applies only the successor relation's closure instance at an empty
root `e`. Adjoining `e` to the positive output hull produces a set containing
`e` and closed under successor; the proof allows the original hull to omit
`e`.

The printed axiom audits are `[propext, Classical.choice, Quot.sound]` for
Pairing and partial Replacement, and no axioms for Infinity beyond its
explicit hypotheses. These are ordinary Lean foundational dependencies,
not additional set-theoretic axioms. No custom axiom, `sorry`, or
`native_decide` is used.

The relation `R` and membership structure are semantic parameters in these
lemmas. `DefinableClosure.lean` supplies actual formula witnesses for all the
forward constructions, using formula-level Separation. `PSCCalibration.lean`
then proves full first-order deductive equivalence of Extensionality plus
subset-seeded PSC with ZF without Foundation or Choice. These separate files
still supply no coded proof translation, Foundation/Choice consistency bridge,
or machine endpoint.
