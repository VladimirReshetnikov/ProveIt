# PA194 finite source-LK compiler

`PA194SourceLKBase.lean` adapts the nine logical rules from the pinned
upstream Foundation LK definition to the current `LO.FirstOrder` syntax,
with multisets of propositions and the same shift, free-variable and
instantiation operations. The older Foundation snapshot has no upstream
`FirstOrder.LK.Basic` module; the local inductive `SourceLK` is therefore a
port of those rules, not an imported Foundation provability predicate. Its
multiset traversal uses a quotient representative and `Classical.choice`.
No equivalence to another LK presentation has yet been proved.

`PA194SourceLK.lean` adapts the pinned upstream constructive compiler. For
every local `SourceLK` logical derivation it constructs a finite PA194
calculus context proof, and `compileSingleton` obtains a finite proof of
the encoded singleton formula. The proof works over actual Foundation
semiformulas and explicitly supplies binder-budget and freshening
conditions. Its printed axiom dependencies are `propext`,
`Classical.choice` and `Quot.sound`, with no `sorryAx`.

`PA194SourceEquality.lean` additionally supplies finite PA194 proofs of
the translated reflexivity, symmetry, transitivity, congruence and
irreflexivity formulas. These are the concrete equality/irreflexivity
supplier formulas from the upstream source language, not the remaining
set-theoretic or PA supplier.

This is an ordinary Lean theorem. It does not yet supply PA axioms,
induction or an interpretation of PA in this source language; it does not
establish PA refutation, candidate-machine nonhalting, or internalize the
compiler in PA/PRA. Upstream file hashes record the source of the adapted
rules, budget and compiler; they do not assert that the different
Foundation versions are definitionally equal.

To replay from the repository root, set `IPRA_FOUNDATION_OVERLAY` to the
audited Lean 4.32 Foundation object directory and run
`bash Computability/BusyBeaver/Research/PA/pa194-source-lk/check.sh`. It
rebuilds the full source-calculus prerequisite chain in tmpfs, checks the
upstream pins, compiles the LK and equality-supplier files, and rejects `sorryAx` in their
printed theorem dependencies.
The full nested `pa194-source-separation/check.sh` replay passed, including
this package and all of its prerequisites.
