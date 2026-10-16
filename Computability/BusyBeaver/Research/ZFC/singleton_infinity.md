`SingletonInfinity.lean` proves the first checkpoint toward ordinary Infinity
from the actual quotient's singleton-closed container. It constructs an
empty-root index with singleton closure and induction over represented sets
and actual formulas. It does **not yet prove ordinary `Inf_form`**.

The base interface contains only actual Extensionality, Pairing and
formula-indexed Separation. It contains neither Infinity nor Separation for
arbitrary semantic predicates. Pairing supplies chosen singletons, with
checked membership, uniqueness and injectivity; an actual empty set is not
a singleton successor.

Given e∈Y with Y singleton-closed, one literal Separation matrix constructs

```text
N = {z∈Y : ∀X [(e∈X ∧ X is singleton-closed) → z∈X]}.
```

The file gives actual `singForm`, `closedForm` and `zMemForm` definitions
and their satisfaction lemmas. This is an object-language quantifier over
sets X, rather than an intersection over arbitrary external classes.
The resulting `Index` has e∈N, singleton closure, and inclusion in every
represented singleton-closed set containing e. Formula induction follows by
applying the supplied formula's own Separation instance to N. It is not
induction over arbitrary external predicates, and N need not consist only
of externally standard natural numbers.

`quotientBase` instantiates this small interface with the actual quotient's
Extensionality, Pairing and Separation. `quotient_index` applies it to
`QuotientBasic.quotient_empty_singleton_container`, retaining both an actual
empty e and the resulting index N. No complete `ZFAxioms` value is fabricated
to access methods whose type already requires `.inf`.

The source and twelve theorem axiom audits, with three caller examples,
passed the explicit pinned Lean 4.32.0 compiler in 0.384 and 0.273 seconds.
The audited dependencies are at most `propext`, `Classical.choice` and
`Quot.sound`; there are no admissions or custom axioms. One development
attempt needed explicit unfolding of the chosen singleton, and a proposition
declaration was changed to `theorem` to remove a linter warning. The final
source and caller have no warnings. The check reused the parent's verified
67-module cache and the separately verified `QuotientBasic` olean, without
rebuilding the full closure or machine bootstrap. Complete commands, hashes,
axiom output and caller source are retained in
`results/singleton-index-verification.json` and
`/tmp/zfc-singleton-index-7_a95ocf`.

The source argument and remaining route are explicit. At upstream commit
`297ab8df7e5de329605c3875b4934643b371a5e3`, `S_ax.v:185–211` proves the
singleton container, and `S_main.v:16–26` invokes the separate
`Std_setinf.inf_or_to_zf` theorem before translating a refutation.
`Std_setinf.v:83–120` constructs the least singleton index above, then
invokes the generic finite-attempt construction in `Std_setrec.v:181–298`.

For that next stage, an attempt f is a set of ordered pairs with its value
at the empty index fixed to an empty seed. Whenever it maps a singleton
successor of u∈N to v', it also maps u to some v with
v'=v∪{v}. Attempts need not already be total functions. Two particular
Separation matrices prove that all attempts agree at each index, and that
every index lies in some attempt's domain. Agreement makes the relation
“some attempt maps this index to this value” partial-functional; one
Replacement matrix collects its image. That image contains the empty set
and is closed under von Neumann successor.

This route uses no preexisting internal omega. The generic upstream
`rec_insts` at `Std_setrec.v:72–74` consists of exactly those two Separation
instances and one Replacement instance. Including the initial ZMem cut,
the proposed ordinary-Infinity bridge uses three particular Separation
matrices and one Replacement matrix. Its finite graphs use only finite
pairs and unions. Upstream additionally cuts out the least inductive omega;
our `Inf_form` only asks for an inductive set, so that final cut can be
omitted. The attempt-graph stage and this final bridge are a mathematical
plan, not theorems in the current module.

The existing `ZF.Zf.ClosureFO_of_ZF`, `omega_ind`, `Approx_exists` and
`BoundedZFCConsistency.omega_recursion` require `ZFAxioms`, including `.inf`.
They cannot supply the missing Infinity field without a separate argument.
Their literal formula constructors and elementary proof patterns remain
useful for a new no-Infinity attempt module. The complete read-only source
and dependency plan is retained at
`/tmp/zfc-singleton-infinity-plan-mlbo3aou/plan.md`.
