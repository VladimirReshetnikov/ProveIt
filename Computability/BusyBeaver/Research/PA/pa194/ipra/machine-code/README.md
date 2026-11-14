# Explicit binary-tape arithmetic codes

`BinaryTapeCodes.lean` constructs finite primitive-recursive function-code
syntax for parity and halving. The parity code starts at zero and toggles via
the existing `isZeroCode`; the half code starts at zero and adds the parity of
the preceding index. These operations are needed for the numerical tape halves
of the PA194 candidate and other binary machines, including the earlier PA196 candidate.

Lean proves that their **standard-natural-number evaluations** are `n % 2`
and `n / 2`. Separately, it proves the corresponding zero and successor
recurrences in every nonempty equality structure satisfying the candidate
classical `PRA` theory. The latter statements are all-model Lean theorems;
the module does not yet package them as syntactic `PRA ⊢` sentences, nor does
it prove an all-model identification with a separate division graph.

`TapeStepCodes.lean` builds six additional explicit `Code 3` terms from
those components. Inputs `(left, written, right)` describe the cells on
either side of the head, with the nearest cell as the least significant bit,
and the symbol just written to the current cell. The three outputs after a
right move are `(2*left + written, right % 2, right / 2)`; a left move gives
`(left / 2, left % 2, 2*right + written)`. Lean proves each component's
standard evaluation, bit recovery when `written < 2`, and that moving back
without changing the new head restores the three components. It also proves
all six exact composition equations in every model of candidate classical
PRA. The round-trip results concern standard natural numbers; the all-model
statements are composition equations, not division or round-trip statements.

`TableDispatch.lean` defines three explicit lookup codes for the write bit,
direction, and target state from the 388-row dense PA194 table. A generic
list-to-code compiler uses zero tests and predecessor recursively; no code is
chosen from an existence theorem. Its standard evaluation at `(state, read)`
agrees with the pinned table at index `2*state+read`, with default
`(0,0,194)` outside the table. This theorem applies to every pair of natural
numbers, although machine use supplies a binary read and working state.
The all-model lookup recurrences imply separate row-output equations for
each **standard numeral** index in every model of candidate classical PRA.
`TableModelSemantics.lean` also proves a finite decision-list specification
for the lookup at *every* model element, including nonstandard ones, using
the model's predecessor and zero. This is a Lean metatheorem, not yet an
iPRA proof. The table is generated into a private temporary directory from
the SHA-256-pinned archive and member by the parent `generate.py`.

`ConfigurationStep.lean` gives three explicit `Code 3` terms for the next
state and two next tape halves. These use the PA194 bounded representation:
the right half includes the head cell as its low bit. `modelNext` proves that
their interpretations agree with a model-side step specification in every
candidate classical PRA model for **all** model configurations. The
specification is stated through the model interpretations of addition,
parity, halving and the comparison code and the finite decision-list lookup;
it does not independently identify parity or halving with division in
nonstandard models. `ConfigurationStandard.lean` proves that these terms evaluate on every
natural-number configuration to `PA194Bounded.next`, and uses its existing
zipper refinement to identify the result with a literal PA194 tape step.
This standard-model binding does not itself internalize the literal-machine
correspondence in PRA. `PackedClock.lean` explicitly constructs a square-root
decoder, a packed transition, an iterator, and a halting indicator as finite
`Code` terms. The
clock's zero and successor equations are proved in every candidate PRA model.
`PackedStandard.lean` proves the decoder, pairing, and iterator correct over
standard natural numbers and proves that the halting indicator equals the
existing bounded predicate. Thus an existential over its standard evaluation
is equivalent to literal PA194 halting. `PackedRootModel.lean` uses open
induction to prove that the explicit square-root code equals Foundation's
model-theoretic square root at every element of every candidate classical PRA
model. `PackedDecoderModel.lean` connects the explicit decoder to Foundation's two
unpairing projections for every model element, and proves that both decode a
pair back to its inputs in every candidate PRA model. The packed clock has not
yet been linked to a model-side iteration of the decoded configurations, and
the clock is not yet a proof of either iPRA implication.

The work still needs an all-model connection between the explicit packed
clock and iterated configuration semantics, as well as an internal proof of a
PA-consistency implication. It does not prove either
machine-specific iPRA implication. In particular, the standard-model
equalities here do not identify these explicit codes with the noncomputably
chosen `PA194Bounded.boundedCode` in arbitrary models.

This directory adapts the checked PA195 arithmetic construction to the pinned
PA194 table, with 194 working controls and halt control 194. It uses separate
builds because the Lean module names are shared between the two research
artifacts.

The complete check uses Lean 4.32.0 and two prebuilt dependency overlays:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-decoder.sh
```

The script regenerates the PA194 table from its pinned archive member and
rebuilds all modules in a private temporary directory. It checks five source
hashes, two directly imported project object hashes, Foundation `Init`, and
the source of `M6/Zip.lean`; it does not rebuild the other transitive overlay
objects. Paths and caches are machine-specific. The script checks printed
axiom dependencies for `sorryAx`.
