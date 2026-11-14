# Explicit binary-tape arithmetic codes

`BinaryTapeCodes.lean` constructs finite primitive-recursive function-code
syntax for parity and halving. The parity code starts at zero and toggles via
the existing `isZeroCode`; the half code starts at zero and adds the parity of
the preceding index. These operations are needed for the numerical tape halves
of the PA195 candidate and other binary machines, including the earlier PA196 candidate.

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
direction, and target state from the 390-row dense PA195 table. A generic
list-to-code compiler uses zero tests and predecessor recursively; no code is
chosen from an existence theorem. Its standard evaluation at `(state, read)`
agrees with the pinned table at index `2*state+read`, with default
`(0,0,195)` outside the table. This theorem applies to every pair of natural
numbers, although machine use supplies a binary read and working state.
The all-model lookup recurrences imply separate row-output equations for
each **standard numeral** index in every model of candidate classical PRA.
`TableModelSemantics.lean` also proves a finite decision-list specification
for the lookup at *every* model element, including nonstandard ones, using
the model's predecessor and zero. This is a Lean metatheorem, not yet an
iPRA proof. The table is generated into a private temporary directory from
the SHA-256-pinned archive and member by the parent `generate.py`.

`ConfigurationStep.lean` gives three explicit `Code 3` terms for the next
state and two next tape halves. These use the PA195 bounded representation:
the right half includes the head cell as its low bit. `modelNext` proves that
their interpretations agree with a model-side step specification in every
candidate classical PRA model for **all** model configurations. The
specification is stated through the model interpretations of addition,
parity, halving and the comparison code and the finite decision-list lookup;
it does not independently identify parity or halving with division in
nonstandard models. `ConfigurationStandard.lean` proves that these terms evaluate on every
natural-number configuration to `PA195Bounded.next`, and uses its existing
zipper refinement to identify the result with a literal PA195 tape step.
This standard-model binding does not itself internalize the literal-machine
correspondence in PRA. `PackedClock.lean` explicitly constructs a square-root
decoder, a packed transition, an iterator, and a halting indicator as finite
`Code` terms. The
clock's zero and successor equations are proved in every candidate PRA model.
`PackedStandard.lean` proves the decoder, pairing, and iterator correct over
standard natural numbers and proves that the halting indicator equals the
existing bounded predicate. Thus an existential over its standard evaluation
is equivalent to literal PA195 halting. `PackedRootModel.lean` uses open
induction to prove that the explicit square-root code equals Foundation's
model-theoretic square root at every element of every candidate classical PRA
model. The complete decoder has not yet been linked
to model-theoretic unpairing, and the clock is not yet a proof of either iPRA
implication.

The work still needs an all-model connection between the explicit packed
clock and the configuration semantics, including decoder correctness, as
well as an internal proof of a PA-consistency implication. It does not prove either
machine-specific iPRA implication. In particular, the standard-model
equalities here do not identify these explicit codes with the noncomputably
chosen `PA195Bounded.boundedCode` in arbitrary models.

The check uses Lean 4.32.0 and two prebuilt dependency overlays. The following
are the exact local caches used for the original check:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa195/ipra/machine-code/check.sh
```

The script rebuilds all five modules in a private temporary directory and verifies
the hashes of five direct sources, the two directly imported project objects,
and the Foundation `Init` object. It prints axiom dependencies and rejects
`sorryAx`. It assumes the remaining transitive overlay objects were built from
the matching sources and toolchain; it does not independently rebuild them.
For the local run, the recorded project dependency closure of the two imports
contained 79 modules, and their current source and object hashes matched the
build's `state.json`; the Foundation provider was the exact overlay shown
above. Paths and caches are machine-specific.

For the standard-number binding, use the same overlays with
`bash Computability/BusyBeaver/Research/PA/pa195/ipra/machine-code/check-standard.sh`.
This separate check also rebuilds the pinned `M6/Zip.lean`, generated literal
PA195 table, and `PA195Bounded.lean` in its private temporary directory.

For the explicit packed clock and standard halting binding, use the same
overlays with `bash Computability/BusyBeaver/Research/PA/pa195/ipra/machine-code/check-clock.sh`.
This performs the standard-step rebuild plus the two packed-clock modules.

The all-model square-root graph can be replayed with the same overlays using
`bash Computability/BusyBeaver/Research/PA/pa195/ipra/machine-code/check-root.sh`.
