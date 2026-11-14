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

These are explicit arithmetic components, not a PA195 transition or clock
code. The work still needs the full finite transition lookup, a configuration
encoding and projections, a state iterator and a proof that its internal
recurrence matches the exact PA195 machine. It does not prove either
machine-specific iPRA implication. In particular, the standard-model
equalities here do not identify these explicit codes with the noncomputably
chosen `PA196Bounded.boundedCode` in arbitrary models.

The check uses Lean 4.32.0 and two prebuilt dependency overlays. The following
are the exact local caches used for the original check:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa195/ipra/machine-code/check.sh
```

The script rebuilds both modules in a private temporary directory and verifies
the hashes of five direct sources, the two directly imported project objects,
and the Foundation `Init` object. It prints axiom dependencies and rejects
`sorryAx`. It assumes the remaining transitive overlay objects were built from
the matching sources and toolchain; it does not independently rebuild them.
For the local run, the recorded project dependency closure of the two imports
contained 79 modules, and their current source and object hashes matched the
build's `state.json`; the Foundation provider was the exact overlay shown
above. Paths and caches are machine-specific.
