# The actual quotient reaches ZF without Foundation or Choice

`QuotientZF0.lean` proves that a nonempty actual CP/GIC model has a quotient
satisfying every closed axiom of `PSCCalibration.ZF0Ax`. That theory contains
Extensionality, Pairing, Union, Power Set, ordinary Infinity, Separation and
functional Replacement. Foundation and Choice are omitted.

The proof composes the existing quotient Extensionality, literal Separation,
Pairing/Union, Power and Replacement theorems with the new finite-attempt
Infinity construction. `quotient_zfAxioms` fills all six fields of the local
`ZFAxioms` bundle; `quotient_zf0` separately adds Power, which that bundle
omits. `quotient_models` uses the existing closed-sentence model bridge,
under arbitrary quotient valuations. No stronger axiom bundle is assumed.

An explicit raw witness gives an actual quotient valuation. Generic
first-order soundness then proves `zf0_consistent_of_model`, the ordinary
metatheoretic statement that this model rules out a finite ZF0 refutation.
The decoded numerical-bundle adapter retains irreflexivity and an explicit
valuation; empty structures cannot satisfy its nonemptiness obligation.

The file also proves a useful one-way link to the actual abstract enumerator:

```text
ZF0 refutation → C254 falsity code1 → Enum254.Halts
¬Enum254.Halts → no ZF0 refutation.
```

For the first arrow, assume a ZF0 refutation. Any nonempty irreflexive
EncBundle model would yield a CP/GIC model and hence a quotient ZF0 model,
contradicting soundness. `Code254.c254_complete` therefore yields numerical
falsity. `Enum254.complete` supplies the second arrow. This argument uses the
EncBundle model interface directly; it does not need the subsequently proved reverse
comparison from encodable to all decoded bundles. All domain valuations
remain explicit through completeness and quotient construction.

The converse consistency direction, the
[Foundation/Choice comparison](foundation_choice_route.md), finite proof-code
translation inside the intended base theory, and the remaining literal-path and binary simulations remain separate.
The merged L2 development now identifies the actual 219-node structured
program with the enumerator, and `ProgramZF0` lifts this one-way consequence
to that program. These results establish neither a ZFC equivalence nor a new
state record. The underlying machine, calculus and CP/GIC interpretation keep
the Mira-Cult/Jeff/Wade attribution recorded in their source modules.

The source passed pinned Lean4.32 in0.339seconds after adding the three final
refutation/enumerator consequences. The umbrella passed in0.479seconds;
16 axiom audits and three caller examples passed. Every dependency is among
`propext`, `Classical.choice` and `Quot.sound`, with no custom axioms or
admissions. `results/quotient-zf0-verification.json` records the final source,
commands, audit and callers. It supersedes the earlier version of this one
module in `results/infinity-l2-integration-verification.json`; that earlier
record remains the source check for the other seven additions. Both checks
reuse the previously verified dependencies and do not rebuild the expensive
finite bootstrap.
