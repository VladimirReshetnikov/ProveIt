# PA196 bounded halting in the iPRA language

`PA196Bounded.lean` implements a primitive-recursive simulation of the literal
PA196 machine using natural numbers for the two binary tape halves. Its finite
table is proved equal, row by row in the Lean kernel, to the imported
`PA196.Literal.transition`. The simulation treats **every** state at least 196
as an absorbing state, matching the exact domain of the upstream machine's
partial step. It proves that encoding commutes with this totalized zipper step,
and hence that its bounded-halting predicate has a witness exactly when the
upstream `M6.Zip.Halts PA196.Literal.machine blankZip` holds.

The file also obtains a primitive-recursive function code and a corresponding
one-variable term in the existing iPRA language, and proves the same binding
for its interpretation over the standard natural numbers. The code is chosen
using an existence theorem; it is not an explicitly serialized code. These
standard-model results do **not** prove either reduction inside iPRA, nor do
they prove an equivalence with PA consistency. In particular, they do not
formalize the correctness of the machine's proof search.

`PA196Endpoint.lean` connects this particular halting sentence to the native
intuitionistic reading of the PA-consistency formula. Its conclusion is an
iPRA derivation, but it explicitly assumes iPRA derivations of both
machine-specific implications: PA refutability implies halting, and halting
implies double-negated PA refutability. Neither implication is established
here. A second conditional endpoint weakens the first hypothesis to PA
refutability implying double-negated halting; it still needs both reductions
to be proved in iPRA. The comparison of this native consistency formula with the separately
defined Gödel–Gentzen reading also remains conditional.

`PA196StandardSemantics.lean` defines an ordinary Tarskian interpretation of
intuitionistic formulas in a classical structure. It proves that, under this
interpretation in the standard natural numbers, the native consistency
sentence says that Foundation's PA is consistent, and the constructed halting
sentence says that the imported literal machine halts. These are external
standard-model identifications; they do not establish either internal iPRA
reduction or identify the upstream FFL and Foundation LO proof codings.

`PA196ForwardGG.lean` proves a conditional transfer from classical PRA to
standard iPRA for this exact halting sentence: a classical PRA proof that the
mapped PA-refutation predicate implies bounded halting yields an iPRA proof
that native PA refutability implies double-negated halting. The classical PRA
proof remains a hypothesis. The upstream result is a PA theorem in a different
coding, so it does not directly supply this hypothesis.

`PA196ReverseGG.lean` provides a corresponding conditional transfer in the
other direction. It assumes both a classical PRA proof that bounded machine
halting implies the mapped PA-refutation predicate and a classical PRA
bounded-witness certificate for that particular predicate. Neither assumption
is established here. The file proves the bounded-matrix comparison and the
erasure of the bound needed to use those assumptions in the native iPRA
endpoint.

For the witness hypothesis, the generic
`PRAWitnessRefutationOuter.certificate_of_core` reduces the task to bounds on
both polarities of the PA derivation core. The existing proofs of those bounds
are specialized to the set-theory language. Reusing them for PA requires, in
particular, bounds for the actual arithmetic induction-axiom recognizer;
its Δ₁ definability in IΣ₁ alone does not supply the required PRA certificate.
`PA196PACoreBound.lean` instantiates the generic theorem for the exact PA
refutation predicate. Its two all-model core bounds are explicit hypotheses
and remain unproved.

`PA196PAMinusWitness.lean` proves the positive and negative bounds for the
finite PA-minus component of Foundation's actual PA axiom recognizer. It also
shows that bounds for the unrestricted induction-schema component suffice
for the complete axiom recognizer. Those induction-schema bounds, the rest
of the derivation-core bounds, and the machine reductions remain open.

`PA196PAAxiomBound.lean` derives bounds for both exact axiom-rule branches of
the PA derivation core from the corresponding PA axiom-recognizer bounds.
`PA196PASimpleRuleBounds.lean` separately proves both polarities for the exact
verum, conjunction, disjunction, and weakening branches.
`PA196PAAxiomAssembly.lean` connects the PA-minus and axiom-branch results,
conditional on the two unrestricted induction-schema bounds. The other rule
branches and the induction-schema recognizer still need bounds before the
complete core certificate follows.

`PA196InductionClosureWitness.lean` proves both witness bounds for the exact
quantifier-closure graph subformulas of the unrestricted-induction recognizer.
The other recognizer subformulas and the complete induction bounds remain open.
`PA196InductionFvarWitness.lean` bounds the exact positive free-variable-vector
graph and its enclosing existential, conditional on a bound for the remaining
Σ₁ conjunct. This does not establish that remaining bound.
`PA196InductionBodyAll.lean` bounds two exact quantifier-code graphs in the
induction-body recognizer and their nested existentials, conditional on the
remaining inner tail's witness bound.

`PA196PAAlphabetBounds.lean` proves both polarities of the witness bounds for
Foundation's arithmetic function-symbol and relation-symbol recognizers.
Those base bounds do not yet establish bounds for formula or proof coding.
`PA196PAFormulaBound.lean` uses the symbol results and fixed-point
truncation to reduce both bounds for the arithmetic formula recognizer to the
corresponding term-vector recognizer bounds. `PA196PATermBounds.lean` proves
those term and term-vector bounds, and `PA196PAFormulaComplete.lean` composes
them to prove both formula-recognizer bounds without additional hypotheses.
The arithmetic formula-recursion and negation modules build on those bounds;
`PA196PAIdentityBounds.lean` uses them to prove both witness-bound polarities
for the exact identity-rule branches, and `PA196PACutBounds.lean` does so for
cut. `PA196PABvGrowth.lean` proves bounds on arithmetic term and formula
bound-variable counts. The term-recursion, variable-graph, and formula-set
modules build on these results: `PA196PAFormulaSetComplete.lean` proves both
witness bounds for the exact formula-set conjunct of Foundation PA's
derivation core. The full core bounds still need the remaining rule branches
and the unrestricted-induction axiom recognizer.

`PA196PRAAssembly.lean` composes the two conditional transfers with the
intuitionistic endpoint. Its equivalence in standard iPRA has three explicit
classical PRA hypotheses: the forward reduction, the reverse reduction, and
the PA-specific witness certificate. All three remain to be proved.

## Checking

The check uses Lean 4.32.0 and the root project's Lake environment. It checks
source hashes for the imported zipper, literal machine, table, and two direct
iPRA sources; rebuilds the upstream zipper, literal machine, consistency module,
and these bridge modules in a private temporary directory; and prints axiom
dependencies. Its two
dependency overlays must already exist and must themselves be built from the
matching sources and toolchain. It does not rebuild or independently verify
their transitive dependencies.

For the local caches used in the original check:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa196-vs-u208/ipra/check.sh
```

The iPRA overlay's `state.json` records that exact Foundation provider. These
temporary paths are machine-specific; substitute equivalently built overlays
when reproducing elsewhere. The Foundation checkout used for this check was at
revision `32e1a0956a8622fad067328ca1959729a7634428`.
