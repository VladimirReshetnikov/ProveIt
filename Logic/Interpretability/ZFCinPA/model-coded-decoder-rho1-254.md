# Internal existence of equality: numerical rho1

`ModelCodedDecoderRho1_254` proves the actual numerical rho1 in ZF and ZFC for
all internal labels, including coincident labels and zero:

```text
Provable ZF  (decode (ArithmeticCode254.rho1 a b))
Provable ZFC (decode (ArithmeticCode254.rho1 a b))
```

The source is existence of equality, `wex a (weq a b)`, whose literal arithmetic
code is `wim (wal a (wim (weq a b) 1)) 1`. This is the actual first logical row,
not an implication-introduction axiom. The theorem holds in every IΣ1 model;
it is not restricted to quotations of standard labels or matrices.

The finite target proof opens the named binder at free label `b`. A represented
binder on a binary equality atom replaces precisely the occurrences of its
chosen label. When `a=b` both occurrences become the new bound slot, and when
`a≠b` only the first does. In either case substituting free `b` yields reflexive
equality `b=b`. Thus a named universal of the negated equality implies
`¬(b=b)`. A fixed ordinary reflexivity theorem, internalized before specializing
at the arbitrary internal free variable, refutes that universal.

This gives the logical existence theorem for any actual Δ1 set-language theory
extending equality. The generic decoded row also explicitly requires internal
negation of decoded1 and actual named-GEN. Those two resources, already checked
in the rho6/generalization packages, transport the equivalence between relative
falsity and primitive negation through the named binder. This handles the
capture of membership(0,0) when the chosen label is0. The final actual ZF/ZFC
clients discharge all resources. No fresh-label, distinct-label, closed-matrix
or shift-fixedness premise is added.

The source also exposes a reusable atom interface: `namedBody_eqAtom` describes
binding on equality with arbitrary internal arguments, using `namedVar` to
retain unchosen labels. It supplies a direct syntactic route to the later
bundle equality-vacuity clause under the two actual gates; that clause itself
is not proved by this package.

The exact139-line source and audit passed Lean4.32.0 with ten ordered axiom
reports, sixteen callers, zero warnings, and only `propext`, `Classical.choice`,
and `Quot.sound`. Recorded source/audit compiler times are2.801406s/2.590188s.
The one unsuccessful attempt was an elaboration failure: the pair-vector length
needed explicit `1+1=2` normalization, and a substitution equality needed its
output arity explicitly set to0. Both source repairs preserve the logical
proof. Its original source/audit/guard and diagnostic log remain in the history
record; old changed-path hashes are not asserted current.

The maintained portable replay is

```bash
python Logic/Interpretability/ZFCinPA/check_model_coded_decoder_rho1_254.py --output /tmp/decoded-rho1-replay
```

The guard accepts explicit repository, dependency-root, compiler, library,
source/audit and parent evidence/source/audit paths. `--project-cache` relocates
the40 selected predecessor objects, and `--namespace-cache` supplies the complete
existing Foundation namespace. The separately recorded unused Cantor object
remains a historical input; a relocated parent record can give its new path
with the same identity. Only the previously accepted exact same-source Cantor
pair is allowed.

The guard merges the actual rho6 12/16 and Equality11/12 PASS records, imports
both fresh parent objects, checks shared source/object identities and the exact
40-project/six-boundary closure, and verifies actual first providers including
Omega. All106 input identities, compiler/pins/manifest and the fresh result are
rechecked. Packaging performed two explicitly unbuilt override/relocated
preflights and three rejection controls, without proof replay or dependency
builds. Preflights query the compiler version and execute zero proof builds.

Together with the separately checked rho2–rho8, this completes the eight
individual logical-row decoder clients. It does not prove the bundle, general
accepted-proof translation, or a PA consistency equivalence with ZFC or the
binary machine.
