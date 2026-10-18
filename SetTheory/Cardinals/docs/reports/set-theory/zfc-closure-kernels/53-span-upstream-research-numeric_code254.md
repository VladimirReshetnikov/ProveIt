`NumericCode254.lean` proves that the two existing versions of the published
four-tag numerical calculus derive exactly the same codes:

```text
Numeric254.NumThm n ↔ Code254.C254 n
```

This holds for every natural number n, including truth code 0 and all codes
outside the named encoder's image. The proof first identifies the two Cantor
pairings: the recursive triangular number in `Numeric254` equals
`Cantor.tri`, and commutativity resolves their displayed addition order. It
then proves all nineteen remaining numerical expression identities: the four
tags, relative falsity, negation, conjunction, existential quantification,
eight logical rows, C, G and the complete C/G/vacuity bundle. Induction in
each direction preserves the twelve inference constructors, including MP's
minor/major premise order and both actual bundle gates c≠a and c≠b.

The definitions retain their existing attribution to Mira-Cult's machine,
Jeff's verification at upstream commit
`297ab8df7e5de329605c3875b4934643b371a5e3`, and the independently authored
`Code254` formalization. No imported or existing Lean source was changed.

Structural induction also proves that `NamedNumeric254.encode` and
`Code254.enc` agree on every named formula. Consequently the existing
theory Q satisfies

```text
NamedNumeric254.Q f ↔ Code254.C254 (Code254.enc f)
Tarski.Thm NamedNumeric254.Q bot ↔ Code254.C254 1
```

The named transport corollary accepts the same explicit axiom-encoding
obligation as the existing `NamedNumeric254.transport`, expressed directly
with C254. This connects the independently developed logical APIs. It does
not identify Q with a calibrated set theory. It also does not compare the
`EncBundle` model class used in `Code254.c254_complete` with the decoded-bundle
model class used in `Code254.c254_sound`. The encoder's deliberate falsity/
`rel 0 0` alias and its missing truth code 0 remain exactly as before. No
enumerator, register execution, binary simulation, endpoint or new state
bound follows from this bridge alone.

The new module compiled with the explicit absolute Lean 4.32.0 executable
(commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35) in 0.411 seconds, followed by
all 27 public theorem axiom audits and four caller examples in 0.275 seconds.
`falsity_eq` uses no axioms; the other 26 audited results use only `propext`
and `Quot.sound`. There are no custom axioms, `sorryAx`, `native_decide`,
warnings or failed build attempts. This was a scoped source check using the
parent's previously verified 57-module cache; the complete dependency closure
and expensive machine bootstrap were not rebuilt.

`results/numeric-code254-verification.json` retains the source and direct
import identities, actual compiler commands/version, complete axiom output,
caller source and dependency-cache identities. The original logs, new olean
and caller remain in `/tmp/zfc-numeric-code254-d4kj5ki0`.
