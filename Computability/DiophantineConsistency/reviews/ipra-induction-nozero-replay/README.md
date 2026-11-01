# Native induction syntax and mapped no-zero translation

`IPRANativeInduction` defines a finite-parameter, quantifier-free induction
schema in Foundation's intuitionistic syntax. Its inductive step uses
intuitionistic implication and the exact `x+1` term from the classical
Foundation schema. It proves that the Gödel–Gentzen image of an open matrix
is eligible for that schema. It does **not** yet prove that the translation
of Foundation's classical induction axiom follows from a native instance,
relate the free-variable and finite-parameter closure mechanisms, or establish
its equivalence to a standard successor-step presentation.

`IPRAMappedNoZero` proves the mapped exact no-zero sentence translates
literally to the universal closure of intuitionistic negated equality on the
mapped terms. This is syntactic and requires no equality decidability.
All reported Lean metatheory axioms are among `propext`, `Classical.choice`,
and `Quot.sound`.

```
python3 Computability/DiophantineConsistency/reviews/ipra-induction-nozero-replay/replay.py
```

The four-module suffix uses the independently replayed quantifier-free parent,
guards 282 workspace sources, 283 parent project objects, 144 observed
external objects and the Lean binary, with package-only fallback, and rejects
warnings/errors/`sorryAx`. Foundation/ZFCinPA/toolchain/package transitive
ancestry is inherited.

Author and independent replay both passed with identical source, object, and
full-log hashes for all four modules. The independent receipt is in
`independent/`; external transitive ancestry remains inherited.
