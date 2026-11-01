# Intuitionistic quantifier-freeness and literal no-zero translation

`IPRAQuantifierFree` defines quantifier-freeness for Foundation's
intuitionistic syntax and proves that Gödel–Gentzen translation preserves it.
It also proves that translation commutes with finite universal closure, and
that the translation of an all-closed inequality is literally the
intuitionistic all-closed negated equality. No equality-decidability premise
is needed for this no-zero translation. This module does not yet define native
intuitionistic PRA or prove that its axioms validate the translated classical
PRA axioms. Its axiom checks report only the standard Lean axioms.

```
python3 Computability/DiophantineConsistency/reviews/ipra-quantifier-free-replay/replay.py
```

This two-module suffix uses the independently replayed strict connector
parent, guards 278 workspace sources, 281 parent project objects, 144 observed
external objects and the Lean binary, with package-only fallback, and rejects
warnings/errors/`sorryAx`. Foundation/ZFCinPA/toolchain/package transitive
ancestry is inherited.

Author and independent peer passed with identical source, object and log
hashes for both modules.
