# A limit of the K/S joint-induction shortcut

An attempted removal of the self-vacuity row can try to prove stability and
fresh-binder persistence together by structural induction. The negation step
does not follow from K/S, normality, seriality and the retained rho6 alone.

Take the 16-element Heyting algebra of upward-closed subsets of the five
worlds {0,1,2,3,4}, ordered by 0<2, 1<2 and 1<4. World 3 is isolated.
Implication A→B consists of worlds w such that every v≥w lying in A lies in
B. F is the empty set, and T is all worlds. Use the quantifier operation
specified by the explicit table in `persistent_negation_receipt.json`; every
binder may have this same operation.

The standard-library checker verifies K/S, MP, GEN, explosion, normality,
seriality, commutation, and every instance of

```
N Q N Q A → A                         (rho6)
```

over all 16 algebra elements. For the atom P={3}, however,

```
QP = P,
NP = {0,1,2,4},
QNP = {0,2,4},
NN(QNP) = {0,1,2,4}.
```

Thus P is persistent and stable, while NP is not persistent and QNP is
not stable. Since N P is an implication into F, this also blocks the
general implication-persistence step with persistent atomic inputs.
It identifies a specific gap in that proof strategy; adding stability of
the original atom does not fix it.

This is **not** a countermodel to the complete native K/S replacement
calculus: no interpretation of all native equality/membership rows or of
the literal set-theory bundle is asserted. Those remaining axioms could
still supply additional reasoning. No negative consistency-strength claim
for the full calculus follows from this fragment example.

Reproduce with Python 3 and no external dependencies:

```sh
python3 check_persistent_negation.py
```

The explicit Q operation was discovered with SMT, but the supplied replay
uses only finite set operations and checks every claimed instance.
