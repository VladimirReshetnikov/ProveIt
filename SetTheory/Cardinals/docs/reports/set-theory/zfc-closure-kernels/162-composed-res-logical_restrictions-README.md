# Exact finite obstructions to four cheap rho8 restrictions

The successful K215 machine retains `U <= A`. This directory records a separate investigation of replacing it by `U=A`, `U=B`, `U=C`, or `U=0` (truth).

The retained implication-only fragment has truth, modus ponens, and the corresponding instances of

`L(A,B,C,U) = ((C -> U) -> A) -> ((A -> C) -> (B -> C))`.

For each restriction, a three-valued matrix respects `truth -> truth = truth`, designates every restricted axiom instance, and preserves designation under modus ponens, yet falsifies a classical basis formula. This is an exact nonderivability proof in that fragment, not an inference from bounded search failure.

From the packet root:

```sh
python3 -B research/logical_restrictions/check_countermodels.py
```

`countermodels.json` is the certificate. `check_countermodels.py` checks all 27 assignments per schema and the displayed counterexamples directly. The separate `countermodels_restricted_rho8.py` records the small exhaustive discovery search; it is not a verification dependency and writes a freshly discovered `restricted_rho8_countermodels.json` beside itself when run.

These matrices do not interpret the quantifier/equality rows or the theory bundle. They do not prove that the corresponding full numerical theories are not equiconsistent with ZFC. A new direct calibration could still use their other axioms. No comprehensive literature-priority assertion is made.
