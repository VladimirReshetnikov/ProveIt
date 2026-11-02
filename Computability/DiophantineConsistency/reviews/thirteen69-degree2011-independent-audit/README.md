# Independent 2011-port degree audit

The independent [audit](audit.py) actually exited 0; its [receipt](CHECK.json)
and [terminal observation](terminal-observation.json) bind the result. It
checked the pinned source definitions and prior external row-audit receipt,
reran the author's degree checker with actual exit 0 and identical receipt,
and confirmed optimized Python was rejected with actual exit 1. It did not
rerun Lean or prove a theorem inside Lean.

The audit uses a second degree argument independent of the author's sparse
leading-form implementation. Tropical degree propagation bounds the full
69-row polynomial by 174, except for the main norm where it checks the exact
row structure and uses the identity

```
(X+ac+γH)² − (a²+H)c² = (X+γH)² + 2ac(X+γH) − Hc².
```

This yields degree at most 18 for that norm and thus the 174 upper bound.
A second propagated bound shows that every monomial involving K, MC or MF
has degree at most 173. This makes the top-degree part independent of those
three port values. Taking all thirteen variables equal to t and setting those
three ports to zero, direct univariate arithmetic modulo 1,000,000,007 gives
the coefficient of t^174 as 737305404, nonzero. Beta is the *actual* fixed
2011 beta 2^(47·2011)−1, with residue 878756698. Therefore the polynomial
at the full actual 2011 tuple has degree exactly 174. Replacing each variable
by itself plus one preserves its top homogeneous part and degree. The
author's distinct selected-monomial check and its nonzero residue are
retained in the pinned author receipt.

The source-defined full tuple is `(beta, K, lowPort, highPort + beta)`,
with K defined as `rawWord radix`. The sensitivity bound means the numeric
values of K, lowPort and highPort do not need to be evaluated for this
degree conclusion. The prior row binding is an external source check, and
this result does not establish PDF binding, exact displayed numeral size,
the all-model carrier converse, port calibration or an iPRA proof.
