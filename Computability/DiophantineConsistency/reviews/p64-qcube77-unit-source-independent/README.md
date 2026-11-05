# Independent source review of the 77-operation unit-factor join

A read-only review on 2026-11-04 inspected the following sources:

| Source | SHA-256 |
| --- | --- |
| `P64QCube77Unit.lean` | `73e76eaa00bfcae01fa2b13a83892547c44c4aba34f58af4185920cfafe871dd` |
| `P64QCube77OldFacts.lean` | `d100eb7a6f573fbe042657f52c1de36551ad48a09a3679dc9a65209f80be60da` |
| `P64QCube77Existence.lean` | `e65822241f4308d969094f91b68a90a5c267ad82b852b3b7b68f2fad769a942a` |

The reviewed `same_zero_iff` quantifies over arbitrary natural port tuples and
requires all fourteen model coordinates to be positive. Its forward direction
uses the four nonnegative squares to obtain `M=W=Lt=0` and `A1*Na=1`. From the
transport zero and positive inputs, `first_ne_neg_of_transport` obtains
`q≥2` and `P≥2`, and applies the separately imported norm exclusion to rule
out `A1=−1`. The discrete ordered-ring unit lemma then yields `A1=Na=1`.
The reverse direction uses `P64QCube77OldFacts.residuals` for an actual 78
zero. Both directions keep the same valuation and use the actual generated
Lean graph expressions. No hidden positive-beta or external coefficient
hypothesis appears in the displayed theorem signature: the relevant
positivity follows internally from the transport equation and the given
positive witnesses.

This is a source review, not an independent Lean replay or verification of
the transitive captured provider, symbolic ports, external graph, gzip, JSON,
or PDF correspondence. It assumes the imported theorem statements and Lean's
reported checks; the author-side receipts and deeper provider evidence have
their own scopes.
