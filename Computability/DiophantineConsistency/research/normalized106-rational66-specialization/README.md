# Rational specialization of the 66-row 106 evaluator

For any integer port tuple `p` with `p 0 ≠ 0` and any 14-coordinate integer
valuation, `rational_value_eq` identifies the 66-row rational evaluation
with the rational cast of the checked 67/106 integer syntax evaluation.
The fixed leaves are `Urank = (p 3 : ℚ)/(p 0 : ℚ)` and
`Wrank = (p 2 : ℚ)-(p 3 : ℚ)`. `positive_zero_iff` gives both directions
for existence of strictly positive integer zeros, using the same valuation.
The client separately proves that the expression's ring evaluation on
rational casts agrees with casting its integer evaluation.

This is an external Lean theorem, conditional on nonzero beta. It has not
yet been specialized to the actual ports and does not create an internal
rational-leaf sentence or a 66-operation integer-leaf equation. The
underlying full graph identity and historical 106 syntax provider are in
`../normalized106-rational66-lean/`.

Attempt01 passed, Lean and runner exit 0, no warnings or `sorryAx`; all
three reports list `[propext, Classical.choice, Quot.sound]`. The run used
`-M2800`, 120 seconds, sampled 3.5 GiB group RSS and 10 GiB available
memory limits, nice 19 and idle I/O. It took 1.759 seconds; peak sampled
RSS was 1,976,213,504 bytes and minimum available memory 18,893,180,928
bytes. Direct inputs, the prior successful receipt, and the stage-078
producer's recorded direct-input/companion guards were stable. The
`ModelCarrierSyntax.olean` output itself was directly guarded by the
predecessor 66/67 check, not directly re-guarded by this specialization.
Outer session 24944 was separately observed to exit 0. Historical transitive/package/dynamic ancestry and sampled
monitoring are inherited limits; the fresh current14 base was not mixed
into this search path.

The output object is
`/tmp/normalized106-rational66-specialization-priority-check01/Normalized106RationalSpecialization.olean`,
SHA-256 `3efc847b71b735789230892c2929879672a2f4042acae0daab4b88c8aa3cff07`.

| Artifact | SHA-256 |
| --- | --- |
| `Normalized106RationalSpecialization.lean` | `f4e4f191815ea9a826b1aeaac3fdfe3119b18aea30f7e919b7618bad11c71d2b` |
| `check01.py` | `65e787ead46775ff5261010b70f09c267cbd275c2d6c53a6db2452b7e36c7cd0` |
| `observations/attempt01/compile.log` | `5e22e95d8158c52d7e9fae7bd921bd5d41bcdb2b718076420a45c87bb06cebb9` |
| `observations/attempt01/result.json` | `c3aac61e3de7684d63cac156e9b784cefa16dda0835dfd0775282d67ed612124` |
| `observations/attempt01/outer-terminal.json` | `a688283eff351eea54d8c469644544bb449181917fe6aab9b12cb5a50d46a036` |
