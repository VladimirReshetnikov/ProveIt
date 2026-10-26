# Two new ten-positive polynomial tradeoffs

| Exact degree | Live binary operations | Positive unknowns | Whole fixed tuple |
|---:|---:|---:|---|
| 202 | 99 | 10 | Start-only 4127, 97,046 raw bytes |
| 190 | 120 | 10 | Start-only 4127, 97,046 raw bytes |

The degree-190 construction composes the free quotient chart with an integer
polynomial center of the whole Pell product. Its new transport weight
`L=(UE)b²` has a full signed bound before rank recovery, including the
auxiliary index-three branch. Bare `b²` is not substituted into the free chart.
The whole norm defect is collected exactly; naive degree propagation would
miss the cancellation. `PROOF.md` gives both witness directions and the exact
nonzero leading homogeneous forms.

These are degree/operation tradeoffs, not simultaneous improvements or global
optimality claims. They have **ten strictly positive** unknowns, not ten
unrestricted integers. The ordinary proof is composed with the retained whole
native/refutation calibration; no new end-to-end formal-kernel certificate,
proof of consistency, or actual zero/unsolvability decision is claimed.

## Reproduction

Run `python -B replay.py` for an offline clean-copy build and complete finite
replay, including the inherited Start-only native decoder/controller checks.
For just the new component:

```
python -B build.py --check
python -B verify.py --mutations --receipt CHECK.json
python -O -B verify.py --mutations --receipt CHECK_OPTIMIZED.json
```

The checker imports no producer. It authenticates all four fixed ports and
the native certificate, checks all actual gates in exact free polynomial
rings, collects the entire quotient-center defect, substitutes all dependent
leading forms, and rejects both alternative operators at all 219 gates
(438 mutations). Normal and optimized receipts agree byte for byte.
These finite checks do not replace the unbounded mathematical proof.

The full frozen baseline, native proof, all numerical payloads and upstream
source closure remain under `inherited_positive10/`. Whole-product center
source proofs and complete source polynomial data are retained separately in
`source_centers/`, with attribution in `NOTICE.md` and pins in `SOURCE_PINS.json`.
No upstream repository, branch, PR or publication was changed.
