# A reachable obstruction to deleting detector state 74

The proposed modification is `58/0 := (0,L,84)` in the context246 table,
making old detector state 74 unnecessary. It fails 36 arbitrary-register
guard cases belonging to 18 source leaves. This note establishes that the
first such leaf is reached in the actual initialized computation; the
exceptions cannot be dismissed as unreachable guards.

## Literal finite witness

`threshold_literal_witness.py` independently replays the original machine
from the completely blank tape, then checks every exact whole-tape target
of 1,700 source instructions. At total binary time **6,012,481**, it reaches:

- Old dispatcher 96, head -9, full head-to-header distance 709.
- Stored PC `11101001001`; consumed leaf `111010010010000000`.
- Logical instruction `CD T` with T=0.
- Physical primary values `[0,0,0,4,0,0,7,0,0]`.
- 696 spare blocks, all of value 1.
- No nonzero tape cells outside the fully specified frame.

The complete support and the 1,700 exact instruction durations are saved in
`threshold-literal-witness.json`. The root is the actual context246 bootstrap,
not an arbitrarily prepared tape. Its logical initial vector is
`(3,0,0,0,3,0,0,0,0)`.

## What the modification changes

Starting from that reached frame:

| Table | Time to first complete successor frame | Successor PC | Primary values |
|---|---:|---|---|
| Original context246 | 5,738 | `11101001001000001` | unchanged |
| Shortened detector | 5,818 | `11101001001001` | unchanged |

Both T and W happen to be zero at this occurrence, but that equality does
not rescue the deletion. The modified return skips a real source-program
fragment. The original source reaches the modified PC only **146 logical
instructions later**, by which time **W=10** instead of zero. Thus the
modification is not merely a contraction of harmless zero-register tests.
The saved evidence also records the corresponding changes in header
distance and spare count.

This is a concrete counterexample to preserving the original instruction
and register-program semantics on reachable frames. It does not, by itself,
decide the modified machine's eventual behavior or prove that every possible
new logical calibration is impossible. Any defense of that machine would
need a different, explicit program interpretation and a new completeness
argument; the existing unchanged-source endpoint cannot be reused.

## Reproduce

Run from the session scratch root:

```sh
python3 -B agent-proof/threshold_literal_witness.py
```

The smaller `threshold_reachability.py` also finds the same bad leaf from
several safe roots. In particular it is reached after 1,112 source
instructions from the all-zero root. These auxiliary source runs are
secondary to the complete literal witness from the actual context246 blank
initialization.
