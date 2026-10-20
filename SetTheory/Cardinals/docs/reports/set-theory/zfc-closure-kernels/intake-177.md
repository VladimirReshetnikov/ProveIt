# Intake 177: a 235-state machine in the original calculus

Placement `746e88f2f7` imports one package as **Source 115** and retires its ZIP. The host
now reconciles **115 sources**; the collection remains **290 reports**. The
[placement map](data/intake177-placement.json) accounts for all 104 members: 72 staged
byte-identical (0 mismatches against a fresh extraction), 28 exact aliases, 1 history alias
and 3 archive-only. The history alias is `vendor/zfc236.zip`, which is Source 112's archive
byte for byte (arrival `0b5fec6980`).

## Source 115 — `ZFC235_Construction_2026-10-19.zip` (prefix `115-c235-`)

Arrival `0128d662fd`, built on Source 112's 236-state table. **A 235-state machine** in the
original calculus: canonical `4a2c6b05…`, inherited labels `d017abe4…` (start 95,
dispatcher 96, halt 254).

1. **Seven closed source rotations**, in order: right at 138/211, left at 116/134, left at
   162/116, left at 199/227, right at 227/197, right at 197/115 and right at 115/229. Every
   chunk at every stage is closed. The 6,455 operations and 8,386 guarded successors are
   unchanged; 2,524 source paths move, the DAG keeps 224 nodes, and the maximum depth
   falls from 49 to 48. Some intermediate trees have a zero run of 7; the final one has 6.
2. **A fold exposed by them.** In the final basis, old state 74 always has a 0 just left of
   the head and old state 193 a 1. Delete 193, redirect `163/1` and `229/1` to 74, and set
   `74/0 = 0 L 138` and `74/1 = 1 L 116`. Four three-step paths reproduce the four old
   transitions on every tape; the other 468 rows commute in one step.

Delivered evidence: the source certificate for every stage, two independent fold audits, the
exact startup (409,835 steps), and direct runtime proofs of the rotated 236 (2,266,171 rules)
and of the 235 (2,269,055 rules, all 470 rows). It also gives **E663**, a 663-bit equational
packet (E667 with the collapse query `N(d,d) = d` replaced by `Q(d) = d`, which has the same
derivability status). E663 has no state count.

**Intake replays** of the literal table on its own source, with the intake's checkers:

- Source 103's finite screen: 0 failures in 8,386 cases.
- Exact blank startup, sparse and dense: the complete dispatch frame after 409,835 steps.
- Source 103's unbounded runtime checker, with only its source hash pin removed:
  `UNIVERSAL_MATHEMATICAL_PASS`, 8,386 cases, **2,269,055** rules, all 470 rows. That is
  the delivered count exactly.

Non-claims: no Lean/Rocq or PA endpoint for 235; no minimality.

## Why the intake's own search missed it

The intake's search below 236 ([intake 175](intake-175.md#the-intakes-search-below-236))
compiled rotations two levels deep and rejected any intermediate source with a zero run above
6. Source 115 needs seven chained rotations, and its first stages pass through zero run 7. The
same pruning hid the 225 of batch 178.

## Consequence

The original calculus now stands at **235 states**. The smaller machines of batch 178 change
the calculus to Elliot Glazer's theory K; see [intake 178](intake-178.md).

## Attribution

Source 115's construction is its own. It builds on Source 112's 236 and on the reductions
credited as before.
