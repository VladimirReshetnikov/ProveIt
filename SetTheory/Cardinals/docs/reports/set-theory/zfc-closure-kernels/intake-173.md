# Intake 173: one 238-state table five times, one 237-state fold

Placement `197ce3dc67` imports six packages as **Sources 104–109** and retires their
ZIPs from `docs/incoming/`. One arrived in `1cba633ec3`, the other five in
`ec480205a1`. All six read ProveIt at `ce192939372ac7944fe2a0208c68a96d49fb5e3b` and
take as inputs the batch-172 packages ([Sources 101–103](intake-172.md), pinned to
`13ec39ed43`). The host now reconciles **109 sources**; the collection remains **290
reports**.

The [placement map](data/intake173-placement.json) accounts for all 1,162 members. 358
are staged byte-identical (0 mismatches against a fresh extraction) and 783 are exact
aliases of blobs already tracked, largely the batch-172 packages re-shipped as inputs.
The other 21 are archive-only: each main `report.tex`, every PDF and each delivery
README.

| Source | Package | Machine | Further contribution |
| --- | --- | --- | --- |
| [104](intake-173-sources.md#source-104) | `ZFC238_Research_2026-10-19.zip` | 238 (`909f29c4…`) | 921-bit equational packet; negative displaced-head quotient search on the 238 table |
| [105](intake-173-sources.md#source-105) | `ZFC238_Construction_2026-10-19.zip` | 238 (`909f29c4…`) | broader source-associativity criterion; a depth-39 source; obstruction to removing the fourth logical input |
| [106](intake-173-sources.md#source-106) | `ZFC_237_State_Construction_2026-10-19.zip` | **237** (`7eda1da1…`) | the 238 composition, then the all-tape fold 235 → 98 |
| [107](intake-173-sources.md#source-107) | `zfc238-composition-20261019.zip` | 238 (`909f29c4…`) | 713-bit equational packet (complemented witness, factored closure) |
| [108](intake-173-sources.md#source-108) | `ZFC238_Construction_2026-10-19 (1).zip` | 238 (`909f29c4…`) | equality-free derivation of membership congruence H3 from one collection matrix |
| [109](intake-173-sources.md#source-109) | `ZFC_238_State_Construction_2026-10-19.zip` | 238 (`909f29c4…`) | 937-bit packet; a rejected 238 rotation with its exact tape discrepancy |

## The five 238-state tables are one table

The intake put every delivered table of 236–239 states into canonical form (start 0,
the other states in sorted order) and grouped them. **All five 238-state packages
deliver the identical table, canonical `909f29c4…`**. It is the composition of the
delayed erasure (Sources 101/102) with the source boundary (Source 103). This intake
published it from batch 172 as
[`candidate-combined238`](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-combined238/README.md).
Five packages and the intake reached it independently. Each package re-proves the
delayed erasure's 169/read-1 guard on the changed source, over 8,386 cases and
2,247,513 rules. Source 107 states the constant, a right-hand 1-run of at least 23,
which matches the intake's own check.

## The 237-state table

Source 106 then deletes inherited state 235 and merges it into 98:

| Row | 238 | 237 |
| --- | --- | --- |
| `98/0` | `0 R 113` | `0 L 240` |
| `139/1` | `1 R 235` | `1 R 98` |
| `156/1` | `1 R 235` | `1 R 98` |
| `240/1` | `1 R 99` | `1 L 87` |

Three exceptional old steps become positive blocks of 3, 5 and 3 steps. An inductive
predecessor invariant from state 95 supplies their guards on **every initial tape**,
so, unlike the delayed erasure, this fold needs no runtime guard. The package also
gives a direct unbounded runtime proof of the 237 table: 8,386 cases, 2,261,369 rules,
all 474 rows. The new exceptional rows are not used during startup, which takes
409,835 steps as for the 238.

The fold came from a finite discovery search (the three C++ programs of Source 101,
applied to the 238 table). The search found exactly one candidate in its class. Its
acceptance rests on the separate all-tape local proof, not on the search.

## Can the ideas be combined below 237?

**No delivered combination gives fewer than 237 states.** The six packages contain
exactly three distinct state savings: the delayed erasure (169), the source boundary
(218) and the 235 → 98 fold. The 237 table already combines all three. Every other
contribution is either an equational packet, which carries no binary state count; a
source-level or logical simplification without a compiled machine (H3 from collection
and so possibly no `rho3` row; the depth-39 source; the broader associativity
criterion); or a negative search.

The intake also iterated the discovery methods once more:

- **Source 106's discovery search, iterated on the 237 table.** On the 238 table the
  intake's rerun reproduces the delivered receipt exactly, including its single
  candidate, 235 → 98. On the 237 table the same search finds **0 candidates**: 27,966
  state pairs and 651,775,278 helper checks over a fresh profile of 28,414 state/window
  pairs.
- **The same search on variants.** Source 101 also delivered the delayed erasure with
  row `80/0` going to 12 or 142 instead of 106. The 238 variants built from these admit
  **only** the 235 → 98 candidate. The corresponding 237 variants admit **none**.
- **Source 103's all-tape fold search** (pair, block and delete modes; window radius 9,
  fuel 101) finds **0 reductions** on the 237 table, over 12,059,883 abstract
  configurations. It also finds none on the 238 table, so this simpler class does not
  even contain the 235 → 98 fold, which needs a coordinated helper-row change.

Within these two discovery classes the 237 table has no further fold. The remaining
leads are source-level and need a recompiled decoder:
- Source 108's H3 derivation, which might allow deleting the numeric `rho3` row;
- Source 102's NIP specialization, whose binary state-72 route is still unrepaired;
- Source 105's depth-39 source and broader associativity criterion, under which no
  223-node source has been found.

These are finite searches in restricted classes. Their negative results are not
lower bounds.

## Proof status

As for batch 172, all of these are ordinary mathematical arguments with executable
certificates, composed with the inherited source calibration. No 238- or 237-state
table has a Lean or Rocq endpoint, and none has an internal PA proof. No package claims
minimality. Actual non-halting follows only under Con(ZFC).

## Attribution

The machine and calculus credits are as in batches 170–172: Mira-Cult, Jeff
Ketchersid, Andrew James Wade, and ProveIt with its incoming reports. The 238
composition was found independently by Sources 104, 105, 107, 108 and 109 and by the
batch-172 intake; the 235 → 98 fold is Source 106's.
