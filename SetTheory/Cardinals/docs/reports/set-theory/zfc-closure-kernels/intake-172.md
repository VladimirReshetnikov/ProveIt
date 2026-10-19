# Intake 172: two 239-state savings, and their 238-state composition

Placement `07194e5b4d` imports the three packages of arrival `83fd358548` as
**Sources 101–103** and retires their ZIPs from `docs/incoming/`. All three are
pinned to ProveIt `13ec39ed43148b1807f51ed6e6528e1c84659562` and continue the
[240-state candidate](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-rotation240/README.md)
of Source 80. The host now reconciles **103 sources**; the collection remains **290
reports**.

The [placement map](data/intake172-placement.json) accounts for all 562 members.
377 are staged byte-identical (0 mismatches against a fresh extraction) and 175 are
exact aliases of blobs already in the tree. The other 10 are archive-only: each main
`report.tex`, every PDF and each delivery README. [Reproduction](intake-172-reproduction.md)
describes recovery and the fresh runs.

| Source | Package | Machine | Saving | Reason retained |
| --- | --- | --- | --- | --- |
| [101](intake-172-source-101.md) | `BusyBeaver239_Research_2026-10-19.zip` | 239, `4447a242…` | delete 169; `80/0`, `91/1`, `147/0` | guarded fold with a changed shared-helper return; 946-bit equational packet; variants; permutation census |
| [102](intake-172-source-102.md) | `ZFC239_Companion_2026-10-19.zip` | **the same** 239 table | the same edits, found independently | independent local proof and guard; logical-basis obstructions; NIP source specialization; alternate 240 layout |
| [103](intake-172-source-103.md) | `ZFC_239_State_Construction_2026-10-19.zip` | 239, `666f5bf1…` | reparenthesized source, decoder repair, 218/223/179 split | a different saving, proved for every tape at the start state |

## Two savings, one table repeated

Sources 101 and 102 deliver **byte-identical** tables, with canonical SHA-256
`4447a242…` and inherited SHA-256 `76a9574a…`. They found them by different searches and
proved them by different local arguments. Source 101 uses four guarded blocks; Source
102 uses six comparisons. Both certify the same runtime guard on the old machine, and
both give a direct unbounded runtime proof of the new table. The table is stored once.
Both packages keep their credit, and neither repeats the other's further research.

Source 103's saving is different in kind. It changes the register *source*, by a
certified reparenthesization that keeps every instruction occurrence. It then repairs
the decoder and splits one decoder state by the bit behind the head. Its fold holds
for every tape, with no runtime guard.

## The combination: 238 states

**Intake finding (not claimed by any source).** The two constructions edit disjoint
rows, and they compose.

- The delayed erasure changes `80/0`, `91/1` and `147/0` and deletes 169. Its blocks
  run through 18 further states.
- The boundary construction changes 40 retained rows of 23 states, between 61 and 237,
  and deletes 218.
- None of the delayed erasure's rows or block states, nor any incoming edge of 67, 80,
  91 or 169, changes in the boundary table.

Applying the delayed-erasure edits to the boundary239 table gives a **238-state** table:
canonical SHA-256 `909f29c4…`, inherited `ab1f12ce…`.

Disjointness is only a heuristic, because the delayed-erasure guard is a property of
whole runs. The table was therefore checked on its own terms, against Source 103's
reparenthesized source:

| Check | Result |
| --- | --- |
| Direct unbounded runtime: Source 103's checker, unchanged | `UNIVERSAL_MATHEMATICAL_PASS`: 8,386 cases, 2,255,513 rules, all 476 rows, minimum duration 13 |
| Exact blank startup: sparse run and dense replay | full initial frame after 409,835 = 409,691 + 144 steps |
| Local fold boundary239 → 238 | invariant on 121,024 windows; 22 admitted block windows; 474 commuting rows; blank prefix matched checkpoint by checkpoint |
| Guard on boundary239 over all runtime frames | PASS: 8,386 cases, 32 symbolic 169/read-1 visits with right-hand 1-run constant ≥ 23, 6 blank-prefix visits |
| Positive controls | boundary239 reproduces 2,247,513 rules; the fold driver reproduces Source 101's 121,536 windows |
| Negative control: without the `91/1` change | `NOT_PROVED` at the 49th case |
| Source 103 quick replay, fresh copy | 8/8 PASS, including the source certificate and the Lean source/seed identification |

The table, receipts and drivers are published as
[`candidate-combined238`](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-combined238/README.md).
Its status matches the 239 packages: an ordinary mathematical argument with unbounded
executable certificates, composed with the inherited source calibration. It is **not**
a Lean or Rocq theorem, nor an internal PA proof. No minimality is claimed.

## Proof status, read separately

The checked Lean endpoints remain those already in the tree: the external endpoint
for the 240-state candidate, and its internal PA formalization in progress in the
Claude lane. Neither 239 table nor the 238 table has one. No import supplies absolute
consistency, unconditional non-halting, a global lower bound, or two-sided independence
from bare consistency. The search counts, bit counts and compiler outputs keep their
stated scopes. In particular the 946-bit equational packet and the 281-state diagnostic
compiler outputs carry no binary state count.

## Leads for a further saving

These are recorded from the sources, not claimed:

- **NIP specialization** (Source 102): the source shrinks to 6,449 leaves, but the
  binary layout's state-72 route still needs repair.
- **Alternate 240 layout** (Source 102, `cluster_variant1`): source depth 48, the same
  depth as Source 103's reparenthesized source.
- **Register permutations** (Source 101): swap (0,1) gives a clean all-zero logical
  frame after 68,835 steps. The fold searches on the 19 simply safe permutations found
  nothing, which is not a lower bound.
- **The methods themselves**: the shared-helper-return change and the
  split-by-bit-behind-head have each been applied once. A search for further
  applications on the 238 table is the natural next step.

## Attribution

The original calculus, source and machine remain credited to Mira-Cult; upstream
verification to Jeff Ketchersid; compiler work to Andrew James Wade; the preceding
reductions and calibration to ProveIt and its incoming reports. Sources 101 and 102
share the delayed-erasure fold, found independently. Source 103 contributes the source
boundary construction. The 238-state composition and its checks are intake work.
