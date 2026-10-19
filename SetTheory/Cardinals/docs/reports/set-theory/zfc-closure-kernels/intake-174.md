# Intake 174: an independent certificate for the 237-state fold

Placement `1c72682b2b` imports `ZFC237_Verified_Construction_2026-10-19.zip` (arrival
`17ce14c2db`) as **Source 110** (prefix `110-ver237-`) and retires its ZIP. The host now
reconciles **110 sources**; the collection remains **290 reports**. The
[placement map](data/intake174-placement.json) accounts for all 138 members: 58 staged
byte-identical (0 mismatches against a fresh extraction), 76 exact aliases and 4
archive-only (the main reports, PDFs and delivery README).

## Same machines, new certificate

The intake's canonical census finds the package's 237-state table
(`machines/zfc_extended237*`) to be **canonical `7eda1da1…`**, the table of
[Source 106](intake-173-sources.md#source-106) and of
[`candidate-composed237`](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-composed237/README.md).
Its 238-state companion (`composition238/`) is the common `909f29c4…` table. The package
says so itself. It found the 238 composition independently and then, on a late source
check, identified Source 106's report. It **credits Source 106 for the 235 → 98
reduction** and claims neither its discovery nor priority.

Its own contributions:
- **An independent all-tape certificate of the fold.** The predecessor invariant says
  that at 98 or 240 the bit to the left is 0, at 139 or 156 it is 1, and at 235 both
  preceding bits are 1. All eight incoming rows preserve it, and it is vacuous at
  start 95 on every tape. The three exceptional rows expand to blocks of 3, 5 and 3
  steps with identical whole tapes and head displacement +1, and 473 old rows are
  identities under `φ(235) = 98`.
- **A fresh two-table startup comparison**: the same full frame after 409,835 steps,
  with no exceptional-row visits during startup.
- **The complete 238-state companion**, including a six-valued K/S obstruction.

It did not import or run Source 106's direct 237 runtime checker. Its theorem goes
through the all-tape simulation from its own freshly verified 238. The batch-173 intake
had already replayed that direct runtime proof independently (2,261,369 rules).

## Consequence for the combination question

None. Three independent routes now lead to the same 237-state table: Source 106, this
package, and the batch-173 intake's rebuild. The answer of
[intake 173](intake-173.md#can-the-ideas-be-combined-below-237) stands: the delivered
ideas contain three state savings, all used by the 237 table, and the searches on that
table found no fourth.

## Non-claims (kept from the package)

No Lean/Rocq endpoint and no PA derivation for the 237 table; no global minimum; no
new discovery of the 237 machine.
