# Attribution and provenance

The original compact proof calculus, set theory, source program and 254-state
machine remain credited to Mira-Cult. The upstream Rocq verification remains
credited to Jeff Ketchersid, and the compiler framework to Andrew James Wade.
ProveIt and its earlier incoming reports retain credit for the reductions that
produced the [240-state candidate](../candidate-rotation240/README.md). Those are the
successive source, routing and initialization reductions, the compensated fold, the
QT and transfer-plus-one loop rotations, and the predecessor-bit folds.

The three savings below 240 are credited as follows:

| Saving | Credit | Delivered in |
| --- | --- | --- |
| Source boundary: certified reparenthesization of the register source, decoder repair, split of 218 | Source 103 of the ZFC closure-kernels host | `ZFC_239_State_Construction_2026-10-19.zip` (arrival `83fd358548`) |
| Delayed erasure: fold 169 into 80 with helper `91/1` | Sources 101 and 102, found independently | `BusyBeaver239_Research_2026-10-19.zip`, `ZFC239_Companion_2026-10-19.zip` (arrival `83fd358548`) |
| Fold 235 into 98 with helper `240/1` | Source 106 | `ZFC_237_State_Construction_2026-10-19.zip` (arrival `ec480205a1`) |

The composition of the first two (the 238-state table) was found by the batch-172
intake and independently by Sources 104, 105, 107, 108 and 109. Source 110 gives an
independent certificate of the third saving and itself credits Source 106. The
intake's own contribution is limited to these:
- the composition of the first two savings;
- the replays recorded here;
- the path checker [code/check_blocks.py](code/check_blocks.py) and
  [code/make_construction.py](code/make_construction.py);
- this page.

No personal author is inferred from tool output or file names. The inherited notices
and licenses are under [licenses/](licenses/), unchanged and not relicensed. No
historical priority for the general techniques (helper-return sharing,
predecessor-bit tags, source reassociation) is claimed.
