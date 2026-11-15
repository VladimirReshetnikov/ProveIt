# PA194H5XS and PA194JH5XS

These are new symmetric cache-test implementations of the incoming H5X and
JH5X witness calculi. Each table is a complete blank-start, two-symbol,
single-tape machine with 194 working states, initial state 0, and terminal
label 194. No prewritten tape is required.

The package gives an ordinary written iPRA proof of positive halting
equivalence to each pinned witness-family parent. Its absolute iPRA
nonhalting/Con(PA) calibration is inherited explicitly through the witness
packet and its retained revised AX11H proof. The proof-assistant endpoint
remains unfinished. See `symmetric_preservation.tex` and the independent
written-calibration review accompanying the main report.

The source change removes the cache-restoration transfer loop from Shift,
comparing 1 with h in place of h with 1. The command result and halt flag
agree for every clean incoming store. The source saves 0 primitive steps
when h=0, 4 when h=1, and 2h+4 when h>=2. The source programs have 3,674 and
3,680 sites. A new raw controller is absorbed with native state 41 by a
checked context fold: 135 fixed + 69 reader - 10 folds = 194 states.

Both complete blank startups reach their exact clean source frame after
57,768 tape transitions. The full source checks bind every instruction and
edge to independently generated arithmetic templates. The literal tape
checker independently rederives the four list-sweep identities and checks
all 4,782 and 4,790 source outcomes over arbitrary primary registers, an
arbitrary nonempty finite spare file, and an arbitrary nonnegative header
gap. The endpoint audit checks full-frame closure and all affine durations.

## Rebuild and verify

Python 3.10+ and its standard library suffice. Keep assertions enabled.

```sh
python3 -B verify.py --work /tmp/symmetric-witness-replay
```

Use a fresh nonexistent output directory. The replay rebuilds both tables,
byte-compares their central artifacts, checks all source contracts, checks
the symbolic AX expressions, runs the independent literal checker and
checks exact frame closure. It makes no network requests. A typical run
is dominated by symbolic tape verification and can take several minutes.

The new complete native and dense tables and fresh receipts are in
`machines/`. The preservation source is `symmetric_preservation.tex`.
The original witness ZIP is retained separately by the main deliverable;
it contains the actual parent tables, logical translations, licenses and
the revised AX11H written calibration archive.

## Provenance

The frozen grammars, folds, input controller and named source nodes are
from the incoming witness packet at ProveIt snapshot
`3c3bf00e3132d31d328a7bcfe79761ef238eced3`. The compiler, support checker and
independent tape induction engine are imported unchanged and remain
attributed in `WITNESS_PROVENANCE.json` and `WITNESS_NOTICE.md`.
The symmetric cache-test controller/fold comes from the existing AX11GHS
implementation. The new contribution is its integration with both exact
witness emitters, the complete fresh checks, source-cost identity, new
transition graphs and the combined relative proof.

The source and literal verification adapters change only explicit family
identities, expected counts/hashes and the symmetric-test flag. Their
arithmetic and symbolic tape rules are unchanged. `PROVENANCE.json`
records hashes for all imported and adapted files.
