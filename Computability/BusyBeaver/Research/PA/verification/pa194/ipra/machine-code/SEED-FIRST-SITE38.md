# First seed-derived site-38 frame

`PA194SeedToFirstSite38.blankTo38` composes the literal blank-start machine's first site-27 transfer and restore with the positive site-34 branch, the site-35 increment, and the site-36 zero branch. In every PRA model it reaches the actual site-38 physical frame with gap exactly 42 and the explicitly given register file and repeated-spare suffix. Its run is expressed using four existential model-valued intermediate clocks and the named, explicit model-level site-35 and site-36 run functions. `PA194SeedToFirstSite36.reg6Zero` establishes the zero test used in that composition.

This is a finite initial physical run: no invariant for later decoder rounds, matching full source-controller trace, single coded combined clock, native iPRA sentence, or consistency implication is claimed.

Build in the following order: `PA194Site35RestoreEntryExists.lean`, `PA194SeedToFirstSite35.lean`, `PA194Site35Run.lean`, `PA194SeedToFirstSite36.lean`, `PA194Site36ZeroRun.lean`, `PA194SeedToFirstSite38.lean`. `Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/run-seed-first-site38.sh` contains the exact staged checker invocation; change its output argument to a fresh directory to repeat it. Its seed-first-gap input must be a completed run of the predecessor checker described in `SEED-FIRST-GAP.md`.

The staged checker recompiles these six modules, rejects `sorryAx` and missing axiom audits, records source/receipt/direct-import hashes, and rejects conflicting direct imports. The predecessor seed-controller, physical, and general-foundation stages are prebuilt; checking their direct overlaps and receipts does not authenticate their complete transitive closure.
