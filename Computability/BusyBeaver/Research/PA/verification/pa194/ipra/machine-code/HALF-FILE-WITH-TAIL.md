# PA194 file scans with an arbitrary suffix

`PA194HalfFileWithTail.scanHalfBlockWithTailExact` generalizes the existing
one-block scan to files with at least one subsequent block. That subsequent
block's separator supplies the needed evenness; the residual suffix can be any
model element, and need not be blank. The theorem gives the exact elapsed
model time and the exact remaining file half.

`PA194HalfFileTwoWithTail.scanTwoWithTailExact` follows the literal state-93
and state-113 scans through two blocks to state 14. The theorem gives its exact
model clock and names the resulting right tape in terms of the complete
remaining `fileCode` tail. `PA194NinetyThreeReturnTwoWithTail` composes these
scans with the checked state-14/16 transitions and two model-length returns to
state 17. Its `ninetyThreeReturnTwoWithTailExact` theorem retains an explicit
clock and right-tape expression containing the complete residual file and its
arbitrary suffix. All values, suffixes and run lengths may be nonstandard.
The number `n` of remaining file blocks is an external natural-number
parameter; this is not a scan of a nonstandard number of blocks.

These are conditional physical segments. They do not assume the seed's 25
remaining one-valued spare blocks are blank, but they also do not yet prove a
complete second root pass, source-instruction simulation, or either PA
consistency implication.

`check-half-file-with-tail.sh` rebuilds all three modules, checks four selected
prerequisite source/object hashes, requires the three exact theorem reports,
and rejects `sorryAx`. It uses retained prerequisite overlays and does not
rebuild or independently pin their entire transitive dependency closure.
An independent [coherent replay](MODEL-HEADER-COHERENT.md) rebuilt the
machine-specific closure in a single startup-derived output directory.
