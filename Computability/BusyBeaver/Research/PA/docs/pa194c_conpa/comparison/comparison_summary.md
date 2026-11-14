# Complete pinned PA table census and construction comparison

The final comparison is pinned to ProveIt commit
`768c2be1a8e4d2fcf8aa3443c7b0f084d145734c`. A final freshness check found two
additional incoming packets after the initial inspection at `b8823533…`;
both were read, classified, and included in a fresh full census. All 36
top-level ZIP archives in `docs/incoming` and all 14 direct PA `.tm` files
were read. Nested ZIP bodies were traversed once per byte identity, with
every reference retained. The machine construction itself is unchanged.

## Fresh counts

| Quantity | Count |
|---|---:|
| Top-level incoming ZIP archives | 36 |
| Distinct ZIP bodies, including nested bodies | 49 |
| ZIP references | 77 |
| Maximum ZIP nesting depth | 8 |
| Member occurrences in distinct ZIP bodies | 26,258 |
| Recognized complete numeric binary table occurrences | 2,519 |
| Byte-distinct tables | 606 |
| Classified action-preserving graph classes | 437 |
| Recognized 194-state occurrences / byte forms / graph classes | 7 / 7 / 4 |
| Recognized 195-state occurrences / byte forms / graph classes | 82 / 25 / 15 |
| Recognized 196-state occurrences / byte forms / graph classes | 788 / 163 / 99 |

These are counts of recognized table artifacts, including ancestors, experiments,
rejected machines, and duplicate presentations. They are not counts of proved
consistency constructions. The parser recognizes complete numeric `.tm` and
`.txt` tables with exactly two rows per working state and one undefined halt
target. Arbitrary code/JSON-embedded tables are outside this numeric census.
A four-state no-halt synthetic control is excluded by the parser; recognized
six- and nine-state synthetic controls have no root reaching their entire
working graph and are excluded from the graph-class count. There were no
archive or parse-execution errors.

`census.json` records every archive/member/hash/table relationship.
`current_census.py --repo /path/to/ProveIt --output /path/to/fresh-census`
reproduces it using the pinned commit, without checking out the repository.
The Git repository must contain the pinned commit and its referenced blobs;
missing blobs in a partial clone may require network access. This corpus
rescan is separate from the fully offline machine and novelty replays.
Canonicalization takes the lexicographically smallest read-0-before-read-1
BFS serialization over every possible root that reaches the whole graph;
it preserves read symbols, writes, movements, and halt.
`archive_ledger.csv` and `.json` give a contribution summary and exact archive
hash for each of the 36 top-level archives. The older 32-archive detailed
comparison is retained separately as `prior_comparison_notes.md`; its old
counts must not be confused with the final counts above.

## The existing 194-state frontier

1. **PA194 primary:** separate190 axiom word, original controller, 3,673
   primitive source sites, 4,780 branch contracts, 58,154-step startup.
   Allocation is 134 fixed controls + 67 raw readers - 7 compatible folds.
   Its archive provides an ordinary mathematical PA calibration and two
   executable physical verifiers, but no newly compiled end-to-end Lean or
   Rocq theorem.
2. **PA194_AD:** the same source and reader allocation with the physical A and
   D register blocks exchanged by three native row changes. Startup is
   58,122 steps. Its graph differs from the primary graph.
3. **PA194 eight-fold allocation:** `pa194_conpa_2026-11-13 (2).zip` supplies
   a further association of the same separate190 source with 134 fixed
   controls + 68 raw readers - 8 compatible folds. It retains the original
   controller and the 3,673 sites / 4,780 contracts / 58,154-step startup.
   Thirty-two local cases include one seven-step case. The manuscript and
   receipts report a positive ordinary PA calibration and complete finite
   checks. Its native hash is
   `46caf1249523f4bef64b5bba5c1d8d2c06da7417bdf8991c6b678fc636bc6037`;
   its dense hash is
   `9087d70fc0e1878c38ceff928e6e7e0999c86b6efed00a5ec353821c00641c87`.
4. **Rejected scanner194:** `near194_bad4_k17595.native.tm` in the follow-up
   archive. Its eight local folds and complete 3,700-site source CFG are
   valid, but seven consecutive zero bits in a source address are mistaken
   for a separator by the inherited scanner. The supplied negative receipt
   identifies the first failed contract as source ordinal 1003, zero branch
   of logical register 1 / physical register 2, after 1,309 earlier successful
   branch contracts. It is not a successful consistency-machine construction.

The new PA194C graph differs from all four of these graphs, even when the
initial root is forgotten and global left/right reflection is allowed.
`check_all194_novelty.py` and `all194_novelty.json` bind this fact to all seven
literal prior byte forms. Native and dense presentations of the three
positive machines account for six of those seven forms. The eight-fold
allocation's root-free graph hash is
`4be970c2361e9877f0ff7b5c74bb1629315e6bfac1feb1ebe4c953eb23f8a0f5`,
which differs from PA194C's
`b79f4d344740679b87dace02fe3f211565c2cd4513f346812570d90caa3d9a3f`.

## The 195-state frontier

The 15 graph classes divide into five principal positive manuscript families,
two retained search intermediates, two finite-verified secondary logical
variants, and six rejected or diagnostic families. `frontier_classes.json`
gives the full classification with every literal form and occurrence. These
status categories distinguish the primary claimed theorem from secondary
implementation witnesses whose logical calibration is discussed separately.

| Family | Source | Physical distinction |
|---|---|---|
| Original PA195 | Diagonal191; 3,700 sites / 4,815 outcomes | 134 + 68 readers - 7 folds |
| 195S | Separate190; 3,673 sites / 4,780 outcomes | 134 + 67 readers - 6 folds |
| 195C | Separate190 AX body, cached-head commands; 3,649 sites / 4,749 outcomes | 134 + 67 readers - 6 folds |
| M195S8 | Original diagonal191 source; 3,700 sites / 4,815 outcomes | 134 + 68 readers + 1 scanner - 8 folds; startup 59,164 |
| PA195DC | Diagonal191 AX body, cached-head commands; 3,676 sites / 4,784 outcomes | 134 + 68 readers - 7 folds; startup 57,922 |
| Crossed195 intermediate | Separate source, retained during the seven-fold PA194 discovery | 68-reader raw202 parent with seven contextual folds |
| Separate195 seed | Separate190; 3,673 sites / 4,780 outcomes; retained by the eight-fold PA194 packet | Different 67-reader/six-fold allocation from principal195S |
| Secondary rho-parameter exchange | Diagonal191; 3,700 sites / 4,815 outcomes | 134 + 69 readers - 8 folds; finite checks PASS |
| Secondary negative Gamma | 197-token negative-vacuity emitter; 3,794 sites / 4,937 outcomes | 134 + 71 readers - 10 folds; finite checks PASS |

The crossed195 intermediate occurs as `pa194_conpa/search/quotientcross.best.tm`
in the first PA194 packet. The report describes the earlier crossed
construction as validated, and its search records an exhaustively closed
192-table local quotient family with best size 195. The other separate195
seed appears under `comparison/separate195/` in the eight-fold PA194 packet;
its exact word, source CFG, 4,780 runtime contracts, and blank startup pass.
Neither is an additional 194-state construction.

The later PA195DC packet supplies the new principal diagonal-plus-cached
machine and the two secondary variants. Its main theorem uses the unchanged
191-token emitter. The rho exchange and negative-Gamma witnesses have
complete finite implementation receipts and separately discussed logical
transfers. They must not be classified as rejected tables or silently
substituted into the primary theorem without their additional calibration.

The six rejected/diagnostic classes are the two-rotation quotient, the warm
physical candidate, the extended physical candidate, seven-zero scanner
regrouping, short-scanner deletion, and the zero-jump/helper fold. A failed
claimed simulation is not in itself a proof of blank halting. Two separately
rejected 196-state Shift layouts have stronger negative evidence: the
repository contains Lean-checked blank halts at 43,563 steps.

## Why the larger machines cannot simply be subtracted from one another

James Chang's PA209 and the U209 parent of the U208 designs are different
machines. The initial U208 saving uses a history-sensitive fold in its own
architecture. Subsequent U208 presentations have many helper routings, but a
fold already present in a descendant cannot be subtracted a second time.
The published PA196 machine already incorporates changed quantifier coding,
axiom heads and ordering, and six reader folds.

The later 196-state families change source association, register allocation,
Shift and MP semantics, zero-jump routing, and closing commands. Several edits
change the same physical row. Smaller source DAGs can lose a useful physical
helper and require more controls; the 18-site negation source is a concrete
example of a large source saving without a smaller final tape machine. All
these sources are distinguished in the 36-row archive ledger.

The successful new composition keeps the verified 67-reader/seven-fold
allocation while installing the known 195C command controller. The source
map remains exactly the published 195C map, independently bound by SHA-256
`0afee1346c0931b3b91fea70571b01fd665a802ab9327409e4030f673412f5e3`.
This changes both command semantics and the expanded source, rather than
merely renaming controls or permuting the old register blocks. PA195DC uses
the same six controller changes with a different, diagonal emitter and
therefore remains a different 195-state source and physical design.

## Proof status

The existing PA directory's many PA195 quotient/runtime files are proof layers
for the same original machine. They must not be counted as separate designs.
The final snapshot also adds bounded PA194 halting and a conditional iPRA
endpoint for the primary seven-fold PA194 table. Its README explicitly says
that both machine-specific reductions remain hypotheses. The updated main
PA README states that neither direction has been established in iPRA for
PA194, original PA195, or PA196. The ordinary written PA calibration supplied
in the research manuscripts is a different proof artifact from an exported
end-to-end Lean theorem.

For PA194C the new contribution is the literal 194-state compilation, exact
parent binding, full source-map equality, complete local fold checks, two
universal physical verifications, and exact blank startup. The supplied 195C
command-calculus calibration is preserved as a reference, and the report's
positive finite-trace simulation transports its ordinary PA theorem.
No new end-to-end kernel-checked arithmetic theorem and no proof that 194 is
minimal are claimed.
