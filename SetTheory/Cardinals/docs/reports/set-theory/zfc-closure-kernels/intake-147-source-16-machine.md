# Batch 147 engineering review

Verdict: retain the attributed source-preserving compression and new codec as
research additions. All fixed and optional machine replays pass. **None of the
three emitted reduced calculi remains a calibration candidate at current HEAD**:
the reviewed finite-sort obstruction applies to their actual formula stacks.
This stronger current diagnosis supersedes the delivery's older C/G-gap wording;
it is not an unconditional nonhalting theorem about the literal tables.

Source: `/tmp/zfc-intake-147-yj1reoca/original/zfc_small_machine`, arrival
`9439d775aa`; verification copy: `/tmp/zfc-review147-engineering-fe87fx4s/package`.
Reviewed all four machine scripts, machine README/notices, fixed/search records,
emitted source contracts, bottom-three codec and the relevant logic/experiment
sections. Main ProveIt pin is `96836f9eea3540e96322c3d28c7127a582aae223`,
upstream `297ab8df7e5de329605c3875b4934643b371a5e3`.
The independent theory/checker/PDF review is owned separately by root.
No repository edits, checksum-manifest audit, Coq or Lean build occurred.

## Actual program changes

The original-row C/G/V control is **254=192+62**, a Wade regeneration of an
edited equality-free program, not Mira-Cult's published optimized 254 table.
Its exact 138-macro word contains GEN, rho8, QI, commutation, **original rho6**,
and `V AND (C AND G)`, with the original reads, cleanup and `c != a,b` gates.
Here **V is inherited freshly gated atomic membership vacuity**, not a newly
implemented quantifier repair. Same-variable specialization is tested only as
an extra countermodel control and is not emitted by any delivered table.

The new weighted Re-Pair counts actual nonoverlapping occurrences of equal-token
pairs, avoiding premature termination on overlaps. Seed 7/exponent 4 gives
19 productions and 67 residual tokens, preserves the complete macro word
before and after backend sharing, and emits **250=188+62** states. The source
checks all 19 original macro roots have zero escaping break/continue levels.
That supports the stated ordinary partial-transformation composition argument.
It does not prove arithmetic termination, compiler/initializer correctness, or
formalize the optimizer. Unlike the preceding 248/270 deliveries, **no finite
operation-bisimulation certificate is included here**.

The genuine-Bottom variant changes only membership arithmetic from `3P+1`
to **`3P+4`**, reusing the existing add-four helper. Truth remains 0, primitive
Bottom and the halting target remain 1, implication is `3P` and forall is
`3P+2`. Pairing and proof-stack encoding do not change. Atom `Rel(0,0)` becomes
code 4; it is no longer the negation target. Every natural still has one
canonical decoding, with the sole recursive Truth→Truth normalization.
The label-bound proof survives the larger atom offset. This is a useful
new numerical representation, independent of calculus completeness.

That constructor change makes one extra helper state reachable:
**251=189+62** for C/G/V. The PSC lane uses fresh `k=c+2` and its separately
specified 138-token word, seed 93; it emits **252=190+62**, matching the prior
four-tag genuine-Bottom PSC count. Both genuine-Bottom winners pass all
225 small register-constructor contracts, including preservation of the other
registers. These are finite arithmetic regressions, not unbounded macro proofs.

Each named output has exactly one missing row, `1.inc/read1`. It is normalized
to write1/R/halt with no extra working state. Independent named/numeric parsers
check the complete bijective relabelling, every original action and the unique
added row; halting and tape are preserved under the missing-row convention,
with a possible final head displacement.

| New table | States/rows | Total-table SHA-256 |
|---|---|---|
| C/G/V, relative falsity | 250/500 | `c252ede1eb26d9fe0cd801074dda373e050f211dc57fad05e46e06129ae7cd42` |
| C/G/V, genuine Bottom3 | 251/502 | `130d73236cd3a38cd5decc860c85f3ee27986b4d55d8568b917e9773d95e7a01` |
| PSC, genuine Bottom3 | 252/504 | `f98ea6c516877d8c44bcf38659bcaa9223d954c2e64e09bf56700bccbd0baa6b` |

## Current countermodel applies to the actual source

`source-contract.json` records an independent exact symbolic AST comparison of
the emitted C and G with the already-reviewed heterogeneous-sort model's C and
G definitions, plus the complete emitted row-stack comparison. No equality row
or general substitution rule was accidentally retained in these tables.

The finite-sort proof in current `typed_countermodel.md` therefore applies to
the relative-falsity 250 source unchanged. For Bottom3, every matrix label is
still below matrix code c, while Bottom is constantly false. All quantifiers
range over their own nonempty finite sort; original rho6, QI, commutation,
atomic vacuity, GEN and MP remain valid. The C/G proof uses only that freshness
bound, the same gates and the same formulas. Consequently it also validates
the 251 source, while primitive target Bottom remains false.

For the PSC lane, `k=c+2` is above the output slot 1 and all matrix labels.
Its finite global output range has an exact representative in that higher sort,
which satisfies closure and support. The package also gives a simpler separate
identity-quantifier algebra for the **exact fixed-slot PSC** template: only
Rel(0,1) is true; the local-bound/closed parts become not(phi), support is true,
and the complete wrapper is true. That algebra validates same-variable UI,
explosion and optional IR while falsifying cross-variable instantiation; a
whole-wrapper alpha permutation can fail, matching its deliberately narrow
fixed-slot claim.

The generic quantifier diagnostic is correct and scoped to the logical
fragment. Its independently assigned atoms are not asserted to model C/G.
The stronger current C/G conclusion above instead uses the reviewed finite-sort
construction. Same-variable specialization is true in that construction too.
Replacing F by genuine Bottom removes the alias and capture issue, **without
restoring the missing cross-name identification/instantiation strength**.

Induction excludes target1 from each intended abstract enumerator. Literal-table
nonhalting remains conditional on the unproved simulation and initialization
interfaces. No claim that a finite diagnostic run proves nonhalting is needed.

## Reproduction

All execution used the fresh copy. The scratch
`run_without_hash_enforcement.py` applies a narrow AST transform **only in
memory**: digest comparisons are bypassed, the snapshot-manifest binding is
empty, and the fixed-winner state-count check remains active. Imported frozen
source/spec digest enforcement is similarly bypassed. Output hashes are still
recorded as artifact identifiers; no checksum manifest was audited. All
formula, arithmetic, macro-word, state-count, parser, action and normalization
checks remain active. The untouched package sources are unchanged on disk.

Run from the copy's root, using `uv run --no-project python` and the scratch
runner before each script:

| Script/arguments | Outcome |
|---|---|
| `machine/reproduce.py --output ../fixed-replay` | PASS. All nine generated named/numeric/map files equal the delivered files. The only reproduction-metadata difference is `verified_input_files=0`, because manifest enforcement was intentionally bypassed. |
| `machine/old_rho6_grammar_search.py --repo machine/proveit_snapshot --output ../search200 --seeds 200` | PASS. Entire metadata, cost distribution and eight minimizing seeds exactly match delivery; minimum250. |
| Same with `--output ../search2000 --start-seed 200 --seeds 2000` | PASS. Entire metadata and all120 minimizing seeds exactly match; minimum250. |
| `machine/bottom3_measurement.py --repo machine/proveit_snapshot --output ../bottom3-search200 --seeds 200` | PASS both lanes. Entire metadata matches; C/G/V minimum251 at the same eight seeds, PSC minimum252 only at seed93. |

The 2,200 relative-falsity samples contain no table below250; the 200-seed
Bottom3 C/G histogram is exactly the first relative histogram shifted by one.
These are sampled-family minima, not lower bounds.

Independent current conservative audits of all three numbered tables also
passed. Every working state is graph-reachable, exact step bisimulation has
only singleton classes after11 refinement rounds, and radius4/64 local steps
find no safe state merge. The auditor's11 regression cases passed once.
No operational blank prefix was needed for these finite action/graph checks.
Records: `audit-cgv250.json`, `audit-cgv251.json`, `audit-psc252.json`.

All replay logs, `comparison.json`, `source-contract.json`, recorded in-memory
bypasses and the joined `engineering-review.json` remain in this review
directory. No new endpoint or state-bound theorem is supplied.

## Actionable continuation

Preserve the overlap-safe grammar optimizer and genuine-Bottom codec as
independent components. Apply exact-word compression to a **complete** source
frontend, such as the unchanged original-equality program or the restored EPSC
control, then export its DAGs/operation relation for the generic register proof.
Do not spend further effort optimizing these unchanged incomplete calculi as
consistency targets. A replacement equality-free frontend must implement or
prove general capture-safe instantiation/renaming; adding same-name UI or
explosion is insufficient. Removing the Truth sentinel could avoid the codec
normalization collision, but would change padding and the halt comparison and
has no emitted state measurement in this delivery.
