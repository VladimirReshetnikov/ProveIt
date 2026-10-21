# Machine-side research handoff

## Accepted local transformation

`build_provider_v3.py` constructs the five-row provider variant of the pinned
K215 baseline, with unchanged source and 215 declared working states.
`provider_base_v3/proof.json` contains the six exact whole-tape local joins
(the first changed row has two guarded cases). Its output table hash is
`da20914ad9bda3f75de0381f2c05a7b5e67d26199b57b870a5ea3b72511ab627`.

| Native row | Baseline | Provider variant |
|---|---|---|
| 13/1 | 1L31 | 1L81 |
| 27/1 | 0L40 | 0L302 |
| 83/1 | 0L42 | 0L57 |
| 156/1 | 1R176 | 1R52 |
| 198/0 | 1L40 | 1L54 |

The guard at13/1 follows from all two-edge predecessor histories: either the
previous cell is1, or it is0 and the preceding cell is1. In the latter case
the replacement takes four transitions instead of two; in the former both
take three. The other four replacements take two transitions in both tables,
and their neighbor guards follow from the unique incoming write. Every macro
has positive duration, equal final state/head/whole tape, and no changed row
in its interior. Start0 cannot encounter13 before the two-edge guard applies.
The resulting stuttering bisimulation transfers blank-tape halting equivalence.

The complete new census is in `engine_provider_v3_census.json`:6176 guarded
cases,1,699,668 symbolic rules,142 protected engine rows in80 states. The
baseline census has144 rows in80 states. The removed engine rows are31/0 and
42/1. These are synthesis filters; the parent separately reran the complete
primitive proof and startup check on the exact table.

## Restricted negative results

None of the following establishes a lower bound or rules out a214-state
machine. Each statement concerns only the displayed search grammar.

| Search class | Scope/result |
|---|---|
| One-row contextual folds, baseline | 133 pairs,56,658 specifications; no candidate |
| Same search after provider rewrites | 138 pairs,58,788 specifications; no candidate |
| Direct contextual decoder contractions | 26,896 directed contractions; no candidate |
| Generic finite-window contractions | 45,796 state pairs at each history depth1–4; radius4, up to96 transitions; no sufficient local join |
| Closed source associations | 625,413 distinct baseline sources in120seconds, best202DAG nodes; 380,470 cache-MP sources in60seconds, best202 |
| Simultaneous two-fusion selector synthesis | 72 eligible pairs;3 pairs admit a freshly synthesized helper, but no two share one compatible helper |
| One fusion with an existing state repurposed as helper | 2,514 specifications;1,121 pass all source prefixes;336 also pass primitive delivery-class filtering; all336 are rejected by quantified block or primitive derivations |
|201-node transfer/cache source allocation | All32 one-state nonpure unfixes fail; simultaneous singleton-leaf unfixing fails on both direct-left/right sources, while baseline controls allocate215 |

The full336-trial experiment has a portable CLI reproducer at
`portable_research/search_contextual_fusions.py`. Its arguments identify the
literal baseline table, source, engine filter, legacy state mapping, selected
case witnesses, and support/runtime module directories. It does not depend on
the original workspace path. It records hashes of all those inputs, writes
each changed-row recipe and rejection reason, and emits actual trial tables
only when requested with `--keep-trials` (or if an unaccepted survivor exists).
A source-prefix pass does **not** validate primitive delivery or semantics.

The engine-row witnesses in `engine_row_witnesses.json` select exact quantified
cases for the rejection filter. Selecting two cases is not an acceptance
test: a successful trial would still require every6176case plus startup.
Every trial here fails at least one quantified derivation, so none is released
as a214 candidate. Failure of this checker means no theorem was established by
its rules; it should not be described as a proof that each arbitrary table
cannot possibly have the desired blank-tape behavior.

## Useful allocation diagnostic

Temporarily relaxing any one of26/0,26/1,37/0,302/0 allows a215-state structural
allocation of the201-node direct-left transfer/cache source. These are **not**
validated machines; the relaxed rows are real engine obligations. The exact
recipes are in `relaxation_diagnostic/result.json` and its referenced trials.
Moving26/0's engine continuation from37 to163 or194 preserves its guarded
engine two-step behavior, but tested reallocations still failed. Moving26/1's
continuation to42 likewise did not solve the allocation.

A tempting38→42 contraction is explicitly rejected. State42 is also the
source node(CI6,CC2) on181 prefixes. Overwriting42/1 to absorb38 destroys the
CC2 delivery; the fresh runtime proof fails at source site15. The rejected
trial directory is intentionally named and marked and must not be included
among accepted candidates.
