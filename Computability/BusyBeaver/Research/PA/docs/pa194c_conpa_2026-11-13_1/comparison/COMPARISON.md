# Current PA-machine comparison

## Scope and outcome

The source revision is `768c2be1a8e4d2fcf8aa3443c7b0f084d145734c` of VladimirReshetnikov/ProveIt. All **36** ZIP archives in `docs/incoming` were inspected, including nested ZIP payloads, and the direct numeric machine tables in `Computability/BusyBeaver/Research/PA` were included. Each incoming archive was checked against its exact Git blob ID. `source_archive_git_blob_ids.json` preserves those checks. The archive-level contributions, member locators, and hashes are recorded in `current_comparison.json`, `archive_census.csv`, and the compact manuscript table `archive_ledger.tex`.

There are **three supplied positive manuscript-level 194-state designs**, represented by six dense/native byte forms in two archives. A seventh 194-state table is explicitly rejected by its source packet. No accepted machine with fewer than 194 states occurs in the inspected materials. The only numeric tables below that count are small six- and nine-state test controls, not PA-consistency proposals.

The new PA194C table is different from every existing 194-state graph, including the rejected table. Exact canonical vectors were compared, with arbitrary control renaming, no distinguished start, optional left/right reflection, and even optional global symbol exchange. All five compared graphs have 194 possible roots that reach every working state. The new result is therefore more than a state-renaming or tape-reflection variant. See `pa194c_graph_novelty.json` and the replayable `compare_graphs.py`.

The source inventory contains **3,486 complete numeric table occurrences, 606 byte forms, and 596 labeled transition functions**, including repeated nested references, diagnostic tables, ancestors, and larger experimental allocations. These are inventory counts, not numbers of established consistency machines. Fourteen occurrences are direct PA-directory tables. The recognizer accepts complete numeric five-column binary tables in `.tm` and `.txt` files with one undefined halt label. Tables represented only in arbitrary source code or JSON are outside that literal-file count; the manuscript and repository reviews supplement it. The broader rooted hashes in `census.json` use documented native/dense start conventions where recognized, while the critical same-size comparison uses exact all-state canonicalization independently of those conventions.

## The three supplied 194-state constructions

| Name used here | Archive and table | Allocation | Source sites | Blank initialization |
|---|---|---:|---:|---:|
| PA194-67 | `pa194_conpa_2026-11-13.zip`, `construction/tables/pa194.tm` | 134 + 67 - 7 | 3,673 | 58,154 |
| PA194-67-AD | Same archive, `construction/tables/pa194_AD.tm` | 134 + 67 - 7 | 3,673 | 58,122 |
| PA194-68 | `pa194_conpa_2026-11-13 (2).zip`, `pa194/pa194.tm` | 134 + 68 - 8 | 3,673 | 58,154 |

The names distinguish these tables because both packets call their primary machine “PA194.” Each dense table has start 0, working controls 0–193, halt 194, and 388 rows. The table alphabet is binary, the tape is two-way infinite and initially all zero, and every transition moves L or R.

All three use the same separate 190-token axiom emitter. Direct comparison of the two primary delivered source maps shows that all **3,673 instructions and ordinal successor lists are identical**. Their compact canonical JSON has SHA-256 `b370f0b692af1ecd662c8cdeda50ef97f6f59ef38060aea1f46abeb0f1cf1eb7`. Their binary reader trees and contextual quotients differ. The A/D companion exchanges two physical register positions through three native row changes; that companion is already part of the source corpus and must not be offered as a new fallback.

The complete independent physical checks were rerun for all three. Each passed 4,780 symbolic source outcomes and complete blank-tape initialization. The 67-reader packet independently rederives four generic list lemmas from the literal table and uses no arithmetic-box oracle. The 68-reader packet checks both its raw 202-state and folded 194-state machines using the inherited arithmetic interface; its independent reconstruction is not a wholly independent proof kernel. `baseline_replay_summary.json` records the fresh outcomes without confusing the original packages’ historical novelty comparisons with the present enlarged corpus.

The primary table hashes are:

- PA194-67: `4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f`.
- PA194-67-AD: `27613aa92da79ba2ec6e2e88e0ac909fda218e06495ecc0af27201eac0e26c8f`.
- PA194-68: `9087d70fc0e1878c38ceff928e6e7e0999c86b6efed00a5ec353821c00641c87`.

## Relevant 195-state families

| Family | Logical/command choice | Reader allocation | Sites | Startup |
|---|---|---:|---:|---:|
| Original PA195 | Bundled diagonal gate, original controller | 68 - 7 | 3,700 | 58,154 |
| PA195S | Separate diagonal head, original controller | 67 - 6 | 3,673 | 58,154 |
| PA195C | Separate diagonal head, Combined controller | 67 - 6 | 3,649 | 57,922 |
| PA195DC | Bundled diagonal gate, Combined controller | 68 - 7 | 3,676 | 57,922 |
| M195S8 | Original diagonal source with eight-zero scanner | 203 raw - 8 folds | — | 59,164 |

The second 194 packet additionally contains a distinct, fully checked supplementary 195-state allocation of the separate source. The PA195DC packet retains two further 195-state implementation witnesses as research leads; it expressly separates their finite checks from its main consistency theorem. They should not be counted as additional completed consistency proofs.

PA194C uses the 67-reader/7-fold decoder and the same Combined-controller source as PA195C. The new complete source instruction array was independently compared with `pa_consistency_research/construction195/rebuilt_195C/source.instructions.json` inside the current `PA195_ConPA_research_2026-11-14.zip`. All 3,649 instructions and successors agree exactly; see `pa194c_source_identity.json`. This is the cleanest source-level proof transport for PA194C. The six-row edit relative to PA194-67 explains why the fallback changes the implementation rather than merely its labels.

## Lessons from larger designs and rejected candidates

The original U208 packets share one finite-history 172/211 fold. Their principal nine presentations give two rooted classes, while later helper variants expand the designated family to twenty classes. These are multiple routings of one reduction, not independent deletions that can simply be added together. James Chang’s PA209 is a different ancestor from the U209 used by those packets.

PA196 uses altered quantifier encoding, axiom organization, and reader allocation. The later 196-state family includes source-tree reassociations, register exchanges, Combined controllers, closing-decrement variants, scanner variants, and zero-jump routes. Several variants edit the same row, making their advertised savings mutually exclusive. The all-36 ledger records each packet’s contribution rather than treating every search table as a valid construction.

The smaller source programs provide a concrete warning against minimizing expanded instruction count alone. NEG18 reduces negation to an 18-instruction macro and the complete source to 3,441 instructions, but its supplied fully checked allocation needs 197 controls. Fewer source instructions can lose useful shared reader states or compatible folds.

The current rejected 194-state quotient has valid local fold traces and a preserved source graph, but its seven-zero source addresses violate the inherited scanner. Increasing the scanner capacity repairs the implementation at 195 states (M195S8). Thus local quotient correctness plus source identity does not suffice without complete physical runtime checks.

Other documented rejected 195 families fail 93, 714, or 777 primitive contracts, misuse the header scanner, or change the successor/register effect of a zero-jump instruction. Two rejected 196-state Shift layouts actually halt on blank input at step 43,563. These examples separate a wrong proof interface from stronger evidence of wrong blank behavior. None of the finite unsuccessful searches establishes a state lower bound.

## Proof status

The task’s endpoint is a proof **in PA** of the nonhalting/consistency equivalence. The incoming positive manuscripts provide ordinary mathematical arguments supported by exact tables, source checks, symbolic certificates, and inherited syntactic calibration. This comparison does not replace their arithmetic proof with finite simulation.

The integrated PA directory also pursues the stronger endpoint in iPRA. At the pinned revision its README explicitly says that neither machine-specific iPRA reduction for PA194, original PA195, or PA196 has yet been established. `pa194/ipra/PA194Endpoint.lean` constructs a conditional endpoint from explicit reduction hypotheses. The bounded halting and standard-model semantics modules do not remove those hypotheses. This is a formalization boundary; it is not a refutation of the ordinary PA arguments and does not introduce an iPRA requirement into the present task.

Similarly, the imported PA196 Lean endpoint includes the internal implication from literal nonhalting to Con(PA). That declaration alone does not supply its converse inside PA. Formal quotient, source, runtime, and arithmetic modules are proof layers rather than new machine designs. The current repository READMEs and endpoint source are retained in `source_readmes/` so that this boundary is reviewable.

## Reproduction

To regenerate the literal-table census against the exact pinned checkout:

```sh
python3 census.py --repo /path/to/ProveIt --output /path/to/new-census
```

The script refuses a different Git HEAD. To recheck same-size graph distinction, pass the four tables under `selected_tables/` whose names begin with `PA194` or `rejected194`, followed by the new table, to `compare_graphs.py`. It compares canonical vectors exactly before emitting SHA-256 summaries. `current_comparison.json` and `primary_families.json` provide machine-readable statements, hashes, and statuses. The comparison scripts and receipts do not assert a new Lean/Rocq theorem.
