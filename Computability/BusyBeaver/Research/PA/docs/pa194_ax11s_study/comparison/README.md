# Comparison scope and reproducibility

This comparison is pinned to ProveIt commit `1c9524d8bf2e0a27b9a16ff622359927f536e663`. It covers the retained files under `Computability/BusyBeaver/Research/PA` and all eleven ZIP archives currently under `docs/incoming`, including recursively nested ZIPs. The delivery ledger records all 61 filed PA research packets plus those eleven incoming archives: 72 deliveries. Every delivery's top-level README was reviewed. The ledger attributes the supplied mathematical and computational claims; it does not certify every historical consistency argument.

## Counts and reconciliation

| Quantity | Count | Meaning |
|---|---:|---|
| Reviewed deliveries | 72 | 61 filed packets and 11 incoming archives |
| Tracked candidate files | 10,171 | Files with the recognized literal/JSON/archive extensions at the pinned revision |
| Literal files examined | 5,820 | Includes members of distinct ZIP payloads |
| JSON files examined | 9,400 | Includes members of distinct ZIP payloads |
| Recognized table occurrences | 3,422 | Successful literal/JSON table decodings |
| Distinct raw table byte forms | 772 | JSON tables are serialized as normalized rows |
| Distinct labeled transition tables | 752 | Sorted numeric rows, before state renaming |
| Component fingerprints | 643 | Includes five nonspanning diagnostic objects |
| Complete spanning graph classes | 638 | Some root can reach every working control in the action graph |
| Complete spanning 193-state classes | 53 | Rejected runtime prototypes or the rejected coefficient-three calculus |
| Complete spanning 194-state classes | 82 | Includes reported constructions, auxiliaries and rejected tables |
| Archive occurrences / distinct ZIP payloads | 37 / 25 | Duplicate archive payloads are traversed once and their aliases recorded |

The historical repository index reports 535 classes and 7,130 originally delivered `.tm` occurrences. Those numbers describe a different indexing scope and are not replaced by the new occurrence count. The present recognition process recovers 533 of those 535 class identities and adds 110 component identities. The two excluded historical entries are recorded, with exact paths, in `corpus_reconciliation.json`:

- `pa196_research_2026-11-13/search/local_folds/synthetic.tm` has four controls and no external terminal target. It is a diagnostic graph.
- `pa194qns_research_2026-11-13/research/additional_reductions/nested2_experiment/nested2/fixed.native.tm` has 133 literal controls (130 maximally reachable) and external targets 254 and 2000. It is an incomplete fixed component.

Recognition requires exactly one external terminal target. For nonspanning tables, the repository's `table_class` convention identifies a maximum reachable component rather than the complete disconnected table. Thus the 643 component identities must not be described as 643 spanning machines. The extra apparent 194-control object has maximum reachable component size three; it is excluded from the 82-class spanning frontier. Its full disconnected table remains represented in the occurrence ledger.

The complete extended canonical tuples of the 82 spanning 194-state classes in the fresh census agree exactly with those in `frontier194.json`. This is recorded in `corpus_reconciliation.json`; both missing and extra sets are empty. The standalone novelty checker independently reparses all 82 frozen representative tables and recomputes every extended canonical tuple.

## Recognition and attribution boundaries

`rescan_corpus.py` accepts complete numeric five-column tables in `.tm`, `.txt`, `.csv`, and `.tsv` files. It also recognizes explicit JSON row arrays, row records, paired or flat action lists, numeric action dictionaries, `(state,read)` action dictionaries, and whole table text embedded in JSON. States and terminal labels are nonnegative integers; tape symbols are binary; each control has exactly two transitions. Moves are `L`/`R`, with numeric `-1`/`1` also accepted in JSON. Embedded one-control JSON fragments are excluded to avoid treating isolated transitions as machines; literal one-control tables are included.

A final numeric-direction prefilter audit fully decoded the 90 additional JSON candidates admitted by the widened filter and found no further tables. Its receipt is `census/json_prefilter_audit.json`; the corpus counts are unchanged.

The scan does not execute generators or reconstruct arbitrary encodings from prose, programs, PDFs or images. It checks each tracked input's bytes against its pinned Git blob identity. For the all-size inventory, it reuses 607 historical labeled-table identities only after exact table byte-hash agreement, and directly classifies 145 further labeled tables. Therefore it is a newly checked recognition and reconciliation of the corpus, with explicitly disclosed use of the existing all-size index. The separate 194-state novelty computation does not rely on those cached class identities.

In `census/occurrences.json`, a declared start is distinguished from an unverified `dense_zero_convention` diagnostic assumption and from an unspecified start. Dense numbering alone does not establish the intended blank-start behavior. The frozen novelty test permits any graph-spanning root and hence does not depend on a claimed designated start. The 193-state replay chooses all controls or a source-backed prescribed control, as specified per entry.

All source paths use repository-relative locators. An exclamation mark separates an archive path from its member. A `::json:` suffix identifies a JSON node. Pinned GitHub URLs are supplied in the delivery and frontier ledgers. The `source_occurrences` field in `frontier194.json` now gives the full tracked literal/JSON count, while `initial_literal_screen_occurrences` preserves the preliminary literal-screen count for provenance.

## Novelty of PA194AX11S

`check_novelty.py` compares exact full transition tuples after allowing arbitrary control renaming, any graph-spanning root, global left/right reflection, global symbol exchange and ignored write/move decoration on terminal halt edges. Global symbol exchange need not preserve blank-zero semantics; it is an additional conservative identification for this structural novelty test.

The delivered candidate has 194 controls, 388 transitions, and dense-table SHA-256

`ae52144ee2bb48e2e90cd473b09054d2024cbdd05deb7261a9bb5bfbf67b4db1`.

The fresh test finds no match among the 82 frozen classes. The receipt is `novelty_receipt.json`. This establishes a new transition graph within the explicitly recognized pinned corpus. It does not establish global novelty, semantic inequivalence, a smaller state record, or an absolute iPRA consistency calibration.

The historical evidence categories on the 82 classes are 40 reported principal constructions, seven supplementary constructions, five source-validated research rotations, 25 research auxiliaries and five rejected tables. These are evidence attributions, not 82 freshly proved consistency equivalences. `comparison_notes.md` describes the mechanism families, duplicated tables, ambiguous names and failed reduction approaches.

## All 53 spanning 193-state classes

| Category | Classes | Fresh startup replay |
|---|---:|---|
| Runtime-collapse transplants | 49 | All 193 starts each: 100 halts, 9,357 certified rays |
| AX11 runtime core | 1 | All 193 starts: 2 halts, 191 certified rays |
| Relay core | 1 | Prescribed start 74: certified ray after 116 transitions |
| QN6 runtime core | 1 | Prescribed start 74: certified ray after 92 transitions |
| Coefficient-three core | 1 | Logical rejection attributed separately; long proof certificate not replayed here |

The 49 transplants already include the original Runtime193 and its append-zero companion, so those are not additional classes. The coefficient-three failure is a collision in the numerical logical calculus, despite successful physical simulation. The other classes fail startup, and the relay also has reported source-contract failures.

`check_rejected193.py` freshly verifies the hashes and sizes of all 53 tables and replays 9,652 blank runs. All are classified within the chosen 2,000-transition bound: 102 finite halts and 9,550 outward blank rays. A ray is certified only when the literal read-zero transition is a self-loop moving into a completely blank half-line. Its future then follows by induction, including when the transition writes a one behind the head. The receipt records every finite configuration and the self-loop row. These are finite proofs of the reported ray behaviors, not extrapolations from a long simulation. The receipt does not itself prove that no useful source frame was visited earlier; the original startup reports make their own target-frame checks.

The coefficient-three 73,393-step logical refutation is supplied evidence discussed in the report, not a computation rerun by this startup checker. None of these failures implies a global 194-state lower bound.

## Files and commands

- `packet_ledger.json` / `.csv`: all 72 deliveries, contributions, source locators and README hashes.
- `frontier194.json` / `.csv`, `reference194/`: annotated 82-class frontier and every exact representative.
- `check_novelty.py`, `novelty_receipt.json`: standalone extended comparison and candidate result.
- `frontier193.json` / `.csv`, `reference193/`: all 53 classes and precise rejection attribution.
- `check_rejected193.py`, `rejected193_replay.json`: standalone blank-run replay and complete finite receipts.
- `census/`: tracked inputs, archive aliases, every recognized occurrence, all class summaries and aggregate metrics.
- `corpus_reconciliation.json`: historical-index exclusions, exact frontier equality and rejected-class categories.
- `inventory_summary.json`: delivery totals plus nested full-census and startup-replay summaries.
- `rescan_corpus.py`: optional complete recognition rescan against a local ProveIt checkout.
- `audit_json_prefilter.py`: optional replay of the numeric-only JSON recognition audit (requires the checkout).

From the packet root, with Python 3.10 or later:

```sh
python3 comparison/check_novelty.py
python3 comparison/check_rejected193.py
```

Both use only the frozen packet and the Python standard library; no original checkout or network is required. To regenerate receipts, supply `--receipt PATH`. These commands do not establish the unresolved absolute iPRA calibration.

The optional full census requires Git and a checkout or Git object database containing the pinned input files and the pinned `MACHINES.tsv` / `MACHINE_FILES.tsv` indices:

```sh
python3 comparison/rescan_corpus.py --repo /path/to/ProveIt --output /path/to/new-census
```

Missing worktree inputs are read with `git cat-file`; a partial clone may need network access to fetch unavailable blobs. Use a fresh output directory. The script does not execute historical generators or verification pipelines. The complete rescan is unnecessary for replaying the frozen novelty result.
