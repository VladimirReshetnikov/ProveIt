# Pinned PA-machine comparison and logical audit

This packet accompanies the new PA194H5X and PA194JH5X constructions. Its source comparison is frozen at ProveIt `8d31445d858761a8f6150c2e5012adae8895e932`.

## Portable check

From this directory, with Python 3.10+ and its standard library:

```sh
python3 -B verify_packet.py
```

This checks the sealed file hashes, the 93-delivery inventory, all-size count identities, every included representative matrix, all 139 exact enlarged canonical tuples, novelty of the two new 194-state tables, and the finite h5X/J/J_A Hilbert certificates. It writes nothing by default. To save a new receipt, use `--output` with a path outside this sealed packet. This command does not rebuild the Lean project or reproduce the entire gigabyte-scale source census.

## Core results and their scope

- All 27,459 pinned PA/incoming source files were checked against Git blob identities, with no mismatch.
- 4,468 recognized table occurrences reduce to 879 normalized labeled identities and 721 spanning graph classes, plus seven disconnected literal identities.
- The 194-state frontier has 139 spanning classes, plus two disconnected diagnostics. Every spanning class stays distinct under arbitrary state labels, any spanning root, tape reflection, global symbol exchange, and ignored final halting action.
- The 54 spanning 193-state classes are rejected or diagnostic constructions, not verified smaller consistency machines.
- The two new tables are absent from the current 139-class frontier and distinct from each other under all tested symmetries.
- Source report categories are attributed claims: 67 principal constructions, seven supplementary, 47 auxiliaries, four seeds, and 14 rejected graphs among the 139. They are not 67 independently formalized iPRA theorems.

The actual start state, blank symbol, and physical interpretation matter for execution. Representative matrices in this comparison preserve their extracted labels and are supplied as structural inputs; consult their original source specification before running them as named machines. Symbol complementation in a graph test is not by itself a zero-blank semantic equivalence.

## File map

- `report_comparison.tex`: article-ready, ASCII LaTeX comparison section, no preamble or private macros.
- `comparison_notes.md`, `historical_architectures.md`: detailed architecture and status reviews.
- `current/frontier194_table.tex`, `current/comparison194_annotated.csv` and `.json`: every current 194-state class with mechanism and evidence attribution.
- `packet_ledger93.csv` and `.json`: all 87 filed deliveries and six current incoming ZIPs.
- `current/all_size_distribution.csv`, `current/all_size_classes.csv`: all observed state sizes and structural classes; `current/occurrences.json` preserves individual source/member locators.
- `current/representatives/`: frozen representative matrices through 196 states, including explicitly marked diagnostics and rejected classes. Larger classes retain their source locators in the all-size inventory.
- `current/canonical_tuples194.json`: exact tuple inputs to the enlarged graph comparison.
- `candidates/`: copies of the two new dense literal tables for novelty checking only; complete construction and physical validation live in the main deliverable.
- `new_candidates_novelty.json`: recorded structural comparison receipt. `verification_record.json` records the complete offline comparison replay.
- `current/all_source_blobs.csv`, `current/source_blobs.json`, `source_manifest.json`, `current/full_source_blob_verification.json`: pinned identities and the completed source audit.
- `current/archives.json`, `current/archive_references.json`: recursive ZIP identities and locators.
- `logical_head_audit.md`: noncircular h5X explosion, the shorter J and J_A heads, exact finite certificates and prior-art distinctions.
- `logical_certificates/`, `j_certificates/`, `ja_certificates/`: independently replayable symbolic Hilbert templates. K/S/Peirce are explicitly retained uniform derived rules of rho8; no truth-table oracle or proof-assistant kernel claim is made.
- `foundation_endpoint_audit.md` and `.json`: current native PA consistency sentence and its exact Foundation dependency, distinguished from the historical source and the revised written AX11H adapter.
- `endpoint_sources/`: the exact small source files supporting that dependency audit.
- `runtime_context_review.md`: review of the finite-window search's overapproximation; its limits are narrower than a global state lower bound.
- `logical_prior_art_hits.json`, `search_logical_prior_art.py`: reproducible text search locators, not a semantic exhaustiveness or literature-priority theorem.
- `vendor/`, `PROVENANCE.json`, `NOTICE.txt`, `licenses/`: attributed parser and classifier reuse.

## Rebuilding the source census, when desired

The stored results are sufficient for the ordinary check above. To rerun the full source inventory, first materialize the two requested source directories at the exact pinned revision, then use an output directory outside this packet:

```sh
python3 -B rebuild_current_census.py --source /path/to/ProveIt --manifest source_manifest.json --pin 8d31445d858761a8f6150c2e5012adae8895e932 --output /path/to/new-census
```

The recognizers cover complete supported literal/JSON matrices and recursive ZIPs. They do not execute arbitrary generator programs or extract every diagram/table from prose. Packet filing removed duplicate literal tables; the retained source maps and recursive reference archives are therefore important provenance. The census says what is present at this pin, not what might appear in a later main revision.

The primary PA194 Lean machine-specific iPRA reductions remain open in the pinned source. The revised AX11H packet supplies a substantial written iPRA proof; the new machines import that written calibration and supply their own logical and physical transformations. Running this comparison packet does not turn that distinction into a new end-to-end Lean theorem.
