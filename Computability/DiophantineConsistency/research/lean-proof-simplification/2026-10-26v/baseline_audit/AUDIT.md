# Prior-work and assumed-application audit

## Result

The six proposed mechanisms in this study remain additional **after** the promised outcomes of all prior work are treated as available. They concern newly introduced machine encoding/action/trace proofs and Wang row constructions, not old unimplemented scanner, coefficient, decoder, depth or geometry work. See `NOVELTY_DECISIONS.md` for the target-by-target test.

The comparison is pinned to [ProveIt `22e020937caa81d0cb72a4f63071d6c0bcc1eba9`](https://github.com/VladimirReshetnikov/ProveIt/tree/22e020937caa81d0cb72a4f63071d6c0bcc1eba9). Both specifically requested locations were inspected at that pin:

- [Exact research/lean-proof-simplification folder](https://github.com/VladimirReshetnikov/ProveIt/tree/22e020937caa81d0cb72a4f63071d6c0bcc1eba9/Computability/DiophantineConsistency/research/lean-proof-simplification): six placed packets `2026-10-26a` through `f`, plus their current README and adoption record.
- [docs/incoming](https://github.com/VladimirReshetnikov/ProveIt/tree/22e020937caa81d0cb72a4f63071d6c0bcc1eba9/docs/incoming): the current README and **five additional proof-simplification archives**. These are not the five archives that occupied the directory at the preceding review pin.
- The nine proposals in the previous delivered study are also assumed applied, whether or not that study has been archived upstream. Its report-source bytes are recorded in `PREVIOUS_STUDY_BINDING.json`.

## Evidence and integrity

| Check | Result |
|---|---:|
| Archive byte streams independently rehashed | 11 |
| Current incoming archives fetched at the pin | 5 |
| Fresh archive members checked and safely extracted | 400 |
| Current placed packet Git blobs verified | 321 |
| Exact-byte matches recovered from prior archives | 296 |
| CSVs reconstructed with CRLF→LF, then exact current Git hash checked | 14 |
| Fresh placement/omission metadata files verified | 11 |
| Research root files and current incoming README verified | 3 |

Archive checks recompute the Git blob SHA-1 over `blob <length>\0<bytes>` as well as SHA-256. Safe reading/extraction rejects absolute paths, parent traversal, backslashes, NULs, duplicate names and symlinks; bounds member counts and total expanded size; and reads members through ZIP CRC checking. Submitted executable code and Lean files were **not executed**.

The six placed manuscripts and their technical material were bound to their exact current Git blobs. Prior exact-byte inspections and the 75-family catalog were reused only after this new binding, with targeted semantic cross-checks. The five fresh manuscripts and their technical proposal notes were inspected, including lower-priority suggestions omitted from the abstracts. `DOCUMENT_SOURCES.json` gives member paths, source keys and hashes. Historical compile receipts inside packets are not new validation by this study.

## How “assume already applied” is modeled

`ASSUMED_APPLIED_BASELINE.md` defines **18 usable API/refactored-state contracts**, rather than merely prohibiting a list of titles. `ASSUMPTION_LEDGER.json` and `.csv` map every recorded outcome to one of those contracts:

- 75 legacy family rows from the six placed packets;
- 31 additional or strengthened contract rows from the current incoming manuscripts/notes;
- nine prior-delivered study rows.

These 115 rows **overlap** and are not a count of 115 independent ideas. For example, exact decoder fusion and sum-at-most-one reuse occur in multiple packets. Newly discovered supplementary proposals include cyclic packing as a monoid-algebra evaluation, schema-renaming action normalization, shared binary syntax constructor views, a common zero-pair lemma and analytic `set`-binding cleanup; these are excluded too.

Design-only proposals are treated as delivered outcomes for novelty. This includes their promised production adapters, migrations and advertised client families: an old unimplemented adapter is not available to be renamed as a new proposal. Where two prior patches are mutually exclusive, the baseline grants their compatible semantic outcomes, not the false claim that all concrete patches were applied simultaneously. `INTEGRATION_CONFLICTS.md` records the resolutions and their guards.

## Source key

For A–F, the paths below are under the pinned exact research folder. Their archive streams are the same six sources as the preceding 75-family catalog, but placement paths have changed.

| Key | Current packet | Original archive / manuscript |
|---|---|---|
| A | `2026-10-26e` | `Lean_Proof_Simplification_2026-10-26.zip`; `report/report.tex` |
| B | `2026-10-26f` | `ProveIt_Lean_Proof_Simplification_2026-10-26.zip`; `report/proof_simplification_report.tex` and its section inputs |
| C | `2026-10-26b` | `diophantine-lean-simplification-2026-10-26.zip`; `report.tex` |
| D | `2026-10-26d` | `lean-proof-simplification-2026-10-26 (2).zip`; `report.tex` |
| E | `2026-10-26c` | `lean-proof-simplification-2026-10-26.zip`; `report.tex` |
| F | `2026-10-26a` | `diophantine-lean-proof-simplification-2026-10-26.zip`; `report.tex` and `source_notes/` |
| G | Current incoming | `diophantine-lean-additional-simplifications-2026-10-26.zip`; `report.tex`, `notes/` |
| H | Current incoming | `diophantine-lean-new-directions-2026-10-26.zip`; `report.tex`, `evidence/*review*` |
| I | Current incoming | `diophantine-lean-new-ideas-2026-10-26.zip`; `report.tex`, `native-proofs/findings.md` |
| J | Current incoming | `diophantine-lean-simplification-2026-10-26(1).zip`; `report.tex` |
| K | Current incoming | `lean-proof-simplification-review-2026-10-26.zip`; `lean-proof-simplification-review.tex`, `evidence/*/findings.txt` |
| R2 | Prior delivered study | `lean_simplification_round2_20261026/report/sections/`; bound separately, not represented as an upstream Git blob |

Legacy locators such as `A:6` mean report sections unless they explicitly name a member and line range. New locators such as `G:182-221` mean `report.tex` line ranges; for K they refer to `lean-proof-simplification-review.tex`. Member-specific references override that convention.

## Actual adoption is a separate question

The current repository [adoption record](https://github.com/VladimirReshetnikov/ProveIt/blob/22e020937caa81d0cb72a4f63071d6c0bcc1eba9/Computability/DiophantineConsistency/research/lean-proof-simplification/ADOPTION.md) distinguishes adopted, queued, pending and deferred work. It is not identical to the committed source state: the record's queued `NatIterate` and extractor/Option changes are absent from the pinned source in the forms it describes. `CompilerSupport` is physically present. These observations are detailed in `INTEGRATION_CONFLICTS.md`; they do not weaken the counterfactual assumption.

## Reproduce the byte audit

With an existing checkout containing the exact pinned files, run:

```sh
python3 verify_baseline.py --repo /path/to/ProveIt
```

This standard-library-only command verifies all 321 placed blobs, the root metadata, all six current incoming entries, and every fresh archive member. It performs no extraction, installation, network request, Lean invocation or repository mutation. It was exercised against a local fixture assembled from the verified fetched bytes, returning PASS. It is **not** a Lean proof check.

The proposed Lean changes require the separate compilation/axiom/downstream replay gates supplied with the study. This audit provides no new compiler acceptance, runtime, proof-term-size or performance claim.
