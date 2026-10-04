# Independent metadata reauthentication: cyclotomic and Mellin/Stokes reviews

**PASS; no metadata mismatch found.** A fresh read-only checker reproduced the recorded Git, archive, placement, span, diff and literal-label evidence. This is metadata reauthentication only. It neither repeats the mathematical reviews nor extends their declared read scope.

The authenticated review files are:

| File | SHA-256 |
|---|---|
| `review_mellin_stokes_placement_05304d5ec.md` | `fd124f5cb3e1aec55e1a939cd79a83d5b1f7bcd9b54dc48b52f62ef07c9ce5dd` |
| `review_mellin_stokes_placement_05304d5ec.json` | `2ddf01c9f533197ad7f72c3c167d670a841c74915a09bdc1bd0749e553135dea` |
| `review_cyclotomic_7389d7de4.md` | `a9e1f9a9d7b3c292910fca4f908c12ce6a42c3bdd68e9038c027c4befdcebb1a` |
| `review_cyclotomic_7389d7de4.json` | `8b6a6348c831234ad8c4ddb87f895bde7c3bbf5c708d615000241b5d982adac0` |

For Mellin/Stokes commit `05304d5ecce537c9a237d4e3a85a18c4519230fe`, the checker independently confirms the immediate parent, all20 changed paths and statuses, before/after object IDs and byte hashes, all20 raw per-file diffs, and the complete recorded commit-message bytes. It reconstructs each recorded raw byte-line span directly from the immutable blob or diff. The diff format uses nine-character object abbreviations, matching the manifest.

Both original ZIP payloads agree with their arrival and retired-parent bytes. All18 regular members, their byte lengths, CRC fields and SHA-256 values reproduce. Both delivered checksum ledgers are parsed in memory and verify all16 non-ledger members. Each of those16 members equals its placed Git file byte for byte; the total is1,179,277 bytes. The ledgers are not extracted or recreated in the repository. The comparison with the earlier intake's18 member pins also matches. The two literal source-label censuses reproduce142/154 unique labels and104/127 recognized internal reference occurrences, without unresolved targets in that parser's stated scope. The978 selected TeX lines are authenticated as recorded spans, not newly claimed mathematical reading.

For cyclotomic commit `7389d7de4cec2bf27f0c882e00f26ecc7acc5c83`, the immediate parent, all four changed paths and their before/after blobs match. All three text diffs reproduce exactly using full object IDs, including their hunk coordinates and285 added/four deleted lines. The PDF is authenticated as bytes only. Every recorded normalized span is reconstructed using the declared UTF-8 splitlines/LF-join/final-LF convention. All three listed archive members and their selected spans match; this intentionally does not broaden that manifest's partial member inventory into an all-member audit.

The cyclotomic archive's original-arrival equality and recorded absence of the claimed placement destination at the review commit are independently checked. The three text label censuses reproduce the chapter's27-to30 change and preservation of the old label sequence. The three added label targets and three bibliography keys are each unique in the recorded current TeX sources. The historical false clause occurs in both the parent and current chapter text, as recorded. This is a retention check, not a new proof of the refutation or a certification of the remaining conjecture.

Across both manifests, the new checker validates68 blob-record occurrences covering43 distinct commit/path pairs,23 diffs,35 spans totaling4,161 recorded lines, five archive-record occurrences,21 listed member-record occurrences, and five label censuses. Archive/member occurrences include repeated payloads across the two reviews. The two original collectors are separately SHA-256 authenticated as inert bytes; neither collector nor any previous reauthentication helper is executed or imported.

Fresh normal and optimized Python (`-O`) exact receipt replays from `/` both pass. The new files are:

* `reauth_cyclotomic_mellin_reviews.py`: `a345a9aea09226cb0509963b81e93c45153a90afc599a334596160a1a2b35b93`.
* `reauth_cyclotomic_mellin_reviews.json`: `5eba43d9b5ec04a957da4e381b83975c10fc061a18d4a6b67717e70b50d1ff3e`.

The checker accepts `--repo`, `--review-root`, and exactly one of `--output` or `--expect`; output creation is exclusive. Git calls are limited to read-only `show`, `rev-parse`, `diff` and `ls-tree`. No repository file, index, branch or history was changed; no archive contents were executed or extracted to the repository. No supplied verifier, build, PDF rendering, numerical experiment, analytic theorem or external reference was replayed. The two reviews' findings and limitations remain attributed to those reviews.
