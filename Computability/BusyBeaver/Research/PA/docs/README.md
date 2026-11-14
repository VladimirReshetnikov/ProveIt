# Delivered research packets on Con(PA) machines

This directory holds the research packets that were delivered to
[`docs/incoming`](../../../../../docs/incoming/README.md) as archives between 28 October and
13 November 2026. Each packet is about constructing a small Turing machine whose
non-halting on the blank tape is equivalent to the consistency of Peano arithmetic,
`Con(PA)`, or about comparing and reducing such machines.

The packets are filed as delivered. Nothing in them was rerun, checked or edited for this
placement, and the summaries in the table below repeat what each packet says about itself.
The checked work of this project is described in the [parent README](../README.md).

## Layout

- Each archive has one directory, named after the archive. A trailing ` (2)` of an archive
  name is written `_2`.
- Every archive wraps its files in a single top directory. That directory is removed, so
  the archive member `<wrapper>/<path>` is the file `<directory>/<path>` here. The table
  gives each wrapper.
- Files are stored byte for byte as delivered. The repository's line-ending normalization
  is switched off for this directory in the root `.gitattributes`, because checks elsewhere
  in the project compare digests of members.
- One directory is renamed. `pa_consistency_research_2026-11-13` ships both
  `reference/proveit/U208_ConPA_2026-10-29/` and `reference/proveit/u208_conpa_2026-10-29/`,
  which a file system that ignores case cannot hold together. The second one is placed as
  `reference/proveit/u208_conpa_2026-10-29_lowercase-name/`.

## What is not placed

[`OMITTED.tsv`](OMITTED.tsv) lists every archive member that has no file here, with the
reason and where the same bytes are. There are three reasons.

| Reason | Members | Where the bytes are |
|---|---:|---|
| `upstream-copy` | 12,938 | The member is byte-identical to a file of the imported snapshots under [`jamesyc-upstream`](../jamesyc-upstream/README.md). The reference column gives that file. Licence and notice files are placed even when they are copies. |
| `sibling-archive` | 15 | The member is a nested archive that is byte-identical to another delivered archive. The reference column gives the directory of that archive here. |
| `ignored` | 903 | The member matches the repository's `.gitignore` (`*.log` and `SHA256SUMS` files). It is available only from the delivered archive. |

Six nested archives have no delivered counterpart and are placed as files:
`U209_ConPA_Joint_2026-10-29.zip` (in three packets), `U209_ConPA_2026-10-29.zip`,
`U209_ConPA_Joint_supplement.zip` and `u212_combined_2026-10-29.zip`.

A member is not omitted because another packet contains the same file. Packets quote one
another at length, so about a third of the placed bytes are repeats between packets.

## Packets

The 36 archives hold 25,017 members: 11,161 placed here (565 MB), 12,938 copies of the upstream
snapshots, 15 nested copies of sibling archives and 903 ignored files. The columns P, U, S
and I give these four counts for each packet. Arrival is the date of the commit that added
the archive to `docs/incoming`.

| Directory | Arrived | Wrapper in the archive | What the packet states | P | U | S | I |
|---|---|---|---|---:|---:|---:|---:|
| [`pa_unary_power_cover`](pa_unary_power_cover/) | 2026-10-28 | `pa_unary_power_cover` | Unary power covering at PA strength (report of 27 October 2026). The U208 packets carry it as a baseline. | 33 | 0 | 0 | 1 |
| [`U208_ConPA_Conditional_Context_2026-10-29`](U208_ConPA_Conditional_Context_2026-10-29/) | 2026-10-29 | `u208_conpa_2026-10-29` | U208 by a conditional tape-context reduction. States a 208-state candidate `machine/u208.tm`. | 96 | 0 | 0 | 7 |
| [`U208_ConPA_Entry_Context_2026-10-29`](U208_ConPA_Entry_Context_2026-10-29/) | 2026-10-29 | `u208_conpa_entry_context_2026-10-29` | U208 by eliminating a state using entry context. States a 208-state machine `machine/u208.tm`. | 98 | 0 | 1 | 4 |
| [`U208_ConPA_History_2026-10-29`](U208_ConPA_History_2026-10-29/) | 2026-10-29 | `U208_ConPA_History_2026-10-29` | U208 by a finite-history decoder fold. States a 208-state candidate `machine/u208.tm`. | 112 | 0 | 1 | 7 |
| [`U208_ConPA_2026-10-29`](U208_ConPA_2026-10-29/) | 2026-10-29 | `U208_ConPA_2026-10-29` | U208 by a three-cell fold. States a 208-state candidate `machine/u208.tm`. | 77 | 0 | 1 | 3 |
| [`u208_research_2026-10-29`](u208_research_2026-10-29/) | 2026-10-29 | `u208_research_2026-10-29` | U208 research release. States two 208-state machines, `machine/u208.tm` and `machine/variant_plain/u208.tm`. | 263 | 0 | 0 | 3 |
| [`Below_U208_Research_2026-10-29`](Below_U208_Research_2026-10-29/) | 2026-10-29 | `Below_U208_Research_2026-10-29` | Research toward fewer than 208 states. States that no machine with 207 states or fewer was obtained. | 227 | 0 | 1 | 4 |
| [`u208_comparison_research_2026-10-29`](u208_comparison_research_2026-10-29/) | 2026-10-29 | `u208_comparison_research_2026-10-29` | Comparison of the 208-state proposals and a search below 208. States that the target was not achieved. | 82 | 0 | 0 | 16 |
| [`ConPA_below208_research_2026-10-29`](ConPA_below208_research_2026-10-29/) | 2026-10-29 | `ConPA_U208_research_2026-10-29` | Comparative audit and reduction search below 208. States that it does not establish a 207-state machine. | 449 | 0 | 3 | 198 |
| [`pa_consistency_research_2026-10-29`](pa_consistency_research_2026-10-29/) | 2026-10-29 | `pa_consistency_research_2026-10-29` | Audit and new source reductions. States that no validated machine below 208 states was obtained. | 151 | 0 | 2 | 23 |
| [`pa208_research_2026-10-29`](pa208_research_2026-10-29/) | 2026-10-29 | `pa208_research` | Comparison and research below 208 states. States that it does not establish a valid machine below 208. | 2262 | 0 | 6 | 116 |
| [`pa_tm_research_2026-11-13`](pa_tm_research_2026-11-13/) | 2026-11-13 | `pa_tm_research_2026-11-13` | Comparison and reduction research. States a new 196-state variant with shorter source paths and nothing below 196. | 207 | 2454 | 0 | 30 |
| [`pa_consistency_research_2026-11-13`](pa_consistency_research_2026-11-13/) | 2026-11-13 | `pa_consistency_research` | Comparison and diagonal-vacuity research. States a shorter axiom program with a 199-state implementation and nothing below 196. | 81 | 9 | 0 | 12 |
| [`conpa_tm_comparison_and_reduction_search`](conpa_tm_comparison_and_reduction_search/) | 2026-11-13 | `conpa_tm_comparison_and_reduction_search` | Comparison and reduction search. States two experimental 196-state command variants and nothing below 196. | 392 | 2149 | 0 | 67 |
| [`pa196_research_2026-11-13`](pa196_research_2026-11-13/) | 2026-11-13 | `pa196_research` | PA196 comparison, source factorization and proof obligations. States a source tree of 157 internal nodes and nothing below 196. | 189 | 15 | 0 | 2 |
| [`pa_consistency_research`](pa_consistency_research/) | 2026-11-13 | `pa_consistency_research` | Research and verification packet. States that no machine below 196 states has been validated. | 121 | 9 | 0 | 2 |
| [`pa_tm_comparison_and_reductions`](pa_tm_comparison_and_reductions/) | 2026-11-13 | `pa_tm_research` | Comparison and new rewrites, a research snapshot. | 171 | 25 | 0 | 5 |
| [`pa_tm_extended_research_2026-11-13`](pa_tm_extended_research_2026-11-13/) | 2026-11-13 | `pa_tm_extended_research_2026-11-13` | Comparison and refined reduction search. States that the smallest accepted count is 196. | 162 | 22 | 0 | 16 |
| [`conpa_tm_comparison_and_search`](conpa_tm_comparison_and_search/) | 2026-11-13 | `conpa_tm_study` | Comparison and a search below 196. States that none was obtained; files named `195` are rejected or diagnostic candidates. | 412 | 2454 | 0 | 78 |
| [`pa_consistency_reduction`](pa_consistency_reduction/) | 2026-11-13 | `pa_consistency_reduction` | Comparison and reduction experiments. States two new 196-state variants and a shorter source program with a 203-state implementation. | 278 | 2141 | 0 | 51 |
| [`pa_consistency_comparison_2026_11_13`](pa_consistency_comparison_2026_11_13/) | 2026-11-13 | `pa_consistency_comparison_2026_11_13` | Comparison and new reduction experiments. States that nothing below 196 was obtained. | 221 | 17 | 0 | 1 |
| [`PA_consistency_TM_research_2026-11-13`](PA_consistency_TM_research_2026-11-13/) | 2026-11-13 | `pa_tm_reduction_study` | Comparison and new source reductions. States that no machine below 196 is claimed. | 245 | 8 | 0 | 16 |
| [`pa_consistency_research_2026-11-13_2`](pa_consistency_research_2026-11-13_2/) | 2026-11-13 | `pa_consistency_research_2026-11-13` | Comparison and search below 196. States two new layouts with 196 and 198 states and a command-level reduction. | 227 | 18 | 0 | 33 |
| [`conpa_tm_study_2026-11-13`](conpa_tm_study_2026-11-13/) | 2026-11-13 | `conpa_tm_study` | Comparison and reduction study. States that nothing below 196 was obtained. | 170 | 1133 | 0 | 2 |
| [`pa_below196_research`](pa_below196_research/) | 2026-11-13 | `pa_below196_research` | Comparison and reduction experiments. States that nothing below 196 was obtained. | 242 | 10 | 0 | 6 |
| [`pa_consistency_comparison_and_new196_2026-11-13`](pa_consistency_comparison_and_new196_2026-11-13/) | 2026-11-13 | `pa_consistency_research` | Comparison and reduction research. States that it contains no accepted machine below 196. | 482 | 21 | 0 | 10 |
| [`pa_tm_research_2026-11-13_2`](pa_tm_research_2026-11-13_2/) | 2026-11-13 | `pa_tm_research_2026-11-13` | Comparison and reduction investigation. States same-size work, failed candidates and nothing below 196. | 177 | 2161 | 0 | 2 |
| [`pa_consistency_cross_archive`](pa_consistency_cross_archive/) | 2026-11-13 | `pa_consistency_cross_archive` | Cross-archive constructions and reduction search. States that it does not certify a 195-state machine. | 519 | 32 | 0 | 8 |
| [`pa195_conpa_2026-11-13`](pa195_conpa_2026-11-13/) | 2026-11-13 | `pa195_conpa` | PA195. States a 195-state machine `pa195/pa195.tm` and an article with a PA proof of the equivalence. | 80 | 26 | 0 | 5 |
| [`pa_consistency_reduction_audit_2026-11-14`](pa_consistency_reduction_audit_2026-11-14/) | 2026-11-13 | `pa_consistency_reduction_audit` | Comparison and reduction audit. States nothing below 196 and no new theorem. | 360 | 20 | 0 | 13 |
| [`pa_consistency_research_2026-11-14`](pa_consistency_research_2026-11-14/) | 2026-11-13 | `pa_consistency_research` | Comparison and NEG18. States an 18-instruction encoded negation with a compiled machine of 197 states. | 379 | 33 | 0 | 22 |
| [`PA195_ConPA_research_2026-11-14`](PA195_ConPA_research_2026-11-14/) | 2026-11-13 | `pa_consistency_research` | A 195-state machine. States the primary `machine_195S.tm` and a second table `machine_195C.tm`. | 1276 | 44 | 0 | 8 |
| [`pa195_followup_research`](pa195_followup_research/) | 2026-11-13 | `pa195_followup` | Comparison and searches below 195. States a graph-distinct 195-state machine M195S8 and nothing below 195. | 404 | 57 | 0 | 54 |
| [`pa194_conpa_2026-11-13`](pa194_conpa_2026-11-13/) | 2026-11-13 | `pa194_conpa` | A 194-state machine. States the table `construction/tables/pa194.tm` and a proof of the equivalence in PA. | 137 | 10 | 0 | 11 |
| [`pa194_conpa_2026-11-13_2`](pa194_conpa_2026-11-13_2/) | 2026-11-13 | `pa194_conpa` | PA194. States a 194-state machine `pa194/pa194.tm` and an article with a PA proof of the equivalence. | 246 | 44 | 0 | 51 |
| [`pa195_diagonal_combined_2026-11-13`](pa195_diagonal_combined_2026-11-13/) | 2026-11-13 | `pa195_diagonal_combined` | PA195DC. States a different 195-state machine. | 133 | 26 | 0 | 16 |

## Archives still in `docs/incoming`

21 of the 36 archives stay in `docs/incoming` although their contents are placed here.
Scripts and READMEs of this project open them at that path, and several scripts check
the digest of the archive file itself, so removing them would break those checks. They
can be removed once those references read the files of this directory instead.

- `PA195_ConPA_research_2026-11-14.zip`
- `U208_ConPA_2026-10-29.zip`
- `conpa_tm_comparison_and_reduction_search.zip`
- `conpa_tm_comparison_and_search.zip`
- `conpa_tm_study_2026-11-13.zip`
- `pa194_conpa_2026-11-13 (2).zip`
- `pa194_conpa_2026-11-13.zip`
- `pa195_conpa_2026-11-13.zip`
- `pa195_diagonal_combined_2026-11-13.zip`
- `pa195_followup_research.zip`
- `pa208_research_2026-10-29.zip`
- `pa_consistency_comparison_and_new196_2026-11-13.zip`
- `pa_consistency_reduction.zip`
- `pa_consistency_research.zip`
- `pa_consistency_research_2026-10-29.zip`
- `pa_consistency_research_2026-11-13 (2).zip`
- `pa_consistency_research_2026-11-13.zip`
- `pa_tm_comparison_and_reductions.zip`
- `pa_tm_extended_research_2026-11-13.zip`
- `pa_tm_research_2026-11-13 (2).zip`
- `pa_tm_research_2026-11-13.zip`

The other 15 archives are removed from `docs/incoming`. They remain in the history of
the repository at the commits that added them.

## Third-party material

The packets contain files derived from James Chang's PA196 and PA209 developments and
from other published sources, under the licence and notice files that each packet ships.
Those files govern the material they name; the repository's root licence does not
replace them.
