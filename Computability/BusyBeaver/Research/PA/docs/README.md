# Delivered research packets on Con(PA) machines

This directory holds the research packets that were delivered to
[`docs/incoming`](../../../../../docs/incoming/README.md) as archives between 28 October and
13 November 2026. Each packet is about constructing a small Turing machine whose
non-halting on the blank tape is equivalent to the consistency of Peano arithmetic,
`Con(PA)`, or about comparing and reducing such machines.

The packets are filed as delivered, except that a machine table which repeats a machine
already kept in another file is removed; [`MACHINES.md`](MACHINES.md) lists the distinct
machines. Nothing in the packets was rerun, checked or edited for this placement, and the
summaries in the table below repeat what each packet says about itself.
The checked work of this project is described in the [parent README](../README.md).

## Layout

- Each archive has one directory, named after the archive. A trailing ` (1)` or ` (2)` of an
  archive name is written `_1` or `_2`.
- Almost every archive wraps its files in a single top directory. That directory is
  removed, so the archive member `<wrapper>/<path>` is the file `<directory>/<path>` here.
  The table gives each wrapper, or `none` for an archive without one.
- Files are stored byte for byte as delivered. The repository's line-ending normalization
  is switched off for this directory in the root `.gitattributes`, because checks elsewhere
  in the project compare digests of members.
- One directory is renamed. `pa_consistency_research_2026-11-13` ships both
  `reference/proveit/U208_ConPA_2026-10-29/` and `reference/proveit/u208_conpa_2026-10-29/`,
  which a file system that ignores case cannot hold together. The second one is placed as
  `reference/proveit/u208_conpa_2026-10-29_lowercase-name/`.

## What is not placed

[`OMITTED.tsv`](OMITTED.tsv) lists every archive member that has no file here, with the
reason and where the same bytes are. There are four reasons.

| Reason | Members | Where the bytes are |
|---|---:|---|
| `upstream-copy` | 13,186 | The member is byte-identical to a file of the imported snapshots under [`jamesyc-upstream`](../jamesyc-upstream/README.md). The reference column gives that file. Licence and notice files are placed even when they are copies. |
| `sibling-archive` | 17 | The member is a nested archive that is byte-identical to another delivered archive. The reference column gives the directory of that archive here. |
| `ignored` | 1,285 | The member matches the repository's `.gitignore` (`*.log` and `SHA256SUMS` files). It is available only from the delivered archive. |
| `duplicate-machine` | 6,596 | The member is a machine table (`.tm`) and its machine is kept in another file, either with the same bytes or with its states renamed. The reference column gives the kept file and says which. See [`MACHINES.md`](MACHINES.md). |

Six nested archives have no delivered counterpart and are placed as files:
`U209_ConPA_Joint_2026-10-29.zip` (in three packets), `U209_ConPA_2026-10-29.zip`,
`U209_ConPA_Joint_supplement.zip` and `u212_combined_2026-10-29.zip`.

Apart from machine tables, a member is not omitted because another packet contains the
same file. Packets quote one another at length, so many placed files repeat between
packets. A script of a packet that reads a removed table or a file that is not placed
does not run here as delivered.

## Packets

The 61 archives hold 35,544 members: 14,460 placed here (776 MB), 13,186 copies of the upstream
snapshots, 17 nested copies of sibling archives, 1,285 ignored files and 6,596 duplicate machine
tables. The columns P, U, S, I and M give these five counts for each packet. Arrival is
the date of the commit that added the archive to `docs/incoming`.

| Directory | Arrived | Wrapper in the archive | What the packet states | P | U | S | I | M |
|---|---|---|---|---:|---:|---:|---:|---:|
| [`pa_unary_power_cover`](pa_unary_power_cover/) | 2026-10-28 | `pa_unary_power_cover` | Unary power covering at PA strength (report of 27 October 2026). The U208 packets carry it as a baseline. | 33 | 0 | 0 | 1 | 0 |
| [`U208_ConPA_Conditional_Context_2026-10-29`](U208_ConPA_Conditional_Context_2026-10-29/) | 2026-10-29 | `u208_conpa_2026-10-29` | U208 by a conditional tape-context reduction. States a 208-state candidate `machine/u208.tm`. | 87 | 0 | 0 | 7 | 9 |
| [`U208_ConPA_Entry_Context_2026-10-29`](U208_ConPA_Entry_Context_2026-10-29/) | 2026-10-29 | `u208_conpa_entry_context_2026-10-29` | U208 by eliminating a state using entry context. States a 208-state machine `machine/u208.tm`. | 81 | 0 | 1 | 4 | 17 |
| [`U208_ConPA_History_2026-10-29`](U208_ConPA_History_2026-10-29/) | 2026-10-29 | `U208_ConPA_History_2026-10-29` | U208 by a finite-history decoder fold. States a 208-state candidate `machine/u208.tm`. | 94 | 0 | 1 | 7 | 18 |
| [`U208_ConPA_2026-10-29`](U208_ConPA_2026-10-29/) | 2026-10-29 | `U208_ConPA_2026-10-29` | U208 by a three-cell fold. States a 208-state candidate `machine/u208.tm`. | 64 | 0 | 1 | 3 | 13 |
| [`u208_research_2026-10-29`](u208_research_2026-10-29/) | 2026-10-29 | `u208_research_2026-10-29` | U208 research release. States two 208-state machines, `machine/u208.tm` and `machine/variant_plain/u208.tm`. | 245 | 0 | 0 | 3 | 18 |
| [`Below_U208_Research_2026-10-29`](Below_U208_Research_2026-10-29/) | 2026-10-29 | `Below_U208_Research_2026-10-29` | Research toward fewer than 208 states. States that no machine with 207 states or fewer was obtained. | 208 | 0 | 1 | 4 | 19 |
| [`u208_comparison_research_2026-10-29`](u208_comparison_research_2026-10-29/) | 2026-10-29 | `u208_comparison_research_2026-10-29` | Comparison of the 208-state proposals and a search below 208. States that the target was not achieved. | 68 | 0 | 0 | 16 | 14 |
| [`ConPA_below208_research_2026-10-29`](ConPA_below208_research_2026-10-29/) | 2026-10-29 | `ConPA_U208_research_2026-10-29` | Comparative audit and reduction search below 208. States that it does not establish a 207-state machine. | 418 | 0 | 3 | 198 | 31 |
| [`pa_consistency_research_2026-10-29`](pa_consistency_research_2026-10-29/) | 2026-10-29 | `pa_consistency_research_2026-10-29` | Audit and new source reductions. States that no validated machine below 208 states was obtained. | 138 | 0 | 2 | 23 | 13 |
| [`pa208_research_2026-10-29`](pa208_research_2026-10-29/) | 2026-10-29 | `pa208_research` | Comparison and research below 208 states. States that it does not establish a valid machine below 208. | 2143 | 0 | 6 | 116 | 119 |
| [`pa_tm_research_2026-11-13`](pa_tm_research_2026-11-13/) | 2026-11-13 | `pa_tm_research_2026-11-13` | Comparison and reduction research. States a new 196-state variant with shorter source paths and nothing below 196. | 194 | 2454 | 0 | 30 | 13 |
| [`pa_consistency_research_2026-11-13`](pa_consistency_research_2026-11-13/) | 2026-11-13 | `pa_consistency_research` | Comparison and diagonal-vacuity research. States a shorter axiom program with a 199-state implementation and nothing below 196. | 70 | 9 | 0 | 12 | 11 |
| [`conpa_tm_comparison_and_reduction_search`](conpa_tm_comparison_and_reduction_search/) | 2026-11-13 | `conpa_tm_comparison_and_reduction_search` | Comparison and reduction search. States two experimental 196-state command variants and nothing below 196. | 313 | 2149 | 0 | 67 | 79 |
| [`pa196_research_2026-11-13`](pa196_research_2026-11-13/) | 2026-11-13 | `pa196_research` | PA196 comparison, source factorization and proof obligations. States a source tree of 157 internal nodes and nothing below 196. | 170 | 15 | 0 | 2 | 19 |
| [`pa_consistency_research`](pa_consistency_research/) | 2026-11-13 | `pa_consistency_research` | Research and verification packet. States that no machine below 196 states has been validated. | 110 | 9 | 0 | 2 | 11 |
| [`pa_tm_comparison_and_reductions`](pa_tm_comparison_and_reductions/) | 2026-11-13 | `pa_tm_research` | Comparison and new rewrites, a research snapshot. | 120 | 25 | 0 | 5 | 51 |
| [`pa_tm_extended_research_2026-11-13`](pa_tm_extended_research_2026-11-13/) | 2026-11-13 | `pa_tm_extended_research_2026-11-13` | Comparison and refined reduction search. States that the smallest accepted count is 196. | 147 | 22 | 0 | 16 | 15 |
| [`conpa_tm_comparison_and_search`](conpa_tm_comparison_and_search/) | 2026-11-13 | `conpa_tm_study` | Comparison and a search below 196. States that none was obtained; files named `195` are rejected or diagnostic candidates. | 397 | 2454 | 0 | 78 | 15 |
| [`pa_consistency_reduction`](pa_consistency_reduction/) | 2026-11-13 | `pa_consistency_reduction` | Comparison and reduction experiments. States two new 196-state variants and a shorter source program with a 203-state implementation. | 237 | 2141 | 0 | 51 | 41 |
| [`pa_consistency_comparison_2026_11_13`](pa_consistency_comparison_2026_11_13/) | 2026-11-13 | `pa_consistency_comparison_2026_11_13` | Comparison and new reduction experiments. States that nothing below 196 was obtained. | 149 | 17 | 0 | 1 | 72 |
| [`PA_consistency_TM_research_2026-11-13`](PA_consistency_TM_research_2026-11-13/) | 2026-11-13 | `pa_tm_reduction_study` | Comparison and new source reductions. States that no machine below 196 is claimed. | 185 | 8 | 0 | 16 | 60 |
| [`pa_consistency_research_2026-11-13_2`](pa_consistency_research_2026-11-13_2/) | 2026-11-13 | `pa_consistency_research_2026-11-13` | Comparison and search below 196. States two new layouts with 196 and 198 states and a command-level reduction. | 203 | 18 | 0 | 33 | 24 |
| [`conpa_tm_study_2026-11-13`](conpa_tm_study_2026-11-13/) | 2026-11-13 | `conpa_tm_study` | Comparison and reduction study. States that nothing below 196 was obtained. | 137 | 1133 | 0 | 2 | 33 |
| [`pa_below196_research`](pa_below196_research/) | 2026-11-13 | `pa_below196_research` | Comparison and reduction experiments. States that nothing below 196 was obtained. | 192 | 10 | 0 | 6 | 50 |
| [`pa_consistency_comparison_and_new196_2026-11-13`](pa_consistency_comparison_and_new196_2026-11-13/) | 2026-11-13 | `pa_consistency_research` | Comparison and reduction research. States that it contains no accepted machine below 196. | 413 | 21 | 0 | 10 | 69 |
| [`pa_tm_research_2026-11-13_2`](pa_tm_research_2026-11-13_2/) | 2026-11-13 | `pa_tm_research_2026-11-13` | Comparison and reduction investigation. States same-size work, failed candidates and nothing below 196. | 131 | 2161 | 0 | 2 | 46 |
| [`pa_consistency_cross_archive`](pa_consistency_cross_archive/) | 2026-11-13 | `pa_consistency_cross_archive` | Cross-archive constructions and reduction search. States that it does not certify a 195-state machine. | 340 | 32 | 0 | 8 | 179 |
| [`pa195_conpa_2026-11-13`](pa195_conpa_2026-11-13/) | 2026-11-13 | `pa195_conpa` | PA195. States a 195-state machine `pa195/pa195.tm` and an article with a PA proof of the equivalence. | 54 | 26 | 0 | 5 | 26 |
| [`pa_consistency_reduction_audit_2026-11-14`](pa_consistency_reduction_audit_2026-11-14/) | 2026-11-13 | `pa_consistency_reduction_audit` | Comparison and reduction audit. States nothing below 196 and no new theorem. | 348 | 20 | 0 | 13 | 12 |
| [`pa_consistency_research_2026-11-14`](pa_consistency_research_2026-11-14/) | 2026-11-13 | `pa_consistency_research` | Comparison and NEG18. States an 18-instruction encoded negation with a compiled machine of 197 states. | 356 | 33 | 0 | 22 | 23 |
| [`PA195_ConPA_research_2026-11-14`](PA195_ConPA_research_2026-11-14/) | 2026-11-13 | `pa_consistency_research` | A 195-state machine. States the primary `machine_195S.tm` and a second table `machine_195C.tm`. | 687 | 44 | 0 | 8 | 589 |
| [`pa195_followup_research`](pa195_followup_research/) | 2026-11-13 | `pa195_followup` | Comparison and searches below 195. States a graph-distinct 195-state machine M195S8 and nothing below 195. | 323 | 57 | 0 | 54 | 81 |
| [`pa194_conpa_2026-11-13`](pa194_conpa_2026-11-13/) | 2026-11-13 | `pa194_conpa` | A 194-state machine. States the table `construction/tables/pa194.tm` and a proof of the equivalence in PA. | 119 | 10 | 0 | 11 | 18 |
| [`pa194_conpa_2026-11-13_2`](pa194_conpa_2026-11-13_2/) | 2026-11-13 | `pa194_conpa` | PA194. States a 194-state machine `pa194/pa194.tm` and an article with a PA proof of the equivalence. | 216 | 44 | 0 | 51 | 30 |
| [`pa195_diagonal_combined_2026-11-13`](pa195_diagonal_combined_2026-11-13/) | 2026-11-13 | `pa195_diagonal_combined` | PA195DC. States a different 195-state machine. | 127 | 26 | 0 | 16 | 6 |
| [`pa194C_conpa_2026-11-13_2`](pa194C_conpa_2026-11-13_2/) | 2026-11-13 | `pa194C_conpa` | PA194C. States a materially different 194-state machine, an article with a PA proof of the equivalence, and nothing below 194. | 261 | 20 | 0 | 29 | 25 |
| [`pa194_new_designs_2026-11-13`](pa194_new_designs_2026-11-13/) | 2026-11-13 | `pa194_cached_research` | Two new 194-state machines, PA194C and PA194CS. States that nothing below 194 was obtained. | 206 | 30 | 0 | 26 | 18 |
| [`pa194c_conpa`](pa194c_conpa/) | 2026-11-13 | `pa194c_conpa` | PA194C, a cached-head 194-state machine. States that no machine below 194 was established. | 177 | 10 | 0 | 42 | 23 |
| [`pa194c_conpa_2026-11-13_1`](pa194c_conpa_2026-11-13_1/) | 2026-11-13 | `pa194c_conpa` | PA194C. States a different 194-state machine and an article with a PA proof of the equivalence. | 171 | 11 | 0 | 29 | 29 |
| [`pa194c_conpa_2026-11-13`](pa194c_conpa_2026-11-13/) | 2026-11-13 | `pa194c_conpa` | PA194C, a cached-head 194-state machine. States an article with a PA proof of the equivalence and nothing below 194. | 352 | 10 | 2 | 30 | 37 |
| [`pa194_radix_family_2026-11-13`](pa194_radix_family_2026-11-13/) | 2026-11-13 | `pa194_radix_family` | New 194-state machines calibrated to Con(PA), a radix family. | 176 | 12 | 0 | 9 | 22 |
| [`pa194j_pa194d_conpa_2026-11-13`](pa194j_pa194d_conpa_2026-11-13/) | 2026-11-13 | `pa194j_pa194d_conpa` | PA194J and PA194D. States two new 194-state machines. | 235 | 4 | 0 | 15 | 635 |
| [`pa194q_conpa_2026-11-13`](pa194q_conpa_2026-11-13/) | 2026-11-13 | `pa194q_conpa` | PA194Q and PA194CSZ. States two new 194-state machines and that no machine below 194 was established. | 189 | 22 | 0 | 22 | 22 |
| [`PA194R_research_2026-11-14`](PA194R_research_2026-11-14/) | 2026-11-13 | `PA194R_research_2026-11-14` | PA194R. States a different 194-state machine with a new decoder layout and that no machine below 194 was verified. | 574 | 11 | 0 | 37 | 246 |
| [`pa194N_conpa_2026-11-13`](pa194N_conpa_2026-11-13/) | 2026-11-13 | `pa194N_conpa_2026-11-13` | PA194N. States a new 194-state machine, an article with a PA proof of the equivalence, and nothing below 194. | 534 | 4 | 0 | 6 | 211 |
| [`pa194zr_conpa_2026-11-13`](pa194zr_conpa_2026-11-13/) | 2026-11-13 | `pa194zr_conpa` | PA194ZR. States a new 194-state machine `machine/pa194zr.tm`, a PA proof of the equivalence, and nothing below 194. | 162 | 21 | 0 | 14 | 211 |
| [`pa194hs_conpa_2026-11-13`](pa194hs_conpa_2026-11-13/) | 2026-11-13 | `pa194hs_conpa_2026-11-13` | PA194HS and PA194H. States two 194-state machines and that no machine below 194 was established. | 119 | 4 | 0 | 13 | 248 |
| [`pa194n5_n6_conpa_2026-11-13`](pa194n5_n6_conpa_2026-11-13/) | 2026-11-13 | none | PA194N5 and PA194N6. States two distinct 194-state machines and claims no machine below 194. | 27 | 5 | 0 | 1 | 4 |
| [`pa194ns_conpa_2026-11-13`](pa194ns_conpa_2026-11-13/) | 2026-11-13 | `pa194ns_conpa_2026-11-13` | PA194NS. States a different 194-state machine and that no machine below 194 was established. | 120 | 12 | 0 | 2 | 671 |
| [`pa194n6_research_2026-11-13`](pa194n6_research_2026-11-13/) | 2026-11-13 | `pa194n6_research_2026-11-13` | PA194N6. States a different 194-state machine and that no machine below 194 was verified. | 108 | 4 | 0 | 8 | 249 |
| [`PA194NS_research`](PA194NS_research/) | 2026-11-13 | `PA194NS_research` | PA194NS and PA194SUMS. States two new 194-state constructions. | 40 | 1 | 0 | 0 | 4 |
| [`pa194haz_research_2026-11-14`](pa194haz_research_2026-11-14/) | 2026-11-13 | `pa194haz_research_2026-11-14` | PA194HA and PA194HAZ. States two 194-state alternatives and that no machine below 194 was obtained. | 108 | 13 | 0 | 1 | 715 |
| [`pa194qn_research_2026-11-13`](pa194qn_research_2026-11-13/) | 2026-11-13 | `pa194qn_research_2026-11-13` | PA194QN. States a distinct 194-state machine and that no verified machine below 194 was found. | 122 | 5 | 0 | 16 | 38 |
| [`pa194h6_conpa_2026-11-13`](pa194h6_conpa_2026-11-13/) | 2026-11-13 | `pa194h6_conpa_2026-11-13` | PA194H6. States a new 194-state machine, an article with a PA proof of the equivalence, and nothing below 194. | 433 | 2 | 0 | 7 | 39 |
| [`pa194dhs_conpa_2026-11-13`](pa194dhs_conpa_2026-11-13/) | 2026-11-13 | `pa194dhs_conpa_2026-11-13` | PA194DHS. States a different 194-state machine and that no machine below 194 was verified. | 132 | 19 | 0 | 13 | 41 |
| [`pa194nq_research_2026-11-13`](pa194nq_research_2026-11-13/) | 2026-11-13 | `pa194nq_research_2026-11-13` | PA194NQ. States a new 194-state machine and claims no machine below 194. | 158 | 10 | 0 | 7 | 40 |
| [`pa194_qns_research_2026-11-13`](pa194_qns_research_2026-11-13/) | 2026-11-13 | `pa194_qns_research_2026-11-13` | PA194QNS. States a new 194-state machine and that no verified construction below 194 was found. | 159 | 7 | 0 | 14 | 769 |
| [`pa194_qradix_research_2026-11-13`](pa194_qradix_research_2026-11-13/) | 2026-11-13 | `pa194_qradix_research` | PA194Q5 and PA194Q6. States two different 194-state machines and that nothing below 194 was obtained. | 212 | 5 | 0 | 24 | 404 |
| [`pa194qh6_conpa_2026-11-13`](pa194qh6_conpa_2026-11-13/) | 2026-11-13 | `pa194qh6_conpa_2026-11-13` | PA194QH6. States a new 194-state composition and that no machine below 194 was obtained. | 151 | 2 | 0 | 2 | 3 |
| [`pa194qns_research_2026-11-13`](pa194qns_research_2026-11-13/) | 2026-11-13 | `pa194qns_research_2026-11-13` | PA194QNS. States a distinct 194-state machine and that no machine below 194 was established. | 217 | 4 | 0 | 15 | 48 |

## Archives still in `docs/incoming`

None. All 61 archives are removed from `docs/incoming`. They remain in the history of
the repository.

Some scripts of the [parent directory](../README.md) open an archive at
`docs/incoming/<archive>.zip` and check the digest of the archive file. Such a script
needs the archive file restored, until it reads the files of this directory instead:

```bash
c=$(git log --diff-filter=D --format=%H -1 -- "docs/incoming/<archive>.zip")
git show "$c^:docs/incoming/<archive>.zip" > "docs/incoming/<archive>.zip"
```

A restored archive is a working copy only; do not commit it.

## Third-party material

The packets contain files derived from James Chang's PA196 and PA209 developments and
from other published sources, under the licence and notice files that each packet ships.
Those files govern the material they name; the repository's root licence does not
replace them.
