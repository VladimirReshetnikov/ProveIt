# Machines in the delivered packets

The packets of this directory contain 4,984 machine tables in files named `*.tm`. Most of
them repeat a machine that another file already gives: packets quote one another, keep
censuses of earlier tables, and ship the same machine under several state numberings.
This page lists the distinct machines. A table that repeats a kept machine is removed
from the directory, and [`OMITTED.tsv`](OMITTED.tsv) names the kept file for each removed
one.

## When two tables are the same machine

All tables use one format: a row `state read write move next` for each state and each
read symbol, and a `next` label without rows is the halting state. Two tables are taken
to be the same machine when one is the other with its states renamed, start state to start
state. Comments, the order of the rows and the label of the halting state do not matter.

- The start is the one declared in a comment of the file (`#! start N`). Without such a
  comment it is state 0 if the states are numbered 0 to n-1, which is the convention the
  packets state for their dense tables.
- Other tables declare no start. These are the tables in native numbering, whose start is
  recorded in a separate file of the packet. Such a table is taken to be a kept machine
  when it is that machine's table with the states renamed and exactly one kept machine
  fits. Otherwise it forms a class of its own kind, marked `table:`, in which tables are
  compared up to renaming of states with no regard to a start.
- The class of a machine is the SHA-256 of its transition list in the order of a traversal
  from the start. For a table whose states are all reachable it equals the
  `graph_class_sha256` of [`archive-audit/catalog.py`](../pa196-vs-u208/archive-audit/catalog.py).
  [`machine_classes.py`](machine_classes.py) computes it for any table.

Three further identifications were tried and merge nothing here: exchanging left and
right throughout, ignoring the symbol written and the move made on a transition into the
halting state, and regarding one table with two different starts. No table occurs with
two starts.

This is a comparison of tables only. Two different classes can still be machines that
halt under the same conditions, and nothing here was run or proved. Machines given only
in another encoding, for example inside a JSON file, are not examined.

## Counts

| | |
|---|---:|
| Table files in the 51 packets | 4,984 |
| Distinct file contents | 682 |
| Distinct machines (classes with a start) | 444 |
| Classes of tables that declare no start and fit no kept machine | 46 |
| Files kept here, one for each class | 489 |
| Classes kept in the upstream snapshot instead | 1 |
| Files removed: same bytes as the kept file | 2,673 |
| Files removed: states renamed | 1,157 |
| Files removed: states renamed, the file declares no start | 665 |

The kept file of a class is one that declares a start if there is one, from the packet
that arrived first; among several, a file outside census, reference and input directories
is preferred. A removed table in native numbering therefore has its machine kept in dense
numbering; the label files of the packet that relate the two numberings are still here.
The class `43115a87740f` is the table [`../jamesyc-upstream/pa196/data/pa196.tm`](../jamesyc-upstream/pa196/data/pa196.tm) of the upstream snapshot, and every copy of it in the packets is removed.

Classes by number of states reachable from the start:

| States | 2 | 4 | 194 | 195 | 196 | 197 | 198 | 199 | 200 | 201 | 202 | 203 | 206 | 207 | 208 | 209 | 210 | 211 | 212 | 213 | 214 | 215 | 217 | 218 | 219 | 220 | 221 | 222 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Classes | 1 | 2 | 34 | 17 | 99 | 15 | 5 | 4 | 2 | 8 | 17 | 5 | 1 | 57 | 142 | 13 | 19 | 11 | 14 | 9 | 4 | 2 | 1 | 1 | 3 | 2 | 1 | 1 |

## Tables that the packets' READMEs name

A packet usually names its proposed tables in its README. The 69 table files named in the
READMEs of 35 packets are 48 distinct classes. This is the closest mechanical reading of
"the machines the packets propose"; a README also names tables that the packet rejects or
only compares, and the names of the files show most of those. The other 16 packets name no
table file in their README.

| States | Class | Kept file | Named by |
|---:|---|---|---|
| 194 | `73170fc8df96` | [`pa194_conpa_2026-11-13/construction/tables/pa194_AD.tm`](pa194_conpa_2026-11-13/construction/tables/pa194_AD.tm) | `pa194_conpa_2026-11-13`: `construction/tables/pa194_AD.tm` |
| 194 | `dd2d4a04364c` | [`pa194_conpa_2026-11-13/construction/tables/pa194.tm`](pa194_conpa_2026-11-13/construction/tables/pa194.tm) | `pa194_conpa_2026-11-13`: `construction/tables/pa194.tm`<br>`pa194n5_n6_conpa_2026-11-13`: `reference/pa194.native.tm` |
| 194 | `10ab28316408` | [`pa194_conpa_2026-11-13_2/pa194/pa194.tm`](pa194_conpa_2026-11-13_2/pa194/pa194.tm) | `pa194_conpa_2026-11-13_2`: `pa194/pa194.tm` |
| 194 | `a4ad9e167b34` | [`pa194_new_designs_2026-11-13/secondary/pa194CS/machine/pa194CS.tm`](pa194_new_designs_2026-11-13/secondary/pa194CS/machine/pa194CS.tm) | `pa194_new_designs_2026-11-13`: `secondary/pa194CS/machine/pa194CS.tm` |
| 194 | `c4ecc511bd51` | [`pa194c_conpa_2026-11-13/tables/pa194C.tm`](pa194c_conpa_2026-11-13/tables/pa194C.tm) | `pa194C_conpa_2026-11-13_2`: `construction/output/pa194C.tm`<br>`pa194_new_designs_2026-11-13`: `construction/candidate/pa194C.tm`<br>`pa194c_conpa`: `machine/pa194C.native.tm`<br>`pa194c_conpa`: `machine/pa194C.tm`<br>`pa194c_conpa_2026-11-13`: `tables/pa194C.native.tm`<br>`pa194c_conpa_2026-11-13`: `tables/pa194C.tm`<br>`pa194c_conpa_2026-11-13_1`: `construction/tables/pa194c.tm` |
| 194 | `5fa34d80085c` | [`pa194_radix_family_2026-11-13/machines/6/machine.tm`](pa194_radix_family_2026-11-13/machines/6/machine.tm) | `pa194_radix_family_2026-11-13`: `machines/6/machine.tm` |
| 194 | `689af6ecb7a2` | [`pa194_radix_family_2026-11-13/machines/4R/machine.tm`](pa194_radix_family_2026-11-13/machines/4R/machine.tm) | `pa194_radix_family_2026-11-13`: `machines/4R/machine.tm` |
| 194 | `6bb94355af4f` | [`pa194j_pa194d_conpa_2026-11-13/logical_emitter/machine/pa194d.tm`](pa194j_pa194d_conpa_2026-11-13/logical_emitter/machine/pa194d.tm) | `pa194j_pa194d_conpa_2026-11-13`: `logical_emitter/machine/pa194d.tm` |
| 194 | `975d853c52ad` | [`pa194j_pa194d_conpa_2026-11-13/construction/machine/pa194j.tm`](pa194j_pa194d_conpa_2026-11-13/construction/machine/pa194j.tm) | `pa194j_pa194d_conpa_2026-11-13`: `construction/machine/pa194j.tm` |
| 194 | `b9a25085b2a5` | [`pa194_radix_family_2026-11-13/machines/5/machine.tm`](pa194_radix_family_2026-11-13/machines/5/machine.tm) | `pa194_radix_family_2026-11-13`: `machines/5/machine.tm` |
| 194 | `bd9391ce305d` | [`pa194_radix_family_2026-11-13/search/pa194CSZ/machine/pa194CSZ.tm`](pa194_radix_family_2026-11-13/search/pa194CSZ/machine/pa194CSZ.tm) | `pa194q_conpa_2026-11-13`: `secondary/pa194csz/machine_csz/pa194CSZ.tm` |
| 194 | `f7dfe50b70eb` | [`pa194q_conpa_2026-11-13/machine/pa194q.tm`](pa194q_conpa_2026-11-13/machine/pa194q.tm) | `pa194q_conpa_2026-11-13`: `machine/pa194q.tm` |
| 194 | `6b61cd11e270` | [`PA194R_research_2026-11-14/machines/PA194R/machine.tm`](PA194R_research_2026-11-14/machines/PA194R/machine.tm) | `PA194R_research_2026-11-14`: `machines/PA194R/machine.native.tm`<br>`PA194R_research_2026-11-14`: `machines/PA194R/machine.tm` |
| 194 | `a464367a4a12` | [`pa194N_conpa_2026-11-13/construction/machine/pa194N.tm`](pa194N_conpa_2026-11-13/construction/machine/pa194N.tm) | `pa194N_conpa_2026-11-13`: `construction/machine/pa194N.tm` |
| 194 | `58e166b2c7a4` | [`pa194zr_conpa_2026-11-13/machine/pa194zr.tm`](pa194zr_conpa_2026-11-13/machine/pa194zr.tm) | `pa194zr_conpa_2026-11-13`: `machine/pa194zr.native.tm`<br>`pa194zr_conpa_2026-11-13`: `machine/pa194zr.tm` |
| 194 | `4970232fdb7d` | [`pa194ns_conpa_2026-11-13/machine/machine.tm`](pa194ns_conpa_2026-11-13/machine/machine.tm) | `pa194hs_conpa_2026-11-13`: `machines/PA194HS/machine.tm`<br>`pa194ns_conpa_2026-11-13`: `machine/machine.tm` |
| 194 | `8a4dfb7d72eb` | [`pa194hs_conpa_2026-11-13/machines/PA194H/machine.tm`](pa194hs_conpa_2026-11-13/machines/PA194H/machine.tm) | `pa194hs_conpa_2026-11-13`: `machines/PA194H/machine.tm` |
| 194 | `96b79e56650d` | [`pa194n5_n6_conpa_2026-11-13/machines/pa194n5.tm`](pa194n5_n6_conpa_2026-11-13/machines/pa194n5.tm) | `pa194n5_n6_conpa_2026-11-13`: `machines/pa194n5.tm` |
| 194 | `75c615697742` | [`pa194n5_n6_conpa_2026-11-13/machines/pa194n6.tm`](pa194n5_n6_conpa_2026-11-13/machines/pa194n6.tm) | `pa194n6_research_2026-11-13`: `machine/machine.tm` |
| 195 | `654ddcd43007` | [`pa_consistency_research/data/rejected195.native.tm`](pa_consistency_research/data/rejected195.native.tm) | `pa_consistency_research`: `data/rejected195.native.tm` |
| 195 | `a76ce33e76ac` | [`pa195_conpa_2026-11-13/pa195/pa195.tm`](pa195_conpa_2026-11-13/pa195/pa195.tm) | `pa195_conpa_2026-11-13`: `pa195/pa195.tm` |
| 195 | `4f5d8b016ec2` | [`PA195_ConPA_research_2026-11-14/machine_195C.tm`](PA195_ConPA_research_2026-11-14/machine_195C.tm) | `PA195_ConPA_research_2026-11-14`: `machine_195C.tm` |
| 195 | `96862fab2a93` | [`PA195_ConPA_research_2026-11-14/machine_195S.tm`](PA195_ConPA_research_2026-11-14/machine_195S.tm) | `PA195_ConPA_research_2026-11-14`: `machine_195S.tm` |
| 195 | `64269e430273` | [`pa195_followup_research/machine_195s8/pa195_scanner8.tm`](pa195_followup_research/machine_195s8/pa195_scanner8.tm) | `pa195_followup_research`: `machine_195s8/pa195_scanner8.tm` |
| 195 | `501c24af5db3` | [`pa195_diagonal_combined_2026-11-13/machine/machine.tm`](pa195_diagonal_combined_2026-11-13/machine/machine.tm) | `pa195_diagonal_combined_2026-11-13`: `machine/machine.native.tm`<br>`pa195_diagonal_combined_2026-11-13`: `machine/machine.tm` |
| 196 | `3657e60366bf` | [`pa_consistency_research/data/variant196.tm`](pa_consistency_research/data/variant196.tm) | `pa_consistency_research`: `data/variant196.native.tm`<br>`pa_consistency_research`: `data/variant196.tm` |
| 196 | `663dc3688f76` | [`pa_consistency_reduction/comparison/audit/h_catalan_node170_3_133_37.tm`](pa_consistency_reduction/comparison/audit/h_catalan_node170_3_133_37.tm) | `pa_consistency_reduction`: `comparison/audit/h_catalan_node170_3_133_37.tm` |
| 196 | `8b0e28045992` | [`pa_consistency_reduction/comparison/audit/rebracketed196_dense.tm`](pa_consistency_reduction/comparison/audit/rebracketed196_dense.tm) | `pa_consistency_reduction`: `comparison/audit/rebracketed196_dense.tm` |
| 196 | `37aa79c9c241` | [`pa_consistency_research_2026-11-13_2/rotated196/machine.tm`](pa_consistency_research_2026-11-13_2/rotated196/machine.tm) | `pa_consistency_research_2026-11-13_2`: `rotated196/machine.tm` |
| 196 | `6a6c70099fd3` | [`conpa_tm_study_2026-11-13/machines/h_only_mp_h.tm`](conpa_tm_study_2026-11-13/machines/h_only_mp_h.tm) | `conpa_tm_study_2026-11-13`: `machines/h_only_mp_h.tm` |
| 196 | `43115a87740f` | [`../jamesyc-upstream/pa196/data/pa196.tm`](../jamesyc-upstream/pa196/data/pa196.tm) | `pa_below196_research`: `physical_search/pa196.tm` |
| 196 | `478a44709797` | [`pa_tm_research_2026-11-13_2/verification/zero_jump_machine/machines/zerojump196.tm`](pa_tm_research_2026-11-13_2/verification/zero_jump_machine/machines/zerojump196.tm) | `pa_tm_research_2026-11-13_2`: `verification/zero_jump_machine/machines/zerojump196.tm` |
| 196 | `9570bee91984` | [`pa_consistency_comparison_and_new196_2026-11-13/axioms/separate196/machine.tm`](pa_consistency_comparison_and_new196_2026-11-13/axioms/separate196/machine.tm) | `pa_consistency_comparison_and_new196_2026-11-13`: `axioms/separate196/machine.tm` |
| 196 | `a5a7506acbd5` | [`pa_consistency_comparison_and_new196_2026-11-13/axioms/search/scanner_best196.tm`](pa_consistency_comparison_and_new196_2026-11-13/axioms/search/scanner_best196.tm) | `pa_consistency_comparison_and_new196_2026-11-13`: `axioms/search/scanner_best196.tm` |
| 196 | `eefe38c5c291` | [`pa_consistency_comparison_and_new196_2026-11-13/axioms/diagonal196/machine.tm`](pa_consistency_comparison_and_new196_2026-11-13/axioms/diagonal196/machine.tm) | `pa_consistency_comparison_and_new196_2026-11-13`: `axioms/diagonal196/machine.tm` |
| 196 | `319fb9fd819a` | [`pa_consistency_cross_archive/machines/separate_combined/machine.tm`](pa_consistency_cross_archive/machines/separate_combined/machine.tm) | `pa_consistency_cross_archive`: `machines/separate_combined/machine.tm` |
| 196 | `350d3177d017` | [`pa_consistency_cross_archive/machines/diagonal_combined_zerojump/machine.tm`](pa_consistency_cross_archive/machines/diagonal_combined_zerojump/machine.tm) | `pa_consistency_cross_archive`: `machines/diagonal_combined_zerojump/machine.tm` |
| 196 | `b9ac9f989be1` | [`pa_consistency_cross_archive/machines/separate_combined_zerojump/machine.tm`](pa_consistency_cross_archive/machines/separate_combined_zerojump/machine.tm) | `pa_consistency_cross_archive`: `machines/separate_combined_zerojump/machine.tm` |
| 196 | `c3af3a720f99` | [`pa_consistency_cross_archive/machines/diagonal_combined/machine.tm`](pa_consistency_cross_archive/machines/diagonal_combined/machine.tm) | `pa_consistency_cross_archive`: `machines/diagonal_combined/machine.tm` |
| 197 | `table:035009006dfb` | [`conpa_tm_study_2026-11-13/machines/direct_negation197.tm`](conpa_tm_study_2026-11-13/machines/direct_negation197.tm) | `conpa_tm_study_2026-11-13`: `machines/direct_negation197.tm` |
| 198 | `0d1437ef851a` | [`pa_consistency_research_2026-11-13_2/diagonal198/machine.tm`](pa_consistency_research_2026-11-13_2/diagonal198/machine.tm) | `pa_consistency_research_2026-11-13_2`: `diagonal198/machine.tm` |
| 199 | `0a91cd1636eb` | [`pa_consistency_research_2026-11-13/diagonal199/machine.tm`](pa_consistency_research_2026-11-13/diagonal199/machine.tm) | `pa_consistency_research_2026-11-13`: `diagonal199/machine.native.tm`<br>`pa_consistency_research_2026-11-13`: `diagonal199/machine.tm` |
| 201 | `table:006328832b94` | [`pa194c_conpa_2026-11-13/tables/pa194C_raw201.native.tm`](pa194c_conpa_2026-11-13/tables/pa194C_raw201.native.tm) | `pa194c_conpa_2026-11-13`: `tables/pa194C_raw201.native.tm` |
| 203 | `511853be829e` | [`pa_consistency_reduction/comparison/audit/integrated_gate203_dense.tm`](pa_consistency_reduction/comparison/audit/integrated_gate203_dense.tm) | `pa_consistency_reduction`: `comparison/audit/integrated_gate203_dense.tm` |
| 206 | `ad1d34d387ad` | [`pa_consistency_reduction/comparison/audit/integrated_gate206_dense.tm`](pa_consistency_reduction/comparison/audit/integrated_gate206_dense.tm) | `pa_consistency_reduction`: `comparison/audit/integrated_gate206_dense.tm` |
| 208 | `735b413e0795` | [`U208_ConPA_Conditional_Context_2026-10-29/machine/u208.tm`](U208_ConPA_Conditional_Context_2026-10-29/machine/u208.tm) | `U208_ConPA_Conditional_Context_2026-10-29`: `machine/u208.native.tm`<br>`U208_ConPA_Conditional_Context_2026-10-29`: `machine/u208.tm`<br>`U208_ConPA_Entry_Context_2026-10-29`: `machine/u208.tm`<br>`U208_ConPA_History_2026-10-29`: `machine/u208.native.tm`<br>`U208_ConPA_History_2026-10-29`: `machine/u208.tm`<br>`U208_ConPA_2026-10-29`: `machine/u208.tm`<br>`u208_research_2026-10-29`: `machine/variant_plain/u208.tm`<br>`pa_consistency_research`: `data/u208_01.native.tm` |
| 208 | `b6396833ab64` | [`U208_ConPA_Conditional_Context_2026-10-29/alternative/u208.tm`](U208_ConPA_Conditional_Context_2026-10-29/alternative/u208.tm) | `U208_ConPA_Entry_Context_2026-10-29`: `machine/u208_compatibility.tm`<br>`u208_research_2026-10-29`: `machine/u208.tm` |
| 209 | `b5fb01b40020` | [`U208_ConPA_Conditional_Context_2026-10-29/machine_parent/u209.tm`](U208_ConPA_Conditional_Context_2026-10-29/machine_parent/u209.tm) | `U208_ConPA_Entry_Context_2026-10-29`: `baseline/u209.native.tm` |

5 of these classes are named by more than one packet:

- `4970232fdb7d`, 194 states: 2 packets (`pa194hs_conpa_2026-11-13`, `pa194ns_conpa_2026-11-13`).
- `c4ecc511bd51`, 194 states: 5 packets (`pa194C_conpa_2026-11-13_2`, `pa194_new_designs_2026-11-13`, `pa194c_conpa`, `pa194c_conpa_2026-11-13`, `pa194c_conpa_2026-11-13_1`).
- `dd2d4a04364c`, 194 states: 2 packets (`pa194_conpa_2026-11-13`, `pa194n5_n6_conpa_2026-11-13`).
- `735b413e0795`, 208 states: 6 packets (`U208_ConPA_Conditional_Context_2026-10-29`, `U208_ConPA_Entry_Context_2026-10-29`, `U208_ConPA_History_2026-10-29`, `U208_ConPA_2026-10-29`, `u208_research_2026-10-29`, `pa_consistency_research`).
- `b6396833ab64`, 208 states: 2 packets (`U208_ConPA_Entry_Context_2026-10-29`, `u208_research_2026-10-29`).

## Files

- [`MACHINES.tsv`](MACHINES.tsv): one row for each of the 490 classes, with the number of states, the
  packet that delivered it first, the kept file, in how many packets and files it occurred,
  the file names it had, and files of the research tree with the same machine.
- [`MACHINE_FILES.tsv`](MACHINE_FILES.tsv): one row for each of the 4,984 table files as delivered, with its
  SHA-256, its class, its start and whether it is kept.
- [`machine_classes.py`](machine_classes.py): prints the class of a table.

To see whether a new table is already here, compute its class and look it up:

```bash
py machine_classes.py new_table.tm
```

and search `MACHINES.tsv` for the value after `machine=`, or for `table:` followed by the
value after `table=` when the table declares no start.
