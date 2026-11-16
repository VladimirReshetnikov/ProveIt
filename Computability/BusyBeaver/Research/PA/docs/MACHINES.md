# Machines in the delivered packets

The packets of this directory contain 26,242 machine tables in files named `*.tm`. Most of
them repeat a machine that another file already gives: packets quote one another, keep
censuses of earlier tables, and ship the same machine under several state numberings.
This page lists the distinct machines. A table that repeats a kept machine is removed
from the directory, and [`OMITTED.tsv`](OMITTED.tsv) names the kept file for each removed
one.

## When two tables are the same machine

All tables use one format: a row `state read write move next` for each state and each
read symbol, and a `next` label without rows is the halting state. Two tables are taken
to be the same machine when one is the other with its states renamed. Comments, the
order of the rows and the label of the halting state do not matter.

The start state is not part of the comparison, because most files do not say what it is.

- A file declares its start only by a comment (`#! start N`).
- The packets state that their dense tables, numbered 0 to n-1, start at state 0. That is
  a convention of the packets and not a fact of the file.
- Tables in native numbering record the start in a separate file of the packet.
- One packet (`pa194haz_research_2026-11-14`) ships native tables renumbered 0 to n-1, and
  in those state 0 is not the start. Read with the convention, such a file would look like
  a new machine although it is a kept one.

So one table with two starts would count once. Among the files that declare a start in a
comment this does not occur. The removed files whose state 0 is not the start of the kept
file are counted below; each is the kept table renumbered.

A class is named by the SHA-256 of the transition list of its kept file in the order of a
traversal from that file's start. For a table whose states are all reachable this is the
`graph_class_sha256` of [`archive-audit/catalog.py`](../verification/other-machines/pa196-vs-u208/archive-audit/catalog.py).
A class whose kept file has no start is named `table:` followed by the hash that does not
depend on the start. [`machine_classes.py`](machine_classes.py) computes both hashes.

For the first 47 packets two further identifications were tried and merged nothing:
exchanging left and right throughout, and ignoring the symbol written and the move made on
a transition into the halting state.

This is a comparison of tables only. Two different classes can still be machines that
halt under the same conditions, and nothing here was run or proved. Machines given only
in another encoding, for example inside a JSON file, are not examined.

## Counts

| | |
|---|---:|
| Table files in the 112 packets | 26,242 |
| Distinct file contents | 1,739 |
| Classes | 1295 |
| Classes whose kept file has a start | 655 |
| Classes whose kept file declares no start | 640 |
| Files kept here | 1294 |
| Classes kept in the upstream snapshot instead | 1 |
| Files removed: same bytes as the kept file | 19,945 |
| Files removed: states renamed, same start | 1,606 |
| Files removed: states renamed, the file declares no start | 3,090 |
| Files removed: states renamed, the kept file declares no start | 204 |
| Files removed: states renamed, state 0 of the file is not the start of the kept file | 103 |

The kept file of a class is one with a start if there is one, from the packet that
arrived first; among several, a file outside census, reference and input directories is
preferred. A removed table in native numbering therefore has its machine kept in dense
numbering; the label files of the packet that relate the two numberings are still here.
The class `43115a87740f` is the [PA196 table](../verification/other-machines/jamesyc-upstream/pa196/data/pa196.tm) of the upstream snapshot, and every copy of it in the packets is removed.

Classes by number of states reachable from the start:

| States | 1 | 2 | 3 | 4 | 8 | 13 | 130 | 131 | 132 | 193 | 194 | 195 | 196 | 197 | 198 | 199 | 200 | 201 | 202 | 203 | 204 | 205 | 206 | 207 | 208 | 209 | 210 | 211 | 212 | 213 | 214 | 215 | 217 | 218 | 219 | 220 | 221 | 222 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Classes | 15 | 7 | 6 | 6 | 1 | 1 | 3 | 6 | 1 | 67 | 624 | 31 | 106 | 16 | 6 | 4 | 4 | 30 | 49 | 17 | 7 | 1 | 2 | 58 | 142 | 13 | 19 | 12 | 14 | 9 | 4 | 3 | 2 | 1 | 3 | 3 | 1 | 1 |

## Tables that the packets' READMEs name

A packet usually names its proposed tables in its README. The 159 table files named in the
READMEs of 83 packets are 120 distinct classes. This is the closest mechanical reading of
"the machines the packets propose"; a README also names tables that the packet rejects or
only compares, and the names of the files show most of those. The other 29 packets name no
table file in their README.

| States | Class | Kept file | Named by |
|---:|---|---|---|
| 193 | `table:00a7e2200f67` | [`pa_sub194_research_2026-11-13/runtime193/runtime193.native.tm`](pa_sub194_research_2026-11-13/runtime193/runtime193.native.tm) | `pa194_tdy_2026-11-14`: `research/runtime193_rejected.native.tm` |
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
| 194 | `11c65a856352` | [`pa194qn_research_2026-11-13/machine/machine.tm`](pa194qn_research_2026-11-13/machine/machine.tm) | `pa194qn_research_2026-11-13`: `machine/machine.tm`<br>`pa194nq_research_2026-11-13`: `machine/machine.tm` |
| 194 | `56f98addf327` | [`pa194haz_research_2026-11-14/machine/pa194haz.tm`](pa194haz_research_2026-11-14/machine/pa194haz.tm) | `pa194haz_research_2026-11-14`: `machine/pa194haz.native.tm`<br>`pa194haz_research_2026-11-14`: `machine/pa194haz.tm` |
| 194 | `5b95f7a94c20` | [`pa194h6_conpa_2026-11-13/machine/machine.tm`](pa194h6_conpa_2026-11-13/machine/machine.tm) | `pa194h6_conpa_2026-11-13`: `machine/machine.tm` |
| 194 | `74486d031f84` | [`pa194dhs_conpa_2026-11-13/machine/machine.tm`](pa194dhs_conpa_2026-11-13/machine/machine.tm) | `pa194dhs_conpa_2026-11-13`: `machine/machine.tm` |
| 194 | `120ba3f800e9` | [`pa194qh6_conpa_2026-11-13/machine/machine.tm`](pa194qh6_conpa_2026-11-13/machine/machine.tm) | `pa194qh6_conpa_2026-11-13`: `machine/machine.native.tm`<br>`pa194qh6_conpa_2026-11-13`: `machine/machine.tm` |
| 194 | `cd37d8a0c83b` | [`pa194_qradix_research_2026-11-13/machines/PA194Q6/machine.tm`](pa194_qradix_research_2026-11-13/machines/PA194Q6/machine.tm) | `pa194_qradix_research_2026-11-13`: `machines/PA194Q6/machine.tm` |
| 194 | `da81e6f6524c` | [`pa194qns_research_2026-11-13/machines/PA194QNS/machine.tm`](pa194qns_research_2026-11-13/machines/PA194QNS/machine.tm) | `pa194_qns_research_2026-11-13`: `construction/machine/machine.native.tm`<br>`pa194_qns_research_2026-11-13`: `construction/machine/machine.tm`<br>`pa194qns_research_2026-11-13`: `machines/PA194QNS/machine.tm` |
| 194 | `dc771eb917f0` | [`pa194_qradix_research_2026-11-13/machines/PA194Q5/machine.tm`](pa194_qradix_research_2026-11-13/machines/PA194Q5/machine.tm) | `pa194_qradix_research_2026-11-13`: `machines/PA194Q5/machine.tm` |
| 194 | `2ad1a833e390` | [`pa194qh_conpa_2026-11-13/machine/machine.tm`](pa194qh_conpa_2026-11-13/machine/machine.tm) | `pa194qh_conpa_2026-11-13`: `machine/machine.native.tm`<br>`pa194qh_conpa_2026-11-13`: `machine/machine.tm` |
| 194 | `11036606a24f` | [`pa194_ax11_research_2026-11-14/primary/machine/machine.tm`](pa194_ax11_research_2026-11-14/primary/machine/machine.tm) | `pa194_ax11_research_2026-11-14`: `primary/machine/machine.tm` |
| 194 | `de3420f4caa1` | [`pa194_qh5_research_2026-11-14/machine/machine.tm`](pa194_qh5_research_2026-11-14/machine/machine.tm) | `pa194_ax11_research_2026-11-14`: `secondary_qh5/machine/machine.tm`<br>`pa194_qh5_research_2026-11-14`: `machine/machine.native.tm`<br>`pa194_qh5_research_2026-11-14`: `machine/machine.tm` |
| 194 | `0acff616b651` | [`pa194qn_2026-11-14/machines/PA194QN5/machine.tm`](pa194qn_2026-11-14/machines/PA194QN5/machine.tm) | `pa194qn_2026-11-14`: `machines/PA194QN5/machine.tm` |
| 194 | `6881f3df3909` | [`pa194qn6_conpa_2026-11-14/machine/machine.tm`](pa194qn6_conpa_2026-11-14/machine/machine.tm) | `pa194qn6_conpa_2026-11-14`: `machine/machine.native.tm`<br>`pa194qn6_conpa_2026-11-14`: `machine/machine.tm`<br>`pa194qn_2026-11-14`: `machines/PA194QN6/machine.tm` |
| 194 | `a2c7a4b6e66e` | [`pa194qhs_conpa_2026-11-14/machine/machine.tm`](pa194qhs_conpa_2026-11-14/machine/machine.tm) | `pa194qhs_conpa_2026-11-14`: `machine/machine.native.tm`<br>`pa194qhs_conpa_2026-11-14`: `machine/machine.tm` |
| 194 | `fec2397a2b3d` | [`pa194h5_research_2026-11-14/machine/machine.tm`](pa194h5_research_2026-11-14/machine/machine.tm) | `pa194h5_research_2026-11-14`: `machine/machine.native.tm`<br>`pa194h5_research_2026-11-14`: `machine/machine.tm` |
| 194 | `55224b3a6d71` | [`pa194ax11q6_2026-11-14/candidate/machine/machine.tm`](pa194ax11q6_2026-11-14/candidate/machine/machine.tm) | `pa194ax11q6_2026-11-14`: `candidate/machine/machine.tm` |
| 194 | `63dfd3f5f5a8` | [`pa194p5_research_2026-11-14/machine/pa194p5.tm`](pa194p5_research_2026-11-14/machine/pa194p5.tm) | `pa194p5_research_2026-11-14`: `machine/pa194p5.native.tm`<br>`pa194p5_research_2026-11-14`: `machine/pa194p5.tm` |
| 194 | `9a39109ff1e3` | [`pa194_ax11qh5_2026-11-14/machine/machine.tm`](pa194_ax11qh5_2026-11-14/machine/machine.tm) | `pa194_ax11qh5_2026-11-14`: `machine/machine.tm`<br>`pa194_research_2026-11-14`: `ax11qh5/AX11QH5/machine.tm` |
| 194 | `a452824fe922` | [`PA194B_PA194G_research_2026-11-14/generalizer/machine.tm`](PA194B_PA194G_research_2026-11-14/generalizer/machine.tm) | `PA194B_PA194G_research_2026-11-14`: `generalizer/machine.tm` |
| 194 | `b0c40750310c` | [`pa194_tdy_2026-11-14/artifacts/pa194_tdy.tm`](pa194_tdy_2026-11-14/artifacts/pa194_tdy.tm) | `pa194_tdy_2026-11-14`: `artifacts/pa194_tdy.tm` |
| 194 | `e8899f4f7397` | [`PA194B_PA194G_research_2026-11-14/machine/pa194B.tm`](PA194B_PA194G_research_2026-11-14/machine/pa194B.tm) | `PA194B_PA194G_research_2026-11-14`: `machine/pa194B.tm` |
| 194 | `28c730d82cb7` | [`pa1944l_research_2026-11-14/machine/machine.tm`](pa1944l_research_2026-11-14/machine/machine.tm) | `pa1944l_research_2026-11-14`: `machine/machine.tm` |
| 194 | `5938e48b03b3` | [`pa194_ax11s_study/machine/machine.tm`](pa194_ax11s_study/machine/machine.tm) | `pa194_ax11s_study`: `machine/machine.tm` |
| 194 | `6faef480d7a4` | [`pa194_ax11qh_research_2026-11-14/candidate/machine/machine.tm`](pa194_ax11qh_research_2026-11-14/candidate/machine/machine.tm) | `pa194_ax11qh_research_2026-11-14`: `candidate/machine/machine.tm` |
| 194 | `7876dd099992` | [`pa194_ax11h_research_2026-11-14/machine/machine.tm`](pa194_ax11h_research_2026-11-14/machine/machine.tm) | `pa194_ax11h_research_2026-11-14`: `machine/machine.tm` |
| 194 | `f255d4bba42c` | [`pa194_research_2026-11-14/hx194/machine/pa194hx.tm`](pa194_research_2026-11-14/hx194/machine/pa194hx.tm) | `pa194_research_2026-11-14`: `hx194/machine/pa194hx.tm` |
| 194 | `812bef83cf5e` | [`pa194_ax11qh4_research_2026-11-14/construction/AX11QH4L/machine.tm`](pa194_ax11qh4_research_2026-11-14/construction/AX11QH4L/machine.tm) | `pa194_ax11qh4_research_2026-11-14`: `construction/AX11QH4L/machine.tm` |
| 194 | `fd8c201cb3b8` | [`pa194_ax11qh4_research_2026-11-14/construction/AX11QH4R/machine.tm`](pa194_ax11qh4_research_2026-11-14/construction/AX11QH4R/machine.tm) | `pa194_ax11qh4_research_2026-11-14`: `construction/AX11QH4R/machine.tm` |
| 194 | `32c41d8342d2` | [`pa194_ax11g_research_2026-11-14/machine/machine.tm`](pa194_ax11g_research_2026-11-14/machine/machine.tm) | `pa194_ax11g_research_2026-11-14`: `machine/machine.tm` |
| 194 | `0be84784c2d0` | [`pa194_sel_ax11gh_research_2026-11-14/machines/SEL/machine/pa194sel.tm`](pa194_sel_ax11gh_research_2026-11-14/machines/SEL/machine/pa194sel.tm) | `pa194_sel_ax11gh_research_2026-11-14`: `machines/SEL/machine/pa194sel.tm` |
| 194 | `23c01c5e8510` | [`pa194_ax11gh_research_2026-11-14_1/acceleration/machines/PA194AX11GHSF/machine.tm`](pa194_ax11gh_research_2026-11-14_1/acceleration/machines/PA194AX11GHSF/machine.tm) | `pa194_ax11gh_research_2026-11-14_1`: `acceleration/machines/PA194AX11GHSF/machine.tm` |
| 194 | `52f94a71722b` | [`pa194_ax11gh_research_2026-11-14/machines/PA194AX11GH/machine.tm`](pa194_ax11gh_research_2026-11-14/machines/PA194AX11GH/machine.tm) | `pa194_ax11gh_research_2026-11-14_1`: `machines/PA194AX11GH/machine.tm`<br>`pa194_research_2026-11-14_2`: `construction/AX11QGH/machine/machine.tm`<br>`pa194_sel_ax11gh_research_2026-11-14`: `machines/AX11GH/machine/machine.tm`<br>`pa_conpa_research_2026-11-14`: `machines/PA194AX11GH/machine.tm` |
| 194 | `65f6eb4aaf7b` | [`pa194_ax11gh_research_2026-11-14/machines/PA194AX11GHS/machine.tm`](pa194_ax11gh_research_2026-11-14/machines/PA194AX11GHS/machine.tm) | `pa194_ax11gh_research_2026-11-14_1`: `machines/PA194AX11GHS/machine.tm`<br>`pa_conpa_research_2026-11-14`: `machines/PA194AX11GHS/machine.tm` |
| 194 | `6a142bf914d5` | [`pa194_research_2026-11-14_2/construction/AX11HR/machine/machine.tm`](pa194_research_2026-11-14_2/construction/AX11HR/machine/machine.tm) | `pa194_research_2026-11-14_2`: `construction/AX11HR/machine/machine.tm` |
| 194 | `6a42aa001e8d` | [`pa194_loop_continuation_research_2026-11-14/additional/PA194LC_AX11H/machine.tm`](pa194_loop_continuation_research_2026-11-14/additional/PA194LC_AX11H/machine.tm) | `pa194_loop_continuation_research_2026-11-14`: `additional/PA194LC_AX11H/machine.tm` |
| 194 | `ffa4141d12e4` | [`pa194_ax11gh_research_2026-11-14_1/acceleration/machines/PA194AX11GHF/machine.tm`](pa194_ax11gh_research_2026-11-14_1/acceleration/machines/PA194AX11GHF/machine.tm) | `pa194_ax11gh_research_2026-11-14_1`: `acceleration/machines/PA194AX11GHF/machine.tm` |
| 194 | `05ee6f2fd3af` | [`pa194_comparison_and_new_designs_2026-11-15/composites/machines/PA194LC_AX11H_SF/machine.tm`](pa194_comparison_and_new_designs_2026-11-15/composites/machines/PA194LC_AX11H_SF/machine.tm) | `pa194_comparison_and_new_designs_2026-11-15`: `composites/machines/PA194LC_AX11H_SF/machine.tm` |
| 194 | `c00c22ecf0b4` | [`pa194_comparison_and_new_designs_2026-11-15/composites/machines/PA194AX11H_SF/machine.tm`](pa194_comparison_and_new_designs_2026-11-15/composites/machines/PA194AX11H_SF/machine.tm) | `pa194_comparison_and_new_designs_2026-11-15`: `composites/machines/PA194AX11H_SF/machine.tm` |
| 194 | `bcafa796bd5e` | [`pa194_loop_return_2026-11-14/machines/PA194LCG/machine.tm`](pa194_loop_return_2026-11-14/machines/PA194LCG/machine.tm) | `pa194_loop_return_2026-11-14`: `machines/PA194LCG/machine.tm` |
| 194 | `ead029efece4` | [`pa194_loop_return_2026-11-14/machines/PA194LCGS/machine.tm`](pa194_loop_return_2026-11-14/machines/PA194LCGS/machine.tm) | `pa194_loop_return_2026-11-14`: `machines/PA194LCGS/machine.tm` |
| 194 | `0aa2ea7df8ea` | [`pa194_witness_research_2026-11-15/machines/PA194JH5X/machine.tm`](pa194_witness_research_2026-11-15/machines/PA194JH5X/machine.tm) | `pa194_witness_research_2026-11-15`: `machines/PA194JH5X/machine.tm` |
| 194 | `5b92fe556a6c` | [`pa194_witness_research_2026-11-15/machines/PA194H5X/machine.tm`](pa194_witness_research_2026-11-15/machines/PA194H5X/machine.tm) | `pa194_witness_research_2026-11-15`: `machines/PA194H5X/machine.tm` |
| 194 | `57973b64e5e7` | [`pa194_ax11gdh_research_2026-11-15/companions/HS/machine/machine.tm`](pa194_ax11gdh_research_2026-11-15/companions/HS/machine/machine.tm) | `pa194_ax11gdh_research_2026-11-15`: `companions/HS/machine/machine.tm` |
| 194 | `7217a6b22bbc` | [`pa194_ax11gdh_research_2026-11-15/companions/R/PA194AX11GDHR/machine.tm`](pa194_ax11gdh_research_2026-11-15/companions/R/PA194AX11GDHR/machine.tm) | `pa194_ax11gdh_research_2026-11-15`: `companions/R/PA194AX11GDHR/machine.tm` |
| 194 | `b4a5fb0e2f42` | [`pa194_ax11gdh_research_2026-11-15/machine/machine.tm`](pa194_ax11gdh_research_2026-11-15/machine/machine.tm) | `pa194_ax11gdh_research_2026-11-15`: `machine/machine.tm` |
| 194 | `ce07fd5be837` | [`pa194_ax11gdh_research_2026-11-15/companions/F/machine/machine.tm`](pa194_ax11gdh_research_2026-11-15/companions/F/machine/machine.tm) | `pa194_ax11gdh_research_2026-11-15`: `companions/F/machine/machine.tm` |
| 194 | `4e27b5ac80d4` | [`pa194_marker_separation_2026-11-14/machines/PA194LCGSMS/machine.tm`](pa194_marker_separation_2026-11-14/machines/PA194LCGSMS/machine.tm) | `pa194_marker_separation_2026-11-14`: `machines/PA194LCGSMS/machine.tm` |
| 194 | `8fb284c0b562` | [`pa194_marker_separation_2026-11-14/machines/PA194LCGMS/machine.tm`](pa194_marker_separation_2026-11-14/machines/PA194LCGMS/machine.tm) | `pa194_marker_separation_2026-11-14`: `machines/PA194LCGMS/machine.tm` |
| 194 | `0b1a10ae7b95` | [`pa194_new_designs_research_2026-11-15/construction/candidate/machine.tm`](pa194_new_designs_research_2026-11-15/construction/candidate/machine.tm) | `pa194_new_designs_research_2026-11-15`: `construction/candidate/machine.tm` |
| 194 | `0bb3d3bdcb15` | [`pa194_ax11hc4_c32_research_2026-11-15/construction/ax11hc4/machine/pa194_ax11hc4.tm`](pa194_ax11hc4_c32_research_2026-11-15/construction/ax11hc4/machine/pa194_ax11hc4.tm) | `pa194_ax11hc4_c32_research_2026-11-15`: `construction/ax11hc4/machine/pa194_ax11hc4.tm` |
| 194 | `115a93d6692d` | [`pa194_symmetric_witness_research_2026-11-14/machines/PA194H5XS/machine.tm`](pa194_symmetric_witness_research_2026-11-14/machines/PA194H5XS/machine.tm) | `pa194_symmetric_witness_research_2026-11-14`: `machines/PA194H5XS/machine.tm` |
| 194 | `2e1cf5ee2408` | [`pa194_research_2026-11-14_1/machines/PA194GDHS_SF/machine.tm`](pa194_research_2026-11-14_1/machines/PA194GDHS_SF/machine.tm) | `pa194_research_2026-11-14_1`: `machines/PA194GDHS_SF/machine.tm` |
| 194 | `39d0224cab8e` | [`pa194_research_2026-11-15/machines/PA194H5X_MF/machine.tm`](pa194_research_2026-11-15/machines/PA194H5X_MF/machine.tm) | `pa194_research_2026-11-15`: `machines/PA194H5X_MF/machine.tm` |
| 194 | `69c646321e93` | [`pa194_symmetric_witness_research_2026-11-14/machines/PA194JH5XS/machine.tm`](pa194_symmetric_witness_research_2026-11-14/machines/PA194JH5XS/machine.tm) | `pa194_symmetric_witness_research_2026-11-14`: `machines/PA194JH5XS/machine.tm` |
| 194 | `6e58a121fa95` | [`pa194_research_2026-11-14_1/machines/PA194GDH_SF/machine.tm`](pa194_research_2026-11-14_1/machines/PA194GDH_SF/machine.tm) | `pa194_research_2026-11-14_1`: `machines/PA194GDH_SF/machine.tm` |
| 194 | `734451157e01` | [`pa194_research_2026-11-15/machines/PA194JH5X_MF/machine.tm`](pa194_research_2026-11-15/machines/PA194JH5X_MF/machine.tm) | `pa194_research_2026-11-15`: `machines/PA194JH5X_MF/machine.tm` |
| 194 | `80a6ad36220f` | [`pa194_new_designs_research_2026-11-15/mp_construction/candidate/machine.tm`](pa194_new_designs_research_2026-11-15/mp_construction/candidate/machine.tm) | `pa194_new_designs_research_2026-11-15`: `mp_construction/candidate/machine.tm` |
| 194 | `91b032a43f98` | [`pa194_ax11hc4_c32_research_2026-11-15/construction/cycle32/pa194_cycle32.tm`](pa194_ax11hc4_c32_research_2026-11-15/construction/cycle32/pa194_cycle32.tm) | `pa194_ax11hc4_c32_research_2026-11-15`: `construction/cycle32/pa194_cycle32.tm` |
| 194 | `bbd2e4784203` | [`pa194_research_2026-11-14_1/machines/PA194GD_SF/machine.tm`](pa194_research_2026-11-14_1/machines/PA194GD_SF/machine.tm) | `pa194_research_2026-11-14_1`: `machines/PA194GD_SF/machine.tm` |
| 194 | `e333e572ddfd` | [`PA194ORH_research_2026-11-15/machines/PA194ORH/machine.tm`](PA194ORH_research_2026-11-15/machines/PA194ORH/machine.tm) | `PA194ORH_research_2026-11-15`: `machines/PA194ORH/machine.tm` |
| 194 | `1219042e685c` | [`PA194ORMP_ORMPLC3_research_2026-11-14/PA194ORMP.tm`](PA194ORMP_ORMPLC3_research_2026-11-14/PA194ORMP.tm) | `PA194ORMP_ORMPLC3_research_2026-11-14`: `PA194ORMP.tm` |
| 194 | `1cc0b167b1db` | [`pa194_fused_witness_research_2026-11-15/companions/machines/PA194FW_MF/machine.tm`](pa194_fused_witness_research_2026-11-15/companions/machines/PA194FW_MF/machine.tm) | `pa194_fused_witness_research_2026-11-15`: `companions/machines/PA194FW_MF/machine.tm` |
| 194 | `2c169c80ba75` | [`PA194ORMP_ORMPLC3_research_2026-11-14/PA194ORMPLC3.tm`](PA194ORMP_ORMPLC3_research_2026-11-14/PA194ORMPLC3.tm) | `PA194ORMP_ORMPLC3_research_2026-11-14`: `PA194ORMPLC3.tm` |
| 194 | `4c4bec344603` | [`pa194_fused_witness_research_2026-11-15/companions/machines/PA194JH5XS_MF/machine.tm`](pa194_fused_witness_research_2026-11-15/companions/machines/PA194JH5XS_MF/machine.tm) | `pa194_fused_witness_research_2026-11-15`: `companions/machines/PA194JH5XS_MF/machine.tm` |
| 194 | `94f0b2e30a4d` | [`PA194GS_research_2026-11-15/machine/machine.tm`](PA194GS_research_2026-11-15/machine/machine.tm) | `PA194GS_research_2026-11-15`: `machine/machine.tm` |
| 194 | `96e9e6a81ad7` | [`pa194_fused_witness_research_2026-11-15/companions/machines/PA194H5XS_MF/machine.tm`](pa194_fused_witness_research_2026-11-15/companions/machines/PA194H5XS_MF/machine.tm) | `pa194_fused_witness_research_2026-11-15`: `companions/machines/PA194H5XS_MF/machine.tm` |
| 194 | `ac808994cb36` | [`pa194_fused_witness_research_2026-11-15/primary/machines/PA194FW/machine.tm`](pa194_fused_witness_research_2026-11-15/primary/machines/PA194FW/machine.tm) | `pa194_fused_witness_research_2026-11-15`: `primary/machines/PA194FW/machine.tm` |
| 195 | `654ddcd43007` | [`pa_consistency_research/data/rejected195.native.tm`](pa_consistency_research/data/rejected195.native.tm) | `pa_consistency_research`: `data/rejected195.native.tm` |
| 195 | `a76ce33e76ac` | [`pa195_conpa_2026-11-13/pa195/pa195.tm`](pa195_conpa_2026-11-13/pa195/pa195.tm) | `pa195_conpa_2026-11-13`: `pa195/pa195.tm` |
| 195 | `4f5d8b016ec2` | [`PA195_ConPA_research_2026-11-14/machine_195C.tm`](PA195_ConPA_research_2026-11-14/machine_195C.tm) | `PA195_ConPA_research_2026-11-14`: `machine_195C.tm` |
| 195 | `96862fab2a93` | [`PA195_ConPA_research_2026-11-14/machine_195S.tm`](PA195_ConPA_research_2026-11-14/machine_195S.tm) | `PA195_ConPA_research_2026-11-14`: `machine_195S.tm` |
| 195 | `64269e430273` | [`pa195_followup_research/machine_195s8/pa195_scanner8.tm`](pa195_followup_research/machine_195s8/pa195_scanner8.tm) | `pa195_followup_research`: `machine_195s8/pa195_scanner8.tm` |
| 195 | `501c24af5db3` | [`pa195_diagonal_combined_2026-11-13/machine/machine.tm`](pa195_diagonal_combined_2026-11-13/machine/machine.tm) | `pa195_diagonal_combined_2026-11-13`: `machine/machine.native.tm`<br>`pa195_diagonal_combined_2026-11-13`: `machine/machine.tm` |
| 195 | `b335fb9bc010` | [`pa194h5_research_2026-11-14/research/sparse/even195HX/even195HX.tm`](pa194h5_research_2026-11-14/research/sparse/even195HX/even195HX.tm) | `pa194h5_research_2026-11-14`: `research/sparse/even195HX/even195HX.tm` |
| 196 | `3657e60366bf` | [`pa_consistency_research/data/variant196.tm`](pa_consistency_research/data/variant196.tm) | `pa_consistency_research`: `data/variant196.native.tm`<br>`pa_consistency_research`: `data/variant196.tm` |
| 196 | `663dc3688f76` | [`pa_consistency_reduction/comparison/audit/h_catalan_node170_3_133_37.tm`](pa_consistency_reduction/comparison/audit/h_catalan_node170_3_133_37.tm) | `pa_consistency_reduction`: `comparison/audit/h_catalan_node170_3_133_37.tm` |
| 196 | `8b0e28045992` | [`pa_consistency_reduction/comparison/audit/rebracketed196_dense.tm`](pa_consistency_reduction/comparison/audit/rebracketed196_dense.tm) | `pa_consistency_reduction`: `comparison/audit/rebracketed196_dense.tm` |
| 196 | `37aa79c9c241` | [`pa_consistency_research_2026-11-13_2/rotated196/machine.tm`](pa_consistency_research_2026-11-13_2/rotated196/machine.tm) | `pa_consistency_research_2026-11-13_2`: `rotated196/machine.tm` |
| 196 | `6a6c70099fd3` | [`conpa_tm_study_2026-11-13/machines/h_only_mp_h.tm`](conpa_tm_study_2026-11-13/machines/h_only_mp_h.tm) | `conpa_tm_study_2026-11-13`: `machines/h_only_mp_h.tm` |
| 196 | `43115a87740f` | [`jamesyc-upstream/pa196/data/pa196.tm`](../verification/other-machines/jamesyc-upstream/pa196/data/pa196.tm) | `pa_below196_research`: `physical_search/pa196.tm` |
| 196 | `478a44709797` | [`pa_tm_research_2026-11-13_2/verification/zero_jump_machine/machines/zerojump196.tm`](pa_tm_research_2026-11-13_2/verification/zero_jump_machine/machines/zerojump196.tm) | `pa_tm_research_2026-11-13_2`: `verification/zero_jump_machine/machines/zerojump196.tm` |
| 196 | `9570bee91984` | [`pa_consistency_comparison_and_new196_2026-11-13/axioms/separate196/machine.tm`](pa_consistency_comparison_and_new196_2026-11-13/axioms/separate196/machine.tm) | `pa_consistency_comparison_and_new196_2026-11-13`: `axioms/separate196/machine.tm` |
| 196 | `a5a7506acbd5` | [`pa_consistency_comparison_and_new196_2026-11-13/axioms/search/scanner_best196.tm`](pa_consistency_comparison_and_new196_2026-11-13/axioms/search/scanner_best196.tm) | `pa_consistency_comparison_and_new196_2026-11-13`: `axioms/search/scanner_best196.tm` |
| 196 | `eefe38c5c291` | [`pa_consistency_comparison_and_new196_2026-11-13/axioms/diagonal196/machine.tm`](pa_consistency_comparison_and_new196_2026-11-13/axioms/diagonal196/machine.tm) | `pa_consistency_comparison_and_new196_2026-11-13`: `axioms/diagonal196/machine.tm` |
| 196 | `319fb9fd819a` | [`pa_consistency_cross_archive/machines/separate_combined/machine.tm`](pa_consistency_cross_archive/machines/separate_combined/machine.tm) | `pa_consistency_cross_archive`: `machines/separate_combined/machine.tm` |
| 196 | `350d3177d017` | [`pa_consistency_cross_archive/machines/diagonal_combined_zerojump/machine.tm`](pa_consistency_cross_archive/machines/diagonal_combined_zerojump/machine.tm) | `pa_consistency_cross_archive`: `machines/diagonal_combined_zerojump/machine.tm` |
| 196 | `b9ac9f989be1` | [`pa_consistency_cross_archive/machines/separate_combined_zerojump/machine.tm`](pa_consistency_cross_archive/machines/separate_combined_zerojump/machine.tm) | `pa_consistency_cross_archive`: `machines/separate_combined_zerojump/machine.tm` |
| 196 | `c3af3a720f99` | [`pa_consistency_cross_archive/machines/diagonal_combined/machine.tm`](pa_consistency_cross_archive/machines/diagonal_combined/machine.tm) | `pa_consistency_cross_archive`: `machines/diagonal_combined/machine.tm` |
| 196 | `463c4697136e` | [`pa_sub194_research/machine/machine/machine.tm`](pa_sub194_research/machine/machine/machine.tm) | `pa_sub194_research`: `machine/machine/machine.tm` |
| 197 | `table:035009006dfb` | [`conpa_tm_study_2026-11-13/machines/direct_negation197.tm`](conpa_tm_study_2026-11-13/machines/direct_negation197.tm) | `conpa_tm_study_2026-11-13`: `machines/direct_negation197.tm` |
| 198 | `0d1437ef851a` | [`pa_consistency_research_2026-11-13_2/diagonal198/machine.tm`](pa_consistency_research_2026-11-13_2/diagonal198/machine.tm) | `pa_consistency_research_2026-11-13_2`: `diagonal198/machine.tm` |
| 199 | `0a91cd1636eb` | [`pa_consistency_research_2026-11-13/diagonal199/machine.tm`](pa_consistency_research_2026-11-13/diagonal199/machine.tm) | `pa_consistency_research_2026-11-13`: `diagonal199/machine.native.tm`<br>`pa_consistency_research_2026-11-13`: `diagonal199/machine.tm` |
| 201 | `table:006328832b94` | [`pa194c_conpa_2026-11-13/tables/pa194C_raw201.native.tm`](pa194c_conpa_2026-11-13/tables/pa194C_raw201.native.tm) | `pa194c_conpa_2026-11-13`: `tables/pa194C_raw201.native.tm` |
| 201 | `table:0057384d4e2e` | [`pa194gh_research_2026-11-14/machines/PA194GH/raw.native.tm`](pa194gh_research_2026-11-14/machines/PA194GH/raw.native.tm) | `pa194_witness_research_2026-11-15`: `construction/inputs/raw.native.tm` |
| 202 | `table:038fe506de9f` | [`pa194h5_research_2026-11-14/machine/raw.native.tm`](pa194h5_research_2026-11-14/machine/raw.native.tm) | `pa194h5_research_2026-11-14`: `machine/raw.native.tm` |
| 203 | `511853be829e` | [`pa_consistency_reduction/comparison/audit/integrated_gate203_dense.tm`](pa_consistency_reduction/comparison/audit/integrated_gate203_dense.tm) | `pa_consistency_reduction`: `comparison/audit/integrated_gate203_dense.tm` |
| 206 | `ad1d34d387ad` | [`pa_consistency_reduction/comparison/audit/integrated_gate206_dense.tm`](pa_consistency_reduction/comparison/audit/integrated_gate206_dense.tm) | `pa_consistency_reduction`: `comparison/audit/integrated_gate206_dense.tm` |
| 208 | `735b413e0795` | [`U208_ConPA_Conditional_Context_2026-10-29/machine/u208.tm`](U208_ConPA_Conditional_Context_2026-10-29/machine/u208.tm) | `U208_ConPA_Conditional_Context_2026-10-29`: `machine/u208.native.tm`<br>`U208_ConPA_Conditional_Context_2026-10-29`: `machine/u208.tm`<br>`U208_ConPA_Entry_Context_2026-10-29`: `machine/u208.tm`<br>`U208_ConPA_History_2026-10-29`: `machine/u208.native.tm`<br>`U208_ConPA_History_2026-10-29`: `machine/u208.tm`<br>`U208_ConPA_2026-10-29`: `machine/u208.tm`<br>`u208_research_2026-10-29`: `machine/variant_plain/u208.tm`<br>`pa_consistency_research`: `data/u208_01.native.tm` |
| 208 | `b6396833ab64` | [`U208_ConPA_Conditional_Context_2026-10-29/alternative/u208.tm`](U208_ConPA_Conditional_Context_2026-10-29/alternative/u208.tm) | `U208_ConPA_Entry_Context_2026-10-29`: `machine/u208_compatibility.tm`<br>`u208_research_2026-10-29`: `machine/u208.tm` |
| 209 | `b5fb01b40020` | [`U208_ConPA_Conditional_Context_2026-10-29/machine_parent/u209.tm`](U208_ConPA_Conditional_Context_2026-10-29/machine_parent/u209.tm) | `U208_ConPA_Entry_Context_2026-10-29`: `baseline/u209.native.tm` |

12 of these classes are named by more than one packet:

- `11c65a856352`, 194 states: 2 packets (`pa194qn_research_2026-11-13`, `pa194nq_research_2026-11-13`).
- `4970232fdb7d`, 194 states: 2 packets (`pa194hs_conpa_2026-11-13`, `pa194ns_conpa_2026-11-13`).
- `52f94a71722b`, 194 states: 4 packets (`pa194_ax11gh_research_2026-11-14_1`, `pa194_research_2026-11-14_2`, `pa194_sel_ax11gh_research_2026-11-14`, `pa_conpa_research_2026-11-14`).
- `65f6eb4aaf7b`, 194 states: 2 packets (`pa194_ax11gh_research_2026-11-14_1`, `pa_conpa_research_2026-11-14`).
- `6881f3df3909`, 194 states: 2 packets (`pa194qn6_conpa_2026-11-14`, `pa194qn_2026-11-14`).
- `9a39109ff1e3`, 194 states: 2 packets (`pa194_ax11qh5_2026-11-14`, `pa194_research_2026-11-14`).
- `c4ecc511bd51`, 194 states: 5 packets (`pa194C_conpa_2026-11-13_2`, `pa194_new_designs_2026-11-13`, `pa194c_conpa`, `pa194c_conpa_2026-11-13`, `pa194c_conpa_2026-11-13_1`).
- `da81e6f6524c`, 194 states: 2 packets (`pa194_qns_research_2026-11-13`, `pa194qns_research_2026-11-13`).
- `dd2d4a04364c`, 194 states: 2 packets (`pa194_conpa_2026-11-13`, `pa194n5_n6_conpa_2026-11-13`).
- `de3420f4caa1`, 194 states: 2 packets (`pa194_ax11_research_2026-11-14`, `pa194_qh5_research_2026-11-14`).
- `735b413e0795`, 208 states: 6 packets (`U208_ConPA_Conditional_Context_2026-10-29`, `U208_ConPA_Entry_Context_2026-10-29`, `U208_ConPA_History_2026-10-29`, `U208_ConPA_2026-10-29`, `u208_research_2026-10-29`, `pa_consistency_research`).
- `b6396833ab64`, 208 states: 2 packets (`U208_ConPA_Entry_Context_2026-10-29`, `u208_research_2026-10-29`).

## Files

- [`MACHINES.tsv`](MACHINES.tsv): one row for each of the 1295 classes, with the number of states, the
  packet that delivered it first, the kept file, in how many packets and files it occurred,
  the file names it had, files of the research tree with the same table, and the hash
  that does not depend on the start (`table_class`).
- [`MACHINE_FILES.tsv`](MACHINE_FILES.tsv): one row for each of the 26,242 table files as delivered, with its
  SHA-256, its class, its start and whether it is kept.
- [`machine_classes.py`](machine_classes.py): prints the hashes of a table.

To see whether a new table is already here, compute its hashes and look the table up:

```bash
py machine_classes.py new_table.tm
```

and search the column `table_class` of `MACHINES.tsv` for the value after `table=`.
