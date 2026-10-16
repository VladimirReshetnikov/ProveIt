# Finite-sort countermodel regression: attribution and reproduction

`equality_free_countermodel.py` is reproduced unchanged from the incoming
report **zfc_consistency_machine_research.zip**, committed to ProveIt at
`47f3a3602946dfe48803a91a910c646e74637ac8`.

- [Pinned source archive](https://github.com/VladimirReshetnikov/ProveIt/blob/47f3a3602946dfe48803a91a910c646e74637ac8/docs/incoming/zfc_consistency_machine_research.zip)
- Exact archive member: `zfc_machine_report/code/equality_free_countermodel.py`
- Source analysis: `zfc_machine_report/sections/countermodel.tex`
- Original attribution notice: `zfc_machine_report/NOTICE.txt`
- SHA-256: `cc6812d56a3f3c60f40c8eed5a263b6f30aa9e8c77d828f136fad889d47be75e`

The finite-sort argument and this regression script belong to that prior
research submission. The present report independently reviews the argument
and strengthens its internalization from ZFC to PA. It does not claim
authorship of the inherited script or finite-sort construction, and makes
no blanket relicensing claim for separately authored sources.

The 254-state machine and original container/collection program are due
to Mira-Cult; Jeff supplied the published Coq verification. The 253-state
reduction is attributed to mira-emmy. The copied regression script does
not contain their compiler or Coq development and does not certify a
literal machine table.

## Reproduction

Use Python 3.10 or newer with its standard library. From the package root:

```sh
python code/equality_free_countermodel.py
```

Run with ordinary assertion-enabled Python, without `-O` or `-OO`.
The script prints its result and writes
`code/equality_free_countermodel_results.json`.
The independent rerun supplied with this report is
`data/countermodel_rerun.json`.

Expected finite case counts are:

| Test family | Cases |
|---|---:|
| Full container formula | 312 |
| Collection with arbitrary binary matrices | 32,768 |
| Collection with higher labels or lower output sort | 440 |
| Colliding input/output labels | 392 |
| Total decoder support | 10,000 |

These finite checks instantiate labels 0, 1, and 2. The ordinary
mathematical proof covers every label by recursion. The checks supply
neither a kernel-checked proof nor a simulation theorem for the literal
248-, 250-, or 252-state experiments. The script has no optional network
or compiler dependency.

