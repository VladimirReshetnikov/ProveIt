# Independent AQ17 paired-result wording review

This finite review passed with the actual process exit recorded in
[terminal-observation.json](terminal-observation.json). It compares the
[revised PDF](../../research/aq22-positive-binding-survey/equation32-17.pdf)
at commit `c995343c1c` to the previously independently audited generator and
TeX at `702a31c646`: both differ only by the same status paragraph. The 17
input aliases, four fixed ports, 99 circuit operations, eight-square output
and base-10 block retain the scope of the
[earlier presentation audit](../equation32-17-independent-audit/README.md).
The candidate graph is unchanged.

The revised historical paired-run wording is supported by the separately
[independently audited AQ17 pair](../ipra-aq17-historical-pair-independent-audit/README.md),
including actual coordinator and auditor exits. Two temporary generator runs,
each compiling twice without warnings, produced the same PDF SHA-256
`33482f0aca32f0ad8a8356bcfae91b06a2bebf981a2c2139c017afcabfb0d1d9`.
At 120 dpi, the updated [first page](page-1.png) has no apparent clipping or
overlap; the table is tightly spaced. The second-page render is byte-identical
to the previously reviewed [second page](../equation32-17-independent-audit/page-2.png).
This is visual inspection, not a layout proof.

The paired artifacts concern the selected embedded Gödel–Gentzen-translated
Foundation consistency sentence. Neither this presentation review nor the
paired audit is a formal Lean interpretation of the PDF; the decoder, table,
rank and port recipe remain manually transcribed in finite checks. Historical
parent, package-transitive, dynamic-load, transient-mutation and missing outer
Foundation-wrapper-exit limitations remain. No global minimality is claimed.

Run with ordinary Python and TeX installed after preserving and moving aside
only this packet's receipt:

```sh
python3 Computability/DiophantineConsistency/reviews/equation32-17-paired-wording-independent-audit/audit.py
```

The script checks prior input hashes and the exact paragraph replacement,
recreates the PDF, refuses to overwrite its receipt and rejects optimized
Python. The [receipt](receipt.json) records the compared hashes.
