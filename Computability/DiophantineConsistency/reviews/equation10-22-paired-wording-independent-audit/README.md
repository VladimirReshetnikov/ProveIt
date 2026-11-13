# Independent AQ22 paired-result wording review

This finite review passed with the actual process exit recorded in
[terminal-observation.json](terminal-observation.json). It compares the
[revised PDF](../../research/adaptive-square-sums22-degree10/equation10-22.pdf)
at commit `4202c66a54` to the previously independently audited generator and
TeX at `fc8c78438c`: both differ only by the same status paragraph. The 22
input aliases, four fixed ports, 114 circuit operations, thirteen-square output
and base-10 block retain the scope of the
[earlier presentation audit](../equation10-22-independent-audit/README.md).
The candidate graph is unchanged.

The qualified historical paired-run wording is supported by the separately
[independently audited AQ22 pair](../ipra-aq22-historical-pair-independent-audit/README.md),
including actual coordinator and auditor exits. Two temporary generator runs,
each compiling twice without warnings, produced PDF SHA-256
`310f638eff89ab3b9776756fac3a8b4984e2feb94c838eeb6508444e8c177363`.
At 120 dpi, the updated [first page](page-1.png) has no apparent clipping or
overlap; the table is tightly spaced. The second-page render is byte-identical
to the previously reviewed [second page](../equation10-22-independent-audit/page-2.png).
This is visual inspection, not an automated layout proof.

The paired artifacts concern the selected embedded Gödel–Gentzen-translated
Foundation consistency sentence. Neither this presentation review nor the
paired audit is a formal Lean interpretation of the PDF; the decoder, table,
rank and port recipe remain manually transcribed in finite checks. Historical
parent, package-transitive, dynamic-load, transient-mutation and missing outer
Foundation-wrapper-exit limitations remain. No global minimality is claimed.

Run with ordinary Python and TeX installed after preserving and moving aside
only this packet's receipt:

```sh
python3 Computability/DiophantineConsistency/reviews/equation10-22-paired-wording-independent-audit/audit.py
```

The script checks prior input hashes and the exact paragraph replacement,
recreates the PDF, refuses to overwrite its receipt and rejects optimized
Python. The [receipt](receipt.json) records the compared hashes.
