# Independent AQ17 wording-refresh review

This review covers the author-run disclosure at the cited revision. The current
PDF has a later paired-run wording refresh; its equation and circuit are
unchanged, and a [separate review](../equation32-17-paired-wording-independent-audit/README.md)
of that refresh has passed.

This review passed with the actual process exit recorded in
[terminal-observation.json](terminal-observation.json). It compares the final
[revision](../../research/aq22-positive-binding-survey/equation32-17.pdf)
at commit `702a31c646` to the exact earlier independently audited generator
and TeX at `39f2c60c9d`: both differ only by the same status paragraph. The
17 input aliases, four fixed ports, all 99 circuit operations, the
eight-square output and the
base-10 fixed block therefore retain the scope of the
[earlier presentation audit](../equation32-17-independent-audit/README.md).
The candidate graph is unchanged.

Two independent temporary generator runs each performed two warning-free
TeX compilations; all four builds reproduced PDF SHA-256
`9e11ae20b1b59f6480e52dc1c7055493ba8990776ecc22f84ed0adcc59828e54`.
At 120 dpi, the updated [first page](page-1.png) has no apparent clipping or
overlap; the tile table is tightly spaced. The second-page render is
byte-identical to the previously reviewed
[second page](../equation32-17-independent-audit/page-2.png). This is visual
inspection, not an automated layout proof.

The qualified wording is supported by the separate
[guarded-author artifact audit](../ipra-aq17-guarded-author-independent-audit/README.md):
one historical author build and an actual successful independent audit, with
no paired AQ17 replay yet. The translated consistency side is the selected
Foundation sentence under the recorded embedding and Gödel–Gentzen
translation. Neither this presentation check nor that artifact audit proves a
formal interpretation of the PDF in Lean. The fixed decoder, table, rank and
port recipe remain manually transcribed in finite checks; package-transitive,
dynamic-load, transient-mutation and missing outer Foundation-wrapper-exit
limitations remain.

Run with ordinary Python and the existing TeX installation, after preserving
and moving aside only this packet's receipt:

```sh
python3 Computability/DiophantineConsistency/reviews/equation32-17-wording-independent-audit/audit.py
```

The script checks the earlier input hashes and exact paragraph replacement,
recreates the final PDF, refuses to overwrite its receipt, and rejects
optimized Python. The [receipt](receipt.json) records the compared input hashes.
