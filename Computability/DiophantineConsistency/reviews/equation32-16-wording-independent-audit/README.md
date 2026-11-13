# Independent AQ16 wording-refresh review

This review covers the exploratory-run disclosure at the cited revision. The
current PDF has a later paired-run wording refresh; its equation and circuit
are unchanged, and a [separate review](../equation32-16-paired-wording-independent-audit/README.md)
of that refresh passed.

This finite review passed with the actual process exit recorded in
[terminal-observation.json](terminal-observation.json). It compares the
[revised PDF](../../research/aq17-positive-signed-binding/equation32-16.pdf)
at commit `7d72057118` to the exact earlier independently audited generator
and TeX at `007aeb301b`: both differ only by the same status paragraph. The
16 input aliases, four fixed ports, all 96 circuit operations, seven-square
output and base-10 fixed block therefore retain the scope of the
[earlier presentation audit](../equation32-16-independent-audit/README.md).
The candidate graph is unchanged.

Two independent temporary generator runs each performed two warning-free
TeX compilations; all four builds reproduced PDF SHA-256
`73a337169a75eb647a7e7f4a3f8ae9d159732df420c82a4b5ce81fca6a16f376`.
At 120 dpi, the updated [first page](page-1.png) has no apparent clipping or
overlap; the tile table is tightly spaced. The second-page render is
byte-identical to the previously reviewed
[second page](../equation32-16-independent-audit/page-2.png). This is visual
inspection, not an automated layout proof.

The qualified wording refers to recorded successful exploratory overlay exits
for witness transport and native/standard endpoints, not a guarded AQ16
replay or an independently matched peer. The consistency side is the
selected embedded and Gödel–Gentzen-translated Foundation sentence. The
signed binding's positivity proof requires beta at least two, which holds for
the recorded fixed port; integer subtraction and natural truncated
subtraction remain distinct. The fixed decoder, table, rank and port recipe
remain manually transcribed in finite checks. No formal PDF-to-Lean theorem,
current-source replay, or global minimality is claimed.

Run with ordinary Python and TeX installed after preserving and moving aside
only this packet's receipt:

```sh
python3 Computability/DiophantineConsistency/reviews/equation32-16-wording-independent-audit/audit.py
```

The script verifies the earlier input hashes and exact paragraph replacement,
recreates the final PDF, refuses to overwrite its receipt, and rejects
optimized Python. The [receipt](receipt.json) records the compared hashes.
