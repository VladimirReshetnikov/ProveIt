# Independent audit of the AQ16 circuit display

This audit records the earlier PDF with the transport-open disclosure. The
current display has a later status-wording refresh; its formula, input list,
fixed constants and circuit are unchanged, and a [separate refresh review](../equation32-16-wording-independent-audit/README.md)
has passed.

The independent checker exited zero. It compared the pinned AQ16 graph with
all 16 displayed input aliases, the four port aliases, all 96 live numbered
gates and the final seven-square output. It checked the fixed base-10 block
byte-for-byte against the maintained original `equation.tex` and the pinned
block digest, including its decimal lines. The [receipt](receipt.json) pins
the checked inputs and PDF; the [terminal observation](terminal-observation.json)
records actual checker and rendering exits.

The generator ran in an isolated tree and recreated both maintained TeX and
PDF byte-for-byte. It compiled twice without warnings, and two further clean
independent TeX compilations produced the same PDF digest. `pdfinfo` reports
two pages and text extraction confirmed content on both. At 120 dpi, the
[page 1](page-1.png) and [page 2](page-2.png) renders show no apparent
clipping or overlap; the tile table is tightly spaced. This is visual review,
not an automated layout proof.

The checker independently rejected changed gate operation, operand and
target, a decimal digit, and a duplicate input name. It deliberately rejects
optimized Python. The page correctly states that AQ16 Lean witness transport
and the internal iPRA equivalence remain open. The degree and substitution
claims refer to the independently audited finite candidate and actual beta
under the explicit beta-at-least-two hypothesis of that candidate.

This is a finite graph-to-display and reproducibility audit. It does not
interpret TeX's decoder, table, rank and port recipe in Lean; that recipe
retains the manual-transcription boundary. It does not establish a
PDF-to-Lean theorem or AQ16 Lean transport, and it makes no global minimality
claim.

Run in ordinary Python from the repository root after moving only this packet's
receipt aside:

```sh
python3 Computability/DiophantineConsistency/reviews/equation32-16-independent-audit/audit.py
```

The script requires `pdflatex`, `pdfinfo` and `pdftotext`, refuses to overwrite
its receipt, and intentionally rejects optimized Python.
