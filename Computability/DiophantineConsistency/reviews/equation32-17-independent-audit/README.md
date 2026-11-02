# Independent audit of the AQ17 circuit display

This audit records the earlier PDF with the exploratory-run disclosure. The
current display has a later status-wording refresh; its formula, input list,
fixed constants and circuit are unchanged, and a [separate refresh review](../equation32-17-wording-independent-audit/README.md)
has passed.

The independent checker exited zero. It compared the pinned AQ17 graph with
all 17 displayed input aliases, the four port aliases, all 99 live numbered
gates and the final eight-square output. It checked the fixed base-10 block
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
optimized Python. It checks the exploratory Lean observation's recorded
successful transport and native/standard endpoint exit codes against the
qualified wording, but does not rerun or authenticate that overlay. It also
uses the previously independently audited finite degree and reconstruction
certificate.

This is a finite graph-to-display and reproducibility audit. It does not
interpret TeX's decoder, table, rank and port recipe in Lean; that recipe
retains the manual-transcription boundary. It does not establish a
PDF-to-Lean theorem or a guarded AQ17 replay, and it makes no global minimality
claim. The displayed consistency side refers to the selected embedded and
Gödel–Gentzen-translated Foundation sentence.

Run in ordinary Python from the repository root after moving only this packet's
receipt aside:

```sh
python3 Computability/DiophantineConsistency/reviews/equation32-17-independent-audit/audit.py
```

The script requires `pdflatex`, `pdfinfo` and `pdftotext`, refuses to overwrite
its receipt, and intentionally rejects optimized Python.
