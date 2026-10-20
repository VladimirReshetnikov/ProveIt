# Alternative 219 state consistency machines

`report.pdf` is the 12-page technical report. `report.tex` is its editable source;
keep the four accompanying `.tex` data sections beside it. `build.sh` runs two
pdfLaTeX passes with standard TeX Live packages. From the packet root:

    sh report/build.sh

A normal TeX Live installation needs no overrides. An installation that stores
its prebuilt format separately can set `K219_ALT_TEXFORMATS` to that directory.
The build script includes a narrowly scoped font-map fallback for minimal Debian
TeX installations. It does not install software or change system files.

`validation.json` records the final PDF identity, compilation checks, exact
machine/source hash checks, copyable command checks, and visual review of all
12 rendered pages. It is presentation and artifact-binding QA, not a separate
mathematical proof or a proof-assistant certificate.

The full machine and proof artifacts are elsewhere in this packet. Run
`portable/reproduce.py` from the packet root for the mathematical replay.
Machine hashes are independent of PDF metadata and TeX-version differences.
