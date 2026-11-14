PA194P5 — comparison and same-size consistency-machine construction
Research date: 14 November 2026
Repository snapshot: 4be5c6e3a10292a7466f5d3687e3b39615ff049b

RESULT
------
This package defines a binary, one-tape, blank-start deterministic machine
with 194 working states, start 0, and halt label 194. It changes the physical
locations of five logical registers and seven router targets of primary PA194.
The logical source program and numerical calculus are unchanged.

No machine with fewer than 194 states was obtained. The positive contribution
is a distinct physical implementation at 194 states. The report proves
PA |- Halt(PA194P5) <-> Halt(primary PA194), and inherits the primary packet's
ordinary written calibration to Con(PA). This is not a new proof-assistant
calibration. The exact scope of the inherited logical argument and the
symbolic arithmetic-box lemmas is explicit in the report.

The machine has 388 rows, 3,673 unchanged source instruction sites and 4,780
passing arbitrary-register symbolic contracts. From blank it reaches the
parent's identical complete clean frame in 56,158 steps (parent: 58,154).

READ FIRST
----------
report/report.pdf       Main article: construction, proof, comparison,
                        search results, full table and packet ledger.
report/report.tex       Editable LaTeX source with three local input files.
machine/pa194p5.tm       Final dense table (the definitive delivered machine).
machine/pa194p5.native.tm
                        Equivalent native-label table, start 74, halt 254.
comparison/README.txt   Exact corpus scope, categories and exclusions.
research/architecture/README.txt
research/local_reductions/README.txt
                        Reproducible bounded searches and their limitations.

VERIFY
------
Python 3.10+ and its standard library are sufficient for:

    python3 verify.py
    python3 comparison/verify_novelty.py
    python3 comparison/verify_census.py

Do not run Python with -O: assertions are certificate checks.
No network is required. The first command reconstructs the seven edits,
checks every table row and native/dense correspondence, replays both exact
blank starts, and checks all source contracts. The second compares the
candidate exactly with the retained 194-control frontier (including global
symmetries and the nonspanning diagnostics). The third reconstructs the
retained table census and checks pinned source identities.

Optional research replays use Node.js and/or Python, as documented in each
research directory. Their negative results are bounded search results, not
a lower bound on PA consistency machine size.

BUILD THE ARTICLE
-----------------
With a normal TeX Live installation:

    cd report
    pdflatex -interaction=nonstopmode -halt-on-error report.tex
    pdflatex -interaction=nonstopmode -halt-on-error report.tex

Required packages are listed in report.tex; all text, tables and mathematical
content are local. The supplied PDF is the rendered article. A Makefile also
provides "make verify" and "make report".

TABLE FORMAT
------------
Each line is:
    state read_bit write_bit direction next_state

There are two rows per working state. Directions are L or R. The head starts
at cell zero on the all-zero tape. Entering label 194 terminates the dense
machine. The halt label is not counted as a working state. All 194 controls
are graph-reachable from start 0; this does not claim that every control is
visited on the actual blank run.

Dense-table SHA-256:
cf3a2c2d3ba8e95d5c0ea825c3f279ae529b6591cc1280264b0ba3793e77d026

Native-table SHA-256:
a9d3a13786b6a0018713d8803865860b5e9e26692fde34975545c3bb0f09501c

REFERENCE MATERIAL AND PROVENANCE
---------------------------------
reference/ contains the primary table, label map, source program, grammar,
fold list and retained symbolic runtime. The sites JSON uses compact path
strings; JSON serialization can differ from the upstream file.

reference/parent_report/ contains the original main LaTeX report, all its
local inputs and its published PDF. reference/primary_calibration.tex is
also retained separately because it is the inherited logical dependency.
These are historical sources, not claims that every accompanying upstream
computation has been freshly re-executed here.

reference/lean/ preserves the actual generic arithmetic-box proof provider
(M6.Native.boxLemmas), its Runtime/Zip definitions and the frozen reference
table. These source dependencies are supplied for inspection; no new
end-to-end PA194P5 Lean build is claimed.

reference/ZFC_README.md and reference/ConciseIPRA_README.md preserve the
pinned contextual sources discussed in the main report.
PROVENANCE.json and the comparison manifests identify all inputs.
SHA256SUMS covers the files delivered in this package.

LICENSES AND ATTRIBUTION
------------------------
The retained ProveIt material is under its MIT-0 license; the original
James Chang runtime source has its separate MIT notice. Both notices are
in reference/. New report text and newly written verification/search glue follow the same
MIT-0 terms as ProveIt. Existing source notices and inherited licenses remain
applicable.

