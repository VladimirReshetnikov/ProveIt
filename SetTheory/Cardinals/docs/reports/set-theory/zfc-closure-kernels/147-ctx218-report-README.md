# A 218 state consistency machine

`report.pdf` is the 12-page technical report. `report.tex` is its editable
source. Keep the six accompanying `.tex` sections beside it.

From the extracted packet root, rebuild with:

    sh report/build.sh

A conventional TeX Live installation needs no overrides. An installation
that stores its prebuilt formats separately can set `K218_TEXFORMATS` to
that directory. The build script includes a narrowly scoped font-map
fallback for minimal Debian installations. It installs no software and
changes no system files.

The report distinguishes the all-natural source bisimulation, exact finite
lineage, complete blank initialization, fresh generic unbounded runtime
proof, and inherited ZFC calibration. It does not claim an exact-byte
Rocq/Lean endpoint, unconditional nonhalting, consistency, or minimality.

`validation.json` records artifact identities, two-pass compilation, text
checks, and visual inspection of all 12 final pages. This is presentation
and artifact-binding QA, not an independent mathematical proof.

For the complete mathematical replay, use the packet-root command:

    python3 -B portable/reproduce.py --output-dir /tmp/k218-replay

Use a new empty output directory. Quick audit and optional fresh ancestor
runtime modes are explained in the report and the packet's top-level README.
Machine and source hashes are independent of TeX-version differences in PDF
metadata or rendering.
