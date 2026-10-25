# Held indexed P66 source and actual-page toolchain

No new application or TeX/PDF utility has run. Require two full static
reviews and a separate root release before the following ten commands.
Run from the repository root, strictly sequentially, with every complete
stdout retained externally next to its JSON receipt. Stop on first failure.

```sh
python -B Computability/DiophantineConsistency/candidates/one-page-fifteen66/build.py --output /tmp/fifteen66-build.json
python -B Computability/DiophantineConsistency/candidates/one-page-fifteen66/FRONT_AUDIT.py --source-only --output /tmp/fifteen66-source-audit.json
python -B -O Computability/DiophantineConsistency/candidates/one-page-fifteen66/FRONT_AUDIT.py --source-only --output /tmp/fifteen66-source-audit-optimized.json
python -B Computability/DiophantineConsistency/candidates/one-page-fifteen66/build.py --check --output /tmp/fifteen66-build-check.json
python -B -O Computability/DiophantineConsistency/candidates/one-page-fifteen66/build.py --check --output /tmp/fifteen66-build-check-optimized.json
python -B Computability/DiophantineConsistency/tools/render_fifteen66_page.py --render --output /tmp/fifteen66-render.json
python -B Computability/DiophantineConsistency/candidates/one-page-fifteen66/FRONT_AUDIT.py --output /tmp/fifteen66-audit.json
python -B -O Computability/DiophantineConsistency/candidates/one-page-fifteen66/FRONT_AUDIT.py --output /tmp/fifteen66-audit-optimized.json
python -B Computability/DiophantineConsistency/tools/render_fifteen66_page.py --check --output /tmp/fifteen66-rerender.json
python -B -O Computability/DiophantineConsistency/tools/render_fifteen66_page.py --check --output /tmp/fifteen66-rerender-optimized.json
```

The source producer's first invocation may emit exactly polynomial.json,
COEFFICIENT_BINDING.json,CALIBRATION_BINDING.json,SOURCE_INDEX.json.
Both check invocations regenerate all four complete byte strings in memory
and require identical existing files, writing only separate receipts.
The producer imports no auditor/project module and executes no arithmetic
compiler. The independent auditor never imports the producer.

Source-only audits authenticate all own/direct pins and three full parent
inventories; compare every historical66 arithmetic row and signature;
read the ACTUAL TeX; prove all23 local polynomial cuts over four free
ports; check complete liveness, full leading homogeneous polynomials and
the actual nonzero8*beta^92 coefficient; verify all four compressed/raw
integers, masks, canonical shift and both-map records; and exercise24
negative plus4 positive controls. No PDF process is launched in that mode.

The first render uses only the immutable reviewed TeX in a private scratch
directory, fixed time/environment settings, no shell escape and explicit
timeouts. It must produce one612x792 Letter page with zero overfull
diagnostics and all seed/alphabet characters. It may materialize exactly
equation.pdf,equation.txt,RENDER.txt,TEX_DIAGNOSTICS.txt,RENDER_DATA.json.
Every already present artifact must match before any artifact is written.

Full audits repeat every source/TeX check and compare every displayed PDF
front glyph and the ENTIRE constant/table/decoder/seed/footer suffix with
the preserved85 PDF. They check all fifteen domain glyphs, printed
metrics, fonts by the fixed TeX, retained diagnostics and page count.
Independent visual review remains mandatory after all ten commands pass.
No byte comparison uses mutable root equation.tex/PDF or CURRENT_EQUATION.

Pure rerenders invoke the same scratch pipeline, compare all five complete
render files and write only separate receipts. The maintained page,
coefficient parents, programs, source inputs, TeX and Lean are not outputs.
All successful metadata/stdout/replay/visual evidence and a final exact
closed inventory must be added separately after release; held core stays
unchanged. No first-run evidence or accepted numerical endpoint exists yet.
