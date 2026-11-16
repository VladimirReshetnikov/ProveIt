# Validation record

- `bash build.sh` passed: all eight exact Python regression tests succeeded and
  the LaTeX report rebuilt.
- The final PDF has 48 letter-size pages. Its LaTeX log has zero overfull boxes,
  zero duplicate page anchors, and no undefined references or citations.
- All 48 pages were rendered at 120 DPI and visually inspected through the four
  retained contact sheets `contact-01-12.png` through `contact-37-48.png`.
- JSON files parse successfully; `examples/cubic_bisection_program.json`
  validates against `schema/scr_program.schema.json` under JSON Schema draft
  2020-12.
- The Lean sources contain no declaration-like `sorry`, `admit`, `axiom`,
  `opaque`, `unsafe`, or `sorryAx` placeholders. Lean and Lake were unavailable,
  so the Lean files were not elaborated and are not claimed kernel-checked.
