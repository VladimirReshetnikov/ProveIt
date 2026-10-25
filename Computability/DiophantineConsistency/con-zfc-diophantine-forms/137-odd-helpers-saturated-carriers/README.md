# Odd Pell helpers and saturated carriers

Round 17 research packet for ProveIt, 25 October 2026.

Read `report/report.pdf`. The modular editable source is `report/report.tex`,
and `report/report_self_contained.tex` is a single-file editable version.

## Main results

| Construction | Domain | Variables | Exact degree | Live binary gates |
|---|---|---:|---:|---:|
| Odd helper minimum | unrestricted integers | 307 | 4 | not the compared metric |
| Odd helper balanced | unrestricted integers | 308 | 4 | not the compared metric |
| Odd helper low height | unrestricted integers | 310 | 4 | not the compared metric |
| Two-root carrier | unrestricted integers | 14 | 88 | 119 |
| Parity-separated roots | unrestricted integers | 13 | 156 | 127 |
| Amplified product carrier | unrestricted integers | 11 | 648 | 115 |
| Doubled Pell square | strictly positive integers | 10 | 750 | 81 |
| Doubled Pell mixed | strictly positive integers | 10 | 560 | 82 |

The direct quartics have respectively 211/212/214 residuals,
22,532/5,364/5,612 monomials and heights 394,412/195,962/128,446.
The 310 point improves variables and support against 324/5,808 at equal height,
but uses six more residuals. The 307 point prioritizes variable count, not
support or height. These are small-coefficient direct-calculus comparisons,
not fewest-variable quartics overall.

The 14-integer equation lowers the historical degree 108 to 88 at the same 119
operations. The 13-integer equation improves degree/cost 274/129 to 156/127.
The 11-integer equation improves 654/117 to 648/115. The two positive equations
save three operations against source 133's 84/436 and 85/328, at a degree cost.
Three dominated 11-integer siblings remain explicitly labeled comparisons.

Every zero-nonexistence equivalence uses the retained ordinary syntactic
refutation calibration. This is not a proof of Con(ZFC), global optimality,
or a fresh end-to-end Lean/Rocq/object-ZFC certificate.

## Contents

- `direct/`: all eight literal source and centered charts, full sparse quartics,
  transformation/restoration certificates, full ordinary proof and source closure.
- `lowdegree/` and `lowdegree/thirteen/`: two- and three-root norms, literal
  equations, complete old-zero maps, fixed coefficients and independent audits.
- `integer/`: four amplified product carriers, with only 648/115 claimed as a
  new frontier improvement; complete interpolation and sign-order proofs.
- `positive/`: two product-square circuits and their exact whole directly indexed
  BFS943 tuple, finite coefficient specification and ordinary native proof.
- `review/`: independent mathematical, exact algebraic, data and package reviews.
- `baseline/`: immutable selected comparisons, late accepted 327/page updates,
  independently recollected coefficients and historical graph census.
- `prior/wave16/`: exact preceding release and its transitive source closure.
- `report/`: editable TeX, PDF, source maps and final visual-QA receipt.

## Reproduce without modifying the release

Python 3.12.14 and SymPy 1.14.0 reproduce exact audit receipt bytes.

On Windows, extract to a short location (for example `C:\r`) and use a
long-path-capable ZIP extractor and Python environment when needed. The
inherited, hash-verified dependency tree has paths up to 238 characters
relative to the release root, before the extraction prefix. Keep the
directory structure intact; do not rename or flatten individual dependencies.

    python -B reproduce.py --receipt ../round17-replay/REPRODUCE_CHECK.json

The runner checks all recorded inventory/code hashes, rebuilds in isolated
normal and optimized copies, compares declared outputs byte-for-byte and runs
negative controls. No network, machine simulation or consistency search runs.
Review code and provenance before execution: a manifest is not a signature.

To check the delivered ZIP too:

    python -B reproduce.py --archive ../ConZFC_Odd_Helpers_Saturated_Carriers_2026-10-25.zip --verify-only

To rebuild the PDF outside the sealed tree:

    sh report/build_report.sh

TeX toolchains may yield different PDF bytes. The included PDF is compiled and
visually inspected, and the single-file TeX is checked against the modular
source. Final archive creation checks two fixed-metadata ZIPs for byte identity.

No repository write, commit, issue or third-party publication was performed.
