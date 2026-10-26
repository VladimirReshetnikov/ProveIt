# Natural quartics with triangular syntax charts

## Main result

All variables range independently over the **nonnegative integers**.
The selected natural quartic has **202 variables, 154 quadratic residuals,
9,353 expanded terms and coefficient height 1,854,167**. Its no-zero
sentence retains the inherited `Con(ZFC)` calibration. No consistency or
optimality claim is made.

| Profile | Variables | Residuals | Degree | Terms | Height |
|---|---:|---:|---:|---:|---:|
| `natural202` | 202 | 154 | 4 | 9,353 | 1,854,167 |
| `natural202_lowheight` | 202 | 154 | 4 | 16,927 | 416,488 |
| `natural203` | 203 | 155 | 4 | 6,524 | 1,979,888 |
| `natural204` | 204 | 156 | 4 | 6,503 | 1,981,520 |
| `chart202` before row-basis changes | 202 | 154 | 4 | 9,652 | 13,654,244 |
| `natural200_degree 8` tradeoff | 200 | 152 | 8 | 10,392 | 13,654,244 |

The new mathematical step is a natural-domain affine gate-chart lemma.
Twelve nonnegative forward shears simplify syntax accumulators. Their
inverse can be negative at arbitrary points, but the retained acyclic
positive gate definitions prove that it is nonnegative on EVERY zero.
No semantic outer coordinate or Pell orientation is changed. This is not
just an inherited endpoint compared against an old benchmark.

The principal quartic improves round21's 9,818 terms / height 239,204,765 to 9,353 / 1,854,167.
The low-height option further lowers height at the explicitly displayed
support cost. The 200-variable companion spends degree 8 and is not claimed
as a quartic-dimension improvement.

## Contents

* `PROOF.md`: complete new domain argument, exact sequential changes,
  application and degree-eight witness restoration.
* `report_section.tex`: article-ready mathematical exposition and table.
* `shears.json`: authoritative sequential named affine changes.
* Each profile: `equation.json`, `expanded_polynomial.json`, readable
  `residuals.txt`, all `residuals.tex`, and `variables.tsv`.
* Chart certificates: forward/inverse affine maps and original positive
  defining-row orders. Coordinate names retain inherited formal labels;
  changed numerical meanings are specified by these certificates.
* Selected basis certificates: reversible row operations, complete rows
  and metrics.
* `inherited/`: byte-preserved round21 proof/construction package, including
  its complete inherited calibration and proof chain.
* `SOURCE_PINS.json`: current upstream commit and literal mathematical
  parent hashes. `MANIFEST_SHA256.json` inventories final package bytes.

## Offline verification

Python 3 standard library only:

```sh
python3 verify.py
python3 -O verify.py
python3 build.py --output /tmp/round22-natural-rebuild
```

The aggregate verifies a clean byte-exact rebuild, independent chart and
SOS checks, forward/reverse residual-basis checks with negative controls,
all literal selected coefficient files, source hashes and all TeX
round-trips. `CHECK_*.json` and `VERIFY_*.json` record completed normal and
optimized runs. The finite checks certify algebra and finite gate criteria,
not a new kernel-checked proof of the unbounded calibrated theorem.
