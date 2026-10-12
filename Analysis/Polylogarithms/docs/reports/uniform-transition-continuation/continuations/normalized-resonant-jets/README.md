# Resonant Polylogarithmic Jets and Convergent Inverse Transseries

**Gamma normal forms, optimal dilation filters, arithmetic sector selection, and exact order tuning**

Research draft prepared for Vladimir Reshetnikov, 11 October 2026, for integration into the Polylogarithms and Transseries areas of ProveIt.

## Read first

`resonant_polylog_transseries.pdf` is the 23-page article. Its complete self-contained source is `resonant_polylog_transseries.tex`. No external figures, bibliography processor, local notation file, or custom font installation is needed.

The article gives conventional proofs of the all-order statements. The finite exact tests and high-precision comparisons are supporting diagnostics, not proofs of the analytic theorems. No Lean formalization, independent refereeing, or exhaustive priority determination is claimed. This package has not been accepted into or written to the repository.

## Main results

1. **Pure-logarithm Gamma-normalized order jets.** Every fixed integer resonance and finite order derivative has the exact form `t^m (L^(r+1) + B(t))`, with `L=-log(t)` and a holomorphic tail with explicit zeta-derivative coefficients. The counterterms are finite Stieltjes/Gamma coefficient combinations.
2. **Optimal dilation filtering.** A centered filter with exactly `d` nodes converts a degree-`d` logarithmic core to `L` without a constant term. A Vandermonde argument proves the minimum node count. The transformed tail and its reduced guaranteed radius are explicit.
3. **Convergent inverse coefficients.** An analytic chart in the independent coordinates `(v,w)=(t0,1/(-log(t0)))` gives a finite Lagrange formula and a separate coefficient recursion. Possible coefficient poles occur only at `m-dw=0`; their maximal order is sharp when the first tail coefficient is nonzero. A three-generator Taylor chart gives a genuinely convergent original-variable power/log/loglog expansion.
4. **Arithmetic selection and restoration of inverse sectors.** The zeroth-jet tail at the half shift is even, so its inverse contains only odd powers of the exact core. The first normalized order derivative restores the missing first sector with an exact coefficient involving `log(2)`.
5. **Order confluence and exact tuning.** A uniform chart works when the order offset times the core logarithm remains bounded. At the half shift a unique analytic order adjustment cancels the entire analytic remainder. The first two coefficients of that adjustment are explicit, and its all-order recurrence does not involve the Gamma normalizer.
6. **A version-specific source correction.** Equation (52) in the inspected author-hosted Bailey–Borwein–Crandall PDF has the opposite sign from its own equation (49). The article proves the corrected formula and an exact nonzero counterexample. No new defect in a canonical ProveIt theorem is asserted.

The classical Lerch expansion, raw order derivatives, Lambert W, Lagrange inversion, Bernoulli identities, finite differences, and Catalan fold mechanism are attributed rather than presented as new discoveries. The explicit refinements and their combination are proposed contributions; worldwide novelty has not been established.

## Reproduce the checks

Python 3.10 or newer:

```sh
python -m pip install -r requirements.txt
python verification/verify.py --part all --output-dir replay
python verification/verify_extensions.py --output-dir replay
```

The reference run used Python 3.13.5, SymPy 1.14.0, and mpmath 1.3.0. All calculations are offline after dependency installation. Both scripts accept `--output-dir`; omitting it writes to `data`, replacing the corresponding delivered records. The recorded JSON files use LF line endings, including on Windows. Timings are machine-dependent and are not byte-reproducibility claims.

The complete delivered run passed **576 finite exact assertions and 89 numerical comparisons**. This comprises 568 base exact assertions, eight tuning-coefficient identities, 47 base high-precision comparisons, 12 inverse comparisons, and 30 extension comparisons. The numerical work uses 80 working decimal digits but is **not outward-rounded interval arithmetic** and does not claim 80 certified digits.

`verification/verify.py` includes two independently implemented finite coefficient constructors:

```python
from fractions import Fraction as Q
from verification.verify import inverse_recursive, inverse_lagrange

# B(t)=t/4-t^2/72+t^4/14400+... for the normalized dilogarithm.
b = [Q(0), Q(1,4), Q(-1,72), Q(0), Q(1,14400)]
coefficients = inverse_recursive(m=1, d=1, w=Q(1,10), b=b, n=4)
assert coefficients == inverse_lagrange(m=1, d=1, w=Q(1,10), b=b, n=4)
print(coefficients[1:])  # Exact rational C_1,...,C_4 at w=1/10.
```

Here `b[0]` must be zero and the list must contain every coefficient through the requested order. These functions calculate the coefficient germ; they do not certify a numerical convergence radius or validate arbitrary user input.

## Build the PDF

With a standard TeX Live installation:

```sh
sh build.sh
```

On Windows with PowerShell and `pdflatex` on PATH:

```powershell
./build.ps1
```

Both scripts run three pdfLaTeX passes. Alternatively run `pdflatex -interaction=nonstopmode -halt-on-error resonant_polylog_transseries.tex` three times. The delivered build had no warnings, undefined references, overfull boxes, or underfull boxes. All 23 pages were rendered and reviewed in contact sheets, with selected formula- and table-heavy pages reviewed at full size; see `BUILD_REPORT.json`.

## Integration and provenance

`integration/INTEGRATION.md` proposes a primary report location and Transseries cross-reference. `integration/THEOREM_STATUS.json` records the statement labels and proof status. `integration/CORRECTIONS.md` scopes the sign correction and the precautions needed when reusing the formulas. `PROVENANCE.json` and `provenance/SOURCE_AUDIT.md` record the targeted source inspection and known overlaps.

The main branch moved during inspection. Individual inspected file blob identifiers are recorded rather than asserting a false single-commit snapshot. Repository overviews were used for orientation and scope; neither area was exhaustively audited.

The article includes twelve further research questions. The priority targets are continuation of the exact tuning curve, unbounded order-resonance products, higher-order sector-restoration loci, and certified chart radii.

No external full paper, font file, repository checkout, or untested proof-assistant file is included. `MANIFEST.sha256` covers all delivered files except the manifest itself.
