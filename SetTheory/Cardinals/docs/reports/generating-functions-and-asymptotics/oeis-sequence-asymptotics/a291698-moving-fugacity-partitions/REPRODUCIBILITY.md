# Reproducibility report

## Deliverables

The canonical editable report is `moving-fugacity-report.tex`; its PDF is `output/pdf/moving-fugacity-report.pdf`. The mathematical development is preserved independently in `theorem-and-proof.md`, SHA256 `5a90f1336fbbd5c0804f4781f436d47cb18a47ef82cefc04ef1f322d5cc9f64b`.

The report treats `[q^n] product_(k>=1)(1+n^alpha q^k)`, uniformly for alpha in any fixed compact subset of `(0,infinity)`. OEIS A291698 corresponds to alpha=1; A292304 corresponds to alpha=2. The alpha=1/2 boundary is a separate threshold for simplifying the exact dilogarithm, not an additional named OEIS specialization.

## Environment and dependencies

Tested with Python 3.12.14, mpmath 1.3.0 and SymPy 1.14.0. The two Python dependencies are pinned in `requirements.txt`. The PDF uses pdfLaTeX with Latin Modern and standard AMS, geometry, microtype, hyperref, xurl, enumitem, fancyhdr and needspace packages. No network access is needed after these dependencies are present. None of the computations uses randomness.

`build_pdf.sh` supports ordinary complete TeX installations. It also contains a local-cache workaround for managed Linux installations that have the TeX source tree but omit generated formats and filename databases. The workaround writes only a `.tex-cache` subdirectory inside the project; it does not modify the system TeX installation.

## Clean replay

Run these commands from a clean copy of the package:

```
python checks.py --max-n 20000 --output checks.json
python resonance_check.py
python validate.py
python sector_integrals.py
bash build_pdf.sh
```

The first four commands regenerate the four principal numerical JSON files. The PDF command performs two passes and fails if the last log contains an overfull box, an undefined control sequence, or a LaTeX error. The temporary compilation cache and logs are not needed to understand the proof.

## What is checked exactly

`checks.py` builds restricted-partition counts by integer dynamic programming and assembles the exact polynomial

`[q^n]F(q,u) = sum_m p_(<=m)(n-m(m+1)/2) u^m`.

For alpha=1 and alpha=2 its final value is an integer computed exactly. Fractional-alpha values use exact polynomial coefficients followed by 100-digit evaluation.

`validate.py` independently computes the product coefficients by descending weighted knapsack updates, with 120 exact comparisons covering n=1 through 60 and alpha=1,2. It also compares all 24 displayed A292304 terms, including n=0, with the public sequence listing. Every exact comparison passed.

## Numerical checks and interpretation

- Forty-four selected `(alpha,n)` comparisons cover alpha=1/4,1/2,1,2 and n through 20,000. Principal Bessel approximants use endpoint depths M=0,3,5,9
- The finite resonance diagnostic evaluates K=0 through 8, retaining M=9
- Three real/complex Jacobi identity evaluations agree to better than 3e-77 at the chosen precision
- Finite-sector inverse diagnostics use the exact-sequence logarithm as a target and compare the recovered continuous index with its known integer index
- Local-sector quadrature uses 70 digits. At alpha=1,n=20,000 it agrees with the M=9 principal local expansion to about 1.28e-28 relative and with the first complex sector to about 3.61e-27

These are numerical diagnostics, not interval-certified bounds. High-precision agreement is not a substitute for the proof. The principal error for alpha=2 at n=20,000 is still about -5.58%, and increasing algebraic depth alone does not remove it. Two conjugate pairs reduce it to about -5.09e-5. This is why the report keeps exact resonance-sector integrals and a practical slow-onset warning.

## Mathematical and numerical stopping conditions

The report proves fixed-depth all-orders expansions and fixed-sector exponential separation. It does not claim a growing K theorem, infinite Bessel-sector convergence, optimal truncation, or explicit finite-input big-O constants. The exact amplitude is deformed only within the right half-plane; the full-circle residue is used only after polynomial truncation.

The continuous inverse is defined using a specified saddle-Fourier continuation. A numerical inverse close to an integer must not be rounded without a certified error enclosure or exact neighboring coefficient checks.

## Further reproducibility work

The next useful extension is interval-certified quadrature for the exact local-sector integrals, together with explicit constants in the outer-arc and Euler-Maclaurin bounds. The current programs intentionally do not advertise certification they do not perform.
