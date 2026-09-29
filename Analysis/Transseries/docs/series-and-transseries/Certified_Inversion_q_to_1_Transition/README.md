# Certified Inversion Through the q→1 Transition

**Signed remainders, optimal truncation, and a modular cancellation window**  
With a shortest-block law for Gaussian multinomials.

Prepared for Vladimir Reshetnikov, 29 September 2026.

## Read first

`q_transition.pdf` is the 24-page article. `q_transition.tex` is its complete,
editable, self-contained LaTeX source. It does not require files from ProveIt.

The article develops explicit analytic refinements of the q→1 chapter in the
ProveIt companion *Combinatorial Transseries and Their Inverses*. The repository
snapshot and source identifiers are recorded in `PROVENANCE.json`.

## Main results

- Theorem 3.2: an exact positive-kernel remainder and signed first-omitted-term
  bounds, for every positive h and x. Corollary 3.3 gives fixed-order control
  uniform down to hx=0 in the composite expansion.
- Theorems 5.1 and 5.2: a determinate Stieltjes measure and two-sided convergent
  Padé bounds for the finite-size correction.
- Theorem 7.2: the sharp optimal remainder, including its first relative
  correction, for h→0, hx in a compact positive interval, and M=πx+O(1).
- Theorems 8.2 and 8.3: the additive inverse-error law and parity-sensitive,
  logarithmically shifted cancellation window. Proposition 8.4 locates an
  exact cancellation point for each fixed even order M≥2.
- Theorem 9.2: shortest-block universality for Gaussian multinomials.

The paper also gives a real Borel reconstruction, explicit finite-sum tail
bounds, a repository crosswalk, and twelve further research questions.

## Scope and verification

These are proof-based research claims, not independently refereed or
machine-checked theorems. Worldwide priority for the explicit refinements has
not been established. The paper attributes the classical modular,
partial-fraction, moment, and summation machinery and distinguishes it from
its proposed refinements. It does not claim to solve a general conjecture
about all transseries or cover the fixed-h, hx→∞ sharp-asymptotic regime.

The runnable program `verification/verify.py` makes exact-rational Padé and
Hankel checks and high-precision analytic checks. It tests the formula against
independent finite Gaussian products, checks remainder signs and analytic
sum-tail bounds, checks optimal prefactors and multinomial multiplicities,
and reevaluates nonlinear inverse residuals in the cancellation window.
All assertions passed in the recorded run in `verification/results.json`.

Floating-point checks use mpmath and are **not outward-rounded interval
certificates**. Small nonzero residuals may reach the arithmetic precision
floor. The recorded decimals are tests, not the proofs of the inequalities.
No Lean formalization is included, and no repository files were modified.

## Reproduce

Python 3.10 or newer:

```sh
python -m pip install -r verification/requirements.txt
python verification/verify.py
```

The script has no network dependency after installation. It overwrites its
local `verification/results.json`. With the recorded environment the full
verification run took about 16 seconds; performance varies by machine.

Build the PDF with TeX Live and the packages named in the source:

```sh
sh build.sh
```

The bibliography is embedded in the TeX source. No BibTeX step or external
notation file is required. The PDF was compiled through stable references;
the final LaTeX log contained no warnings, undefined references, overfull
boxes, or underfull boxes. All pages were rendered and visually inspected.

## Files

`q_transition.tex`, `q_transition.pdf`, `README.md`, `build.sh`,
`PROVENANCE.json`, `BUILD_REPORT.json`, `MANIFEST.sha256`, and the
`verification/` directory containing the script, requirements and recorded
results. No font files are distributed.
