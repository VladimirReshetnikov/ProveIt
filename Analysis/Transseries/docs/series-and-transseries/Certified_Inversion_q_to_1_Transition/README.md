# Certified Inversion Through the q→1 Transition

**Signed remainders, optimal truncation, and a modular cancellation window**  
With a shortest-block law for Gaussian multinomials.

Prepared for Vladimir Reshetnikov, 29 September 2026.

## Read first

`q_transition.pdf` is the 24-page article (25 pages since the editorial
rebuild of 2026-09-29; see the last section). `q_transition.tex` is its complete,
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
`PROVENANCE.json`, `BUILD_REPORT.json`, and the
`verification/` directory containing the script, requirements and recorded
results. No font files are distributed. (Editorial note, ProveIt,
2026-09-29: the delivered checksum ledger `MANIFEST.sha256` was verified in
full on filing (batch 46) and not kept; the delivered archive remains in the
repository history, see `docs/incoming/README.md`, batch 46 row.)

## Editorial amendments (ProveIt, 2026-09-29)

Changes made after filing (batch 46 of `docs/incoming/README.md`), file by
file. Every change to the article source is marked with a
`% ed. (2026-09-29)` comment; visible additions are labelled "Editorial
note (ProveIt, 2026-09-29)" or "[Editorial addition, ProveIt, 2026-09-29.]".

- `q_transition.tex`:
  - an editorial note at the end of Section 1 naming the four sibling
    packages of the same `q → 1` merge unit
    (`../Uniform_q_Multinomial_Certified_Inversion/`,
    `../Uniform_Resurgent_Crossover_Gaussian_Binomials/`,
    `../Gamma_Core_q_to_1_Crossover/`,
    `../Theta_Resolved_Optimal_Truncation_q_Multinomial/`). It records that
    Theorems 7.2 and 8.3 re-derive, independently, the principal theorem of
    the Gaussian-binomial package: its optimal remainder
    `e^{−2πx}/(π√x)(1 + O_T(1/x))` is uniform for `0 ≤ hx ≤ T`, and its
    boundary-layer coordinate `s'` satisfies `s = s' + log π + o(1)` for the
    window coordinate `s` of (8.7) here, with agreeing balance point. The
    hypothesis here (`hx` in a compact subset of `(0, ∞)`) is narrower; the
    relative correction, the Stieltjes–Padé bounds, the parity window and
    the exact cancellation point are new here. The note also relates
    Theorem `q3:thm:double-scaling` of
    `Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/combinatorial-coefficient-calculus/Gaussian_Coefficient_Calculus/`
    (same `τ ≥ τ₀` restriction; its central case, with its `τ` equal to
    `2hx`), the canonical volume's `p0:thm:optimal-truncation`, and the
    Lean theorems `Fabius.exists_eq_in_residual_interval` and
    `Fabius.transport_bound` (the "derivative lower bound and root-existence
    bracket" of Section 11); the article cites none of them;
  - after the pre-split source path in Section 11, a note giving the
    current path;
  - `\hypersetup{pageanchor=false}` around the title page, which removes a
    duplicate `page.1` hyperlink destination;
  - four editorial bibliography entries (`ed:siblings`, `ed:gcc`, `ed:tai`,
    `ed:lean`).
- `q_transition.pdf`: rebuilt with `build.sh` (three pdfLaTeX passes); 25
  pages; no errors, warnings, undefined references, overfull boxes or
  duplicate destinations. `BUILD_REPORT.json` describes the delivered
  24-page build and is kept unchanged as its record.
- `verification/verify.py`: `results.json` is written with `newline='\n'`
  (LF on Windows too). A rerun on a copy (Python 3.13.5, `mpmath==1.3.0`,
  `sympy==1.14.0`) reproduced `verification/results.json` byte for byte, so
  the in-place default run, which rewrites that file, is harmless.
- `PROVENANCE.json` is unchanged; its `companion_source` is the pre-split
  path at the pinned commit. The companion is now
  `Analysis/Transseries/docs/series-and-transseries/Combinatorial_Transseries_Inverses/Combinatorial_Transseries_Inverses.tex`.
- `README.md`: the page-count note, the ledger note above, and this
  section.
