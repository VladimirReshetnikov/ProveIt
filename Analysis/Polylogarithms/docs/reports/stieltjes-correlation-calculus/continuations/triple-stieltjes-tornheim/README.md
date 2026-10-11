# Triple Stieltjes Correlations

**Colored Tornheim Jets, Harmonic Contact Terms, and Exact Gamma Reductions**  
Research continuation prepared for Vladimir Reshetnikov — ProveIt programme  
10 October 2026; prepared with OpenAI ChatGPT

## Reading

Start with `article.pdf` (27 pages). `article.tex` is the modular source;
`article_standalone.tex` contains the entire article and bibliography in one
file. The modular and standalone sources are both provided for integration.

The article answers the explicit three-shift representation question in
`stieltjes-correlation-calculus/continuations/shifted-hurwitz-jets/`.
Its principal results are:

- An entire continuation of the nontrivially colored Tornheim family, a
  six-sector triple product identity, and an all-index formula for canonical
  finite parts of three separated Stieltjes functions (Theorems 3.1, 4.1, 4.2).
- Three convergent logarithmic Mellin integrals in polylogarithm order
  derivatives, with the required endpoint constants at every index
  (Theorem 5.1).
- Ordinary products of normalized primitives and a contact-complete
  derivative extension. Complete homogeneous harmonic coefficients govern
  the primitives; elementary harmonic coefficients govern the contact terms
  (Sections 6–7).
- Finite single-Stieltjes reductions for one Stieltjes factor and arbitrarily
  many separated reflected digamma factors. At index zero and rational
  shifts, this gives finite log-Gamma evaluations (Sections 8–9).

One explicit specialization is

    PV integral_0^1 psi(x) cot(pi(x-1/4)) cot(pi(x-1/2)) dx
      = EulerGamma + 4 log(2) + 3 log(pi) - 4 log(Gamma(1/4)).

The principal values are symmetric at 1/4 and 1/2. The singularity at zero
is removable; the integrand tends to -pi there. The generic Stieltjes
triple uses a different, explicitly specified one-sided finite-part
normalization. These conventions must not be interchanged.

## Reproduction

From this directory, with Python and a TeX distribution installed:

```sh
python -m pip install -r requirements.txt
python code/verify_exact.py
python code/verify_numerical.py --dps 50
python code/build_article.py
python code/verify_manifest.py
```

The numerical suite is substantially slower than the finite exact suite.
The scripts are local and require no network access after dependency
installation. `build_article.py` runs three `pdflatex` passes and refreshes
the flattened source. LaTeX needs the packages listed in `article.tex`,
including Latin Modern and `mathrsfs`.

To build just the standalone source, copy `article_standalone.tex` into an
empty directory and run `pdflatex` on it three times. Both source forms were
compiled in this delivery. PDF binary metadata may change on rebuilding;
a changed hash is not, by itself, a mathematical discrepancy.

`verify_manifest.py` checks the delivered snapshots. Run it before replay
when checking transport integrity: a new build or a rerun under a different
software version may legitimately replace files included in the manifest.

## Executed evidence

`results/exact_checks.json` records **621 passing exact assertions**, including
finite Fourier-sector identities, rational partial fractions, harmonic
coefficients, and deliberate corruption controls.

`results/numerical_checks.json` records **56 passing comparisons**. These
include endpoint-subtracted quadratures, rational Gamma formulas, arbitrary
cotangent depth examples, six-sector Mellin integrals against exact
Bernoulli-polynomial integrals, and three singular three-digamma products
computed by two independent integral representations.

The numerical run used 50 decimal working digits for the main checks and
40 for the more expensive Mellin/polylogarithm checks. These are
floating-point diagnostics, not interval certificates or proofs of the
infinite families. The analytic proofs are in the article. The high-index
triple and full contact families have not been exhaustively evaluated
numerically.

## Scope and integration

No GitHub or Library files were modified. Proposed placement and a
namespaced status-update fragment are in `notes/INTEGRATION.md` and
`integration/three-shift-status-update.tex`.

The source read was targeted: seven incoming ZIPs were inventoried, not
unpacked or analytically audited in full. Provenance and read limitations
are recorded in `notes/source_snapshot.json`. No false theorem was found
in the selected canonical passages; `notes/AUDIT.md` records normalization
safeguards rather than invented errata.

The result resolves the stated **representation** question, not a reduction
of every triple to single Stieltjes values. S6, the revised S8 candidate,
period independence, minimal transcendental depth, and generic collision
regularization remain outside the established claims. Classical identities
are attributed separately. Global priority and proof-assistant formalization
are not claimed.

## Artifact map

| Path | Purpose |
|---|---|
| `article.pdf` | Compiled 27-page article |
| `article.tex`, `sections/`, `references.tex` | Modular editable source |
| `article_standalone.tex` | Self-contained editable source |
| `code/verify_exact.py` | Finite exact checks and coefficient tables |
| `code/calculus.py` | Reusable numerical identity and integration routines |
| `code/verify_numerical.py` | Independent numerical comparisons |
| `code/build_article.py` | Three-pass build and standalone-source generation |
| `code/verify_manifest.py` | SHA-256 transport-integrity checker |
| `results/` | Exact coefficient tables and numerical results |
| `verification/` | Executed logs and PDF quality record |
| `notes/` | Provenance, audit, proof dependencies, and integration guidance |
| `integration/` | Additive, unapplied manuscript status-update fragment |
| `SHA256SUMS` | Hashes of every other delivered file |
