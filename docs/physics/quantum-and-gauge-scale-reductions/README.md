# Surreal Scales in Quantum Theory and Gauge Models

**Rare-event shadows, exact elimination, and quaternionic curvature**
Research manuscript prepared for Vladimir Reshetnikov, 23 September 2026.

## Repository placement

Placed in `66d7e55`. The maintained base is [article.tex](article.tex), from
source 07; there is no maintained PDF yet. Its delivered verification
program and output are
[code/07-scales-in-physics-verify_examples.py](code/07-scales-in-physics-verify_examples.py)
and [data/07-scales-in-physics-verification_results.txt](data/07-scales-in-physics-verification_results.txt).
The observable-limits (03), gauge-holonomy (04) and quantum-operations (08)
companions remain to be integrated. Their audit notes, programs and recorded
outputs are retained under the corresponding prefixes. Independent proof
review, source reconciliation and Lean verification remain pending.

The contents and reproduction instructions below describe the delivered
source-07 package and its original filenames. They are not a build record
for this repository. To typeset the maintained base here, run
`pdflatex -halt-on-error -interaction=nonstopmode article.tex` from this
directory until references stabilize. Run finite checks separately using
the prefixed program above and write new output to a scratch directory.

## Contents

- `surreal_scales_physics.pdf` — 31-page article, including the cover, with proofs and 17 bibliography entries.
- `surreal_scales_physics.tex` — complete LaTeX source with an embedded bibliography.
- `verify_examples.py` — exact symbolic checks of selected finite identities and examples.
- `verification_results.txt` — the supplied successful run: 43 named checks.
- `requirements.txt` — the tested SymPy version.
- `build.sh` — rebuild the PDF and regenerate the example-check record.

## Main results

Theorem 5.1 computes the leading ordinary conditional state of a nonzero finite Kraus branch even when its success probability is infinitesimal. Theorem 5.4 gives two states indistinguishable modulo every power of a selected parameter but having orthogonal rare conditional outputs. Theorem 6.2 proves the sharp success-weighted trace-distance bound.

Theorem 7.1 constructs an exact invariant low-energy graph for independently separated high-energy scales, proves that the complementary spectrum is positive unlimited, and gives a controlled Hermitian effective-Hamiltonian correction. Its uniform real-parameter counterpart is Corollary 7.3. Proposition 8.1 gives a three-level virtual-selection counterexample.

Theorem 9.2 explains the complex simulation of finite surquaternion instruments; Theorem 9.4 isolates a precise obstruction to a naive quaternionic composite. Theorem 10.2 gives the gauge-invariant leading valuation and coefficient of a positive finite Wilson-loop action. Section 11 includes finite algebraic Bell and canonical-commutation obstructions.

The scalar field is denoted K and the effective Hamiltonian L. The verification program's internal variable names need not coincide with the manuscript's notation.

## Scope and claim status

This is an unrefereed, AI-assisted mathematical research manuscript. It supplies mathematical proofs under explicit hypotheses; it does not certify historical priority or claim a new experimental prediction. Classical results—including Schrieffer–Wolff reduction, quaternionic complex simulation, Wilson-loop algebra, and the Tsirelson bound—are attributed, not claimed as discoveries.

The exact-check program verifies finite polynomial and finite-series identities only. It does not implement arbitrary Hahn series, construct the full surreal field, prove the general theorems, or constitute Lean verification. The all-rank existence arguments depend on strong Hahn summability and formal implicit evaluation, not on an invalid assumption that powers of a positive valuation are cofinal.

The uniform O(tau^2) effective-Hamiltonian remainder does not certify every deeper term displayed inside its first correction. In a higher-rank hierarchy, such a retained term may be smaller than omitted terms from a larger scale; the exact graph or a support-aware expansion is then necessary.

## Repository baseline

Repository: https://github.com/VladimirReshetnikov/Surreal

Inspected snapshot:
`c0a36eebe5cf30aa72abfe4ef8ff9e46f63c3c28`.

The review used the repository README, its physics-report README, directory/tree metadata, and targeted code-index searches. It was not a full source audit. The existing physics report already includes the finite quantum-shadow theorem and its restriction to nonzero-standard-probability conditioning. This article treats those as prior project results.

A local Git clone was unavailable in the execution environment. No repository Lean build was performed and no new Lean theorem is claimed. Bibliographic sources and the novelty boundary are documented in the article.

## Reproduce

The checks were run with Python 3.13.5 and SymPy 1.14.0. Install the dependency in a suitable Python environment and run:

```sh
python -m pip install -r requirements.txt
python verify_examples.py --output verification_results.txt
```

For the PDF, a TeX distribution with pdfLaTeX, latexmk, Latin Modern, and the standard packages listed in the source is required. Run:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error surreal_scales_physics.tex
```

Alternatively, `sh build.sh` builds into `build/`, copies the final PDF alongside the source, and reruns the symbolic checks.

The supplied PDF was compiled with pdfLaTeX, all 31 pages were rasterized and inspected, and the final compile reported no overfull boxes or undefined references. The source includes no external figures or bibliography files. No font files are distributed.
