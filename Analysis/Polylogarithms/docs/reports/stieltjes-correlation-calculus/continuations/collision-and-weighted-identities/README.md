# Exact Identities for Polylogarithms, Harmonic Zeta Functions, and Stieltjes Finite Parts

Research continuation for Vladimir Reshetnikov's ProveIt project, dated 10 October 2026.

## Read and build

- `article.pdf` is the complete research article.
- `article.tex`, `sections/*.tex`, and `references.tex` are the editable modular sources.
- `article_standalone.tex` contains the same complete article in one TeX file.
- `python build.py` builds the modular source with three pdfLaTeX passes and regenerates the standalone source. It requires standard TeX Live packages and Latin Modern fonts; no shell escape or network access is used. It rejects undefined references and overfull boxes.

To build the standalone file directly, run `pdflatex article_standalone.tex` three times. Its output will be named `article_standalone.pdf`.

## Mathematical contents

1. A complete colliding unequal-dilation finite-part calculus, including all Stieltjes and argument derivatives, a convergent collision expansion, and odd-order cancellations.
2. Every nonlinear coordinate contact coefficient, its composition law, sharp unit-tangent thresholds, and exact antiderivative endpoint constants.
3. A finite colored-Tornheim formula for three separated unequal frequencies and all their Stieltjes and argument coefficients.
4. Fully shifted height-one harmonic sums: an entire Gamma-normalized difference, finite Stirling corrections, every Laurent principal part and finite part at nonpositive integers, exact pole orders, and Gamma primitives.
5. A real two-term trilogarithmic evaluation of the weighted arctangent integral; an inverse-hyperbolic companion; ordinary and higher Euler primitives.
6. A source audit and thirteen precise further research questions.

The short S6 and current S8 conjectures remain unresolved. S4 was already proved in the source. No historical-priority, numerical-independence, or Lean-formalization claim is made.

## Reproduce the audits

Python 3.12.14, SymPy 1.14.0, and mpmath 1.3.0 were used. Install the two Python packages from `requirements.txt` in your own environment if needed, then run:

```bash
python code/run_all.py
```

The driver runs seven mathematical scripts (three at a time by default), records subprocess logs under `results/logs/`, and validates the JSON results. Use `--jobs 1` for a sequential run. Runtime depends on the machine; the Stieltjes quadrature and weighted-Tornheim integrations are the slowest parts. `--validate-only` checks the delivered JSONs without recomputation.

The run comprises 167 numerical comparisons, 213 exact nonlinear checks, 33 exact collision checks, four exact weighted differential checks, and an exact coefficient obstruction. The floating-point comparisons are not interval certificates. The analytic proofs, including their domains and branch conventions, are in the article.

The exact collision coefficient generator accepts arbitrary nonnegative indices:

```bash
python code/exact_collision_coefficients.py 1 0 0 1
```

Here the four arguments are the Stieltjes indices `m,n` and argument orders `r,k`. Formal `Z_j` means `zeta^(j)(r+k+1)` when `r+k>0`; `G_j` means the ordinary Stieltjes constant `gamma_j` in the zero-order case. The script does finite symbolic arithmetic and can become expensive at high total degree. With no arguments it regenerates the included low-order audit table.

## Integration and provenance

The baseline is commit `445f754610e1377939235794de84ed9075fc09f5`. `provenance/snapshot_manifest.json` records the 85 inspected file payloads and Git blob identifiers. The source comparison includes the unified manuscript and the five current polylogarithm archives under `docs/incoming` at that commit.

See `integration/INTEGRATION.md` for a section map, label namespaces, and exact claim-status changes. `integration/canonical_corrections.patch` proposes two small corrections to canonical chapter 03. It was checked on a temporary copy of the pinned source; it has not been applied to the repository. The correction notes acknowledge that both issues were previously flagged.

No repository files were pushed or changed. The archive omits TeX build caches and downloaded third-party source PDFs. `SHA256SUMS.txt` records the final delivered files.
