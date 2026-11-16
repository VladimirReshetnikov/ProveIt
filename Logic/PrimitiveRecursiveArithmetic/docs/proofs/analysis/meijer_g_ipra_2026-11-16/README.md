# Meijer G in intuitionistic primitive recursive arithmetic

Prepared for Vladimir Reshetnikov, 16 November 2026.

## Main deliverables

- `meijer_g_ipra.pdf` — the 51-page human-readable research report.
- `paper/meijer_g_ipra.tex` and `paper/sections/*.tex` — complete LaTeX source.
- `claims/coverage.csv` — machine-readable audit of 107 claim families from the requested Wikipedia and MathWorld pages.
- `lean/` — a Lean-oriented finite-data scaffold, analytic-contract interfaces, exact object-language targets, and a module-by-module completion roadmap.
- `code/` and `evidence/` — exact coefficient checks, high-precision regression checks, coverage generation, PDF validation, and selected rendered pages.

## Mathematical contribution

The report gives the Meijer G-function a finitary iPRA reading. A theorem is a schema for fixed primitive-recursive names and explicit natural-number certificates: rational complex approximants, pole clearance, branch separation, dyadic error budgets, finite quadrature data, and primitive-recursive tail moduli.

The central construction proves agreement, on overlapping certified domains, between:

1. a finite Mellin–Barnes contour evaluator;
2. a residue normal form built from generalized hypergeometric series; and
3. the local solution of the Meijer differential equation selected by finite initial data.

Nonconfluent residues give the economical primary evaluator. Confluent poles are handled by finite Laurent jets, producing the required powers of `Log z`. The report develops the vertical and loop convergence regimes, Slater expansions, the differential equation and corrected fundamental systems, hypergeometric and terminating-polynomial conversions, cancellation/shift/inversion/multiplication identities, derivative and contiguous relations, Mellin/Euler/convolution/Laplace formulas, a rational-power product compiler, transform pairs, and the requested elementary and higher special-function cases.

The unit-circle boundary case is supplied with an explicit p-series modulus. The Whittaker transform pair is reduced constructively through explicit `U` and `1F1` representations. Source statements that silently require branch, resonance, boundary, or function-space hypotheses are repaired before being proved.

## Coverage status

The 107 source claim families are classified as follows:

| Status | Count | Meaning |
|---|---:|---|
| P | 46 | Proved directly by a finite constructive argument. |
| Q | 30 | Proved under explicit quantitative certificates omitted by the source. |
| C | 29 | Literal source statement corrected for branch/domain/resonance, then proved. |
| R | 2 | Reduced to a general certified compiler/kernel principle, without printing every specialized normalization. |
| X | 0 | Not established. |

The two `R` entries are the Wimp transform’s long auxiliary-kernel normalization and the qualitative claim that contour integration is numerically “practical.” Neither is used as an unproved premise.

## Formalization status

The mathematical report and executable checks are complete at their stated levels. The Lean files are **scaffolds**, not a completed analytic formalization. `lean/FiniteCore.lean` deliberately contains `sorry`; the artifact environment did not include the ProveIt dependency closure or a Lean executable used to compile these files.

The final trusted endpoint is not a theorem about host `Nat`, `Rat`, or `Complex`. It is a closed ProveIt derivation

```lean
[] ⊢[PRAAx] phi
```

inside `LeanProofs.ConciseIPRA`, followed only then by the checked `pra_iff_native` bridge if a theorem in the native scalar calculus is desired. No main analytic theorem in this package is claimed to have reached that endpoint.

The ProveIt snapshot used throughout is commit:

`85afffc93b2abbc1972fdfc98244052cbfbda1b3`

## Reproduce

PDF, with a TeX distribution containing the packages named in the preamble:

```sh
./build_pdf.sh
```

Exact and numerical regression checks, with Python 3.10+ and `mpmath`:

```sh
python3 -m pip install -r requirements.txt
./run_checks.sh
```

Run both:

```sh
./run_all.sh
```

The numerical checks are validation only. They do not prove universal identities or replace object-iPRA derivations.

## Trust boundary

- The report supplies human-readable constructive proofs and explicit finite reductions.
- Python verifies 1,000 exact coefficient identities and 63 high-precision numerical instances.
- PDF validation checks structure and rendering.
- The Lean directory specifies the completion path and final theorem shapes.
- No completed Lean proof of the analytic theorem collection is claimed.
