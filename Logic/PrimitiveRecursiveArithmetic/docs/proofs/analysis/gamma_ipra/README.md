# Gamma in intuitionistic primitive recursive arithmetic

Prepared for Vladimir Reshetnikov, 15 November 2026.

## Main deliverable

`paper/gamma_ipra.pdf` is the complete human-readable research report.
`paper/gamma_ipra.tex` and `paper/sections/*.tex` are its complete LaTeX sources.
The coverage ledger records 62 result families, with exact domain and
formalization qualifications.

The development constructs gamma from finite Euler products, supplies explicit
primitive recursive error bounds, identifies the Euler integral, and proves
functional, reflection, multiplication and beta identities; poles, residues
and the entire reciprocal; derivative and power-series formulas; convexity,
effective Bohr–Mollerup, gamma inequalities and real critical points; real
Stirling expansions with signed remainders; both Binet formulas on the
complex right half-plane; Raabe and gamma–zeta Mellin integrals; and additional
special-value and integral consequences.

## Exact scope

The iPRA reading is a first-order theorem schema for each fixed primitive
recursive name with its explicit numerical certificates. It does not assume
a universal primitive recursive evaluator, a sort of arbitrary reals,
unrestricted real-order decisions, or a Cauchy-completeness axiom. Complex
division requires quantitative apartness. Derivative and asymptotic orders
can be read as externally fixed theorem families.

The report provides the human-readable mathematical argument. The full Lean
analytic development and its compilation into ConciseIPRA's object theory
remain the specified formalization work. The executable certificate
interfaces are not silently assumed to be inhabited.

## Archive contents

- `paper/`: the report, PDF and all LaTeX source sections.
- `lean/GammaIPRA.lean`: executable rational definitions, fourteen proved
  finite arithmetic lemmas, and explicit uninstantiated analytic contracts.
- `lean/README.md`, `lean/build.sh`, `lean/lean-toolchain`: reproduction
  instructions, Lean version and scope details.
- `lean/proof_audit.txt`: successful Lean compilation and axiom audit.
- `code/gamma_brackets.py`: exact-rational positive gamma enclosures using
  Euler strip brackets and bounded integer-root bisection.
- `evidence/gamma_brackets.json`: eight exact finite arithmetic certificates.
- `evidence/validation.txt`: outward-rounded displayed enclosures and checks.
- `evidence/quality_report.json`: final document and code validation summary.
- `SOURCE_MANIFEST.json`: source URLs and inspected repository identifiers.
- `build_pdf.sh`: ordinary TeX rebuild command.
- `SHA256SUMS.txt`: SHA-256 checksums of the packaged files.

## Reproduce

With a standard TeX distribution providing the packages named in the preamble:

```sh
./build_pdf.sh
```

With Lean 4.32.0 available:

```sh
cd lean
lean GammaIPRA.lean
```

Or use `GAMMA_LEAN_BIN=/absolute/path/to/lean ./lean/build.sh` from this directory.
The companion imports only `Std`; Mathlib is not required to check this file.
Every one of its fourteen named lemmas reports no axiom dependencies. This
audit applies to those elementary lemmas, not to the unformalized analysis.

With Python 3.10 or later:

```sh
python3 code/gamma_brackets.py --bits 8 \
  --output evidence/gamma_brackets.json \
  --validation evidence/validation.txt
```

The numerical program uses integers and `fractions.Fraction` only. It verifies
the integer-root inequalities, rational interval widths and outward decimal
rounding. Its enclosure interpretation relies on the bracket theorem proved
in the report; finite examples do not prove universal gamma identities.

## ProveIt integration point

The inspected repository snapshot is
`94a4713736d281e1bfcd0b54e0acb6410136971c`.
The ordinary object theory is `LeanProofs.ConciseIPRA.PRAAx`, and the bridge
`pra_iff_native` in `ConciseIPRA.NativeBiInterpretation` translates completed
ordinary arithmetic derivations into the native concise calculus. The report
gives the target formulas, induction invariants, precision allocation, and
module dependency order for producing those derivations.

## Explicit omissions

The package does not claim Hölder differential transcendence, special-value
irrationality or transcendence, elliptic singular-value formulas, Kummer's
Fourier series, continued-fraction identities, Hankel contour formulas,
correctness of particular numerical-library approximations, the full complex
sector Stirling expansion, or the zeta functional equation. It does not
claim a completed Lean proof of the analytic theorem collection.
