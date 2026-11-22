# Continuous probability in intuitionistic primitive recursive arithmetic

Research prepared for Vladimir Reshetnikov, 20 November 2026.

Start with **`paper/report.pdf`**. Its complete source is `paper/report.tex` and
the included section and reference files. The report develops a represented
fragment of continuous probability using fixed primitive recursive programs,
finite rational inequalities, quantifier-free induction, and explicit error
moduli. It includes the human proofs, the necessary representation data, and
a staged route to embedded Lean derivations in ProveIt's iPRA calculus.

## Main mathematical results

- One coherent fair-bit cylinder algebra supports events and random variables
  in the bounded convergence-in-probability metric, with stronger `L1` and `L2`
  names when moments are available.
- Expectation, products, independent copies, countable additivity with tail
  moduli, quantitative Vitali and dominated convergence, and dyadic conditional
  averaging are constructed from finite observations.
- Uniform, exponential, normal, Cauchy, and singular continuous Cantor laws are
  developed. A coherent dyadic histogram sampler realizes effective densities
  on the same bit space and preserves supplied moment-tail certificates.
- Gaussian normalization and moments, Gaussian conditioning, guarded Bayes
  updating, bounded stopping, a first Borel--Cantelli fragment, and a Gaussian
  autoregressive stationary-law example have explicit finite error bounds.
- The weak law has bound `V/(n epsilon^2)`. The finite-window strong-law bound
  is `4V/(N epsilon^2)`, with exceptional-event certificates under the stated
  threshold-presentation hypotheses.
- A complete elementary Lindeberg argument gives CDF error
  `eta + 10(B+2)/(sqrt(n) eta^3)` when the standardized third absolute moment
  is at most `B`. A sufficient sample size for error `delta` is
  `ceil(25600(B+2)^2 delta^(-8))`. This is a conservative explicit rate.

The report distinguishes event names from arbitrary classical measurable
sets, ordinary random variables from integrable ones, positive separation
data from a negation of zero, and uniform primitive recursive families from
nonuniform collections of computable objects. These distinctions are part of
the mathematical foundation, not additional axioms.

## Exact formalization status

The standalone Lean 4.19.0 project was built successfully using only its bundled
`Std` library. It contains **30 proved named theorems and three checked closed
examples**, plus compiling representation specifications. Its source has no
unfinished proof or new axiom declarations. Representative axiom reports are
included.

These are checked semantic Lean proofs of finite arithmetic and probability.
The continuous theorems in the report are supplied as human arguments and
formalization specifications; **their complete embedded iPRA proof objects
are not part of this package**. A semantic proof or a structure's contract
field is not substituted for an actual `Prf PRAAx` derivation. The report's
formalization section and `lean/ROADMAP.md` identify the remaining work and
its required quantifier-free induction invariants.

The existing ProveIt repository has richer object-language finite probability
providers. They were inspected at pinned commits, not rebuilt here. Their
roles and their limits are recorded in `metadata/PROVIDERS.md` and
`metadata/source_manifest.json`. Upstream sources are not vendored or modified.

## Files

| Path | Contents |
|---|---|
| `paper/report.pdf` | Complete human-readable report. |
| `paper/report.tex`, `paper/sections/*.tex`, `paper/references.tex` | Complete editable LaTeX source. |
| `lean/` | Standalone checked kernel, compiling specifications, validation driver, axiom reports, and completion roadmap. |
| `code/probability_kernel.py` | Exact-rational reference implementation of cylinder tables, selected laws, Gaussian enclosures, smoothing, and precision budgets. |
| `code/verify.py` | Reproducible finite checks, with a JSON receipt. |
| `metadata/` | Pinned source records, provider map, and theorem-status ledger. |
| `validation/` | Verification receipts and a description of what they establish. |
| `build_pdf.py` | Portable pdfLaTeX build driver. |
| `reproduce.py` | Convenient entry point for the arithmetic checks and optional Lean/PDF rebuilds. |
| `SHA256SUMS` | Checksums of all other packaged files. |

## Reproduction

Run commands from the extracted `ipra_probability` directory.

### Exact arithmetic checks

Requires Python 3.10 or newer, with no third-party Python packages:

```sh
python3 reproduce.py
```

The supplied run passed **2,963 checks**, using integers and `fractions.Fraction`
for every acceptance comparison. Its certified normal CDF enclosure is

```text
882141/1048576 <= Phi(1) <= 55143/65536
```

The script recreates `validation/exact_checks.json`. These finite computations
are regression and certificate checks, not a replacement for universal proofs.

### Lean kernel

Install Lean 4.19.0 and its matching `lake` executable, or use the supplied
`lean-toolchain` with an existing Elan installation. Then run:

```sh
python3 reproduce.py --lean
```

This runs the arithmetic checks, `lake build`, and `lake env lean Validation.lean`.
The project has no Mathlib, ProveIt, or other package dependency. Compiler
binaries and build caches are excluded from the archive. The original build
and axiom reports remain in `lean/validation.log` and `lean/toolchain.log`.

### PDF

Use a working pdfLaTeX installation with the packages listed in
`paper/report.tex`; a standard TeX Live or MiKTeX installation supplies them:

```sh
python3 reproduce.py --pdf
```

The PDF driver runs three passes and refreshes `validation/latex_build.log`.
It reports missing characters, unresolved references, and overfull boxes for
review. `IPRA_PDFLATEX` may select a particular compiler. Optional
`IPRA_PDF_FORMAT` and `IPRA_FONT_MAP_DIR` support a separately prepared local
format and font map on minimal installations; ordinary installations do not
need these settings. The prebuilt report is included for immediate reading.

To request every stage:

```sh
python3 reproduce.py --lean --pdf
```

Rebuilding may alter PDF timestamps and build logs. Verify `SHA256SUMS` before
rebuilding if checking the integrity of the original delivered package.

