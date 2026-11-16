# The normal distribution in intuitionistic primitive recursive arithmetic

Prepared for Vladimir Reshetnikov on 16 November 2026.

## Main deliverables

- `paper/normal_distribution_ipra.pdf` — 46-page human-readable manuscript.
- `paper/normal_distribution_ipra.tex` and `paper/sections/*.tex` — complete LaTeX source.
- `THEOREM_LEDGER.md` — statement-by-statement coverage of the inspected Wikipedia and MathWorld pages.
- `lean/` — a concrete Lean 4 blueprint, object-language targets, and completion roadmap.
- `code/gaussian_certificates.py` — exact-rational certificate generator.
- `evidence/validation.json` and `evidence/validation.txt` — recorded 96/96 validation run.
- `provenance/` — source inventory, repository snapshot, and trust boundary.

## Mathematical scope

The manuscript reconstructs a large portion of elementary and intermediate Gaussian theory in a form suitable for first-order intuitionistic primitive recursive arithmetic (iPRA). Real numbers and functions are fixed primitive-recursive rational names with explicit moduli; integrals are finite quadrature certificates with tail bounds; limiting claims are uniform rational inequalities with primitive-recursive witnesses.

The proved or effectively reconstructed families include:

- normalization, standardization, density, CDF, error function, symmetry, shape, and support;
- two globally convergent CDF expansions, Mills inequalities, finite tail asymptotics, effective quantiles, and safeguarded Newton iteration;
- all integer moments, absolute moments, Hermite identities, truncated moments, transforms, cumulants, Wick formulas, and Stein's identity;
- entropy, maximum entropy under effective hypotheses, KL and Hellinger distances, Fisher information, and expected-max bounds;
- affine and convolution closure, stability, infinite divisibility, multivariate projections, Gaussian independence criteria, and conditional laws;
- folded/half-normal, chi-square, chi, Rayleigh, Maxwell, Cauchy-ratio, product-normal, and lognormal laws;
- exact normal-sample decomposition, sample mean/variance, maximum likelihood, Student t, Fisher F, confidence pivots, inverse-CDF generation, and Box–Muller generation.

The existing ProveIt central-limit packet is reused for quantitative CLT and Berry–Esseen claims. Deep converse characterizations such as the full Cramér, Kac–Bernstein, Geary, and Marcinkiewicz theorems are explicitly marked as deferred rather than smuggled in through classical semantic assumptions.

## Constructive meaning

“Provable in iPRA” means a theorem schema for fixed primitive-recursive presentations. A completed formal endpoint has the literal form

```text
[] ⊢[PRAAx] φ
```

in namespace `LeanProofs.ConciseIPRA`, followed when desired by `pra_iff_native`. The manuscript gives the encodings, induction invariants, finite verifiers, precision allocation, and module dependency order needed to construct those derivations. It does not posit a universal evaluator for all primitive-recursive programs or quantify over a completed real line.

## Status and trust boundary

- Human-readable mathematics: complete for the theorem families labelled P/E/R/C in the ledger.
- Exact executable validation: 96/96 checks pass, using `int` and `fractions.Fraction` for every proof-relevant computation.
- PDF: compiled successfully with `latexmk`/`pdflatex` and visually inspected after rendering.
- Lean: detailed uncompiled blueprint. No claim is made that the analytic theorem collection is kernel checked.
- Floating-point diagnostics: optional and informational only; they are not proof oracles.

See `STATUS.md` for the precise audit statement.

## Reproduce

From the archive root:

```sh
./build.sh
```

This reruns the exact certificates and compiles the PDF. The Python program uses only the standard library for proof-relevant work; if `mpmath` is installed, it adds non-authoritative regression diagnostics.

Run the certificate generator alone with:

```sh
python3 code/gaussian_certificates.py \
  --output evidence/validation.json \
  --summary evidence/validation.txt
```

## Repository baseline

The source audit used ProveIt commit

```text
8f028dcb4be7a7397d0c11d7c467aa1170cbf2f3
```

and the ordinary iPRA interfaces `PR`, `PTm`, `PRAAx`, `Prf`, `PRA.qfInd`, together with the bridge `pra_iff_native`. Details are recorded in `provenance/SOURCES.md`.
