# Stable observables from finite witnesses

Prepared for Vladimir Reshetnikov, 15 November 2026.

This package develops a general finite-certificate comparison interface for
embedding mathematical constructions into intuitionistic primitive recursive
arithmetic (iPRA). Its substantive application is a rational spectral theory
uniform in matrix dimension: approximate orthogonal diagonalization, stable
ordered eigenvalue names with multiplicities, principal positive square roots,
and gap-dependent spectral projectors.

Start with **paper/ipra_stable_observables.pdf**. Its complete LaTeX source is
**paper/ipra_stable_observables.tex** and **paper/sections/**.

## Mathematical results

- Exact rational Jacobi rotations with explicit primitive recursive fuel.
- An optional finite-grid version controlling rotation denominators.
- A comparison theorem for any two valid diagonalization certificates:
  `max |d_i-e_i| <= input_error + residual_1 + residual_2`.
- Coherent ordered spectral names through eigenvalue collisions, retaining
  repetitions without choosing coherent eigenvectors or exact matching indices.
- A finite rational positivity alternative: nonnegative LDL certificate or
  negative quadratic-form witness.
- Positive square-root certificates, a mixed-basis stability estimate,
  correction for slightly indefinite rational samples, and a finite uniqueness
  argument establishing the principal root.
- Spectral projector comparison under a certified gap, with explicit precision
  conversion and stable block counts.
- A metatheoretic impossibility theorem for sound, complete effective numerical
  bound certificates for arbitrary primitive recursive singleton fibers.

The abstract observation rule refines earlier ProveIt frameworks. No priority
claim is made for classical spectral mathematics. The new comparison is a
subclass resolution for real symmetric spectra; general complex root matching
and the difficult global arithmetic theorems remain outside these results.

## Verification status

The mathematical arguments are fully developed human arithmetic proofs with
finite data, explicit error budgets, and quantifier-free induction invariants.
The matrix-specific embedded Lean derivations are **not complete**.

- `lean/ObjectObservation.lean`: five compiled combinators returning the
  actual `Prf PRAAx` type. Their audit reports `propext` and `Quot.sound`,
  without `sorryAx` or `Classical.choice`.
- `lean/SpectralBlueprint.lean`: compiled finite definitions, the Jacobi
  algorithm, certificate predicates, and explicitly **unproved target
  propositions**. Its `UnprovedMatrixObligations` structure has no instance.
  Host rational definitions additionally inherit `Classical.choice` from Std;
  they are not object-iPRA proofs.
- `code/`: exact rational reference producers and independent certificate
  checks. They are not a proof checker for iPRA.
- `verification/` and `lean/validation/`: reproducible finite check results,
  build records, and axiom audits. Finite testing does not replace the proofs.

## Reproduce

Python needs only the standard library:

```sh
python3 code/verify_spectral.py
python3 code/verify_observables.py
```

Build the PDF using a TeX distribution with the packages listed in its preamble:

```sh
cd paper
pdflatex -interaction=nonstopmode -halt-on-error ipra_stable_observables.tex
pdflatex -interaction=nonstopmode -halt-on-error ipra_stable_observables.tex
```

The Lean subproject is pinned to Lean 4.32.0 and Mathlib commit
`81a5d257c8e410db227a6665ed08f64fea08e997`:

```sh
cd lean
bash build.sh
```

It includes three unchanged ConciseIPRA source modules and their upstream
license. Network access is needed to obtain pinned Lean/Mathlib dependencies;
toolchain and dependency binaries are not included.

## Source baseline and integration

The audited ProveIt revision is
`c39c388d4f87220ab9e758ae457520bbc0d74341`.
`provenance/source_manifest.json` records inspected repository source paths and
content hashes. The paper cites the exact sources and distinguishes their
reported status from independent verification.

The package can be filed as a new foundations proof packet under
`Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/`.
For Lean integration retain the new modules and resolve the existing
`ConciseIPRA` imports from the repository instead of duplicating its modules.
No remote repository mutation is part of this delivery.

`MANIFEST.sha256` records the delivered archive members, excluding itself.
