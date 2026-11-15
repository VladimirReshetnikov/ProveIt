# Pell equations in intuitionistic primitive recursive arithmetic

Prepared for Vladimir Reshetnikov, November 15, 2026.

The main deliverable is `pell_ipra.pdf`; its complete LaTeX source is
`pell_ipra.tex`. The article gives self-contained human-readable proofs and
an explicit audit showing how the algorithms and induction invariants fit
first-order intuitionistic primitive recursive arithmetic (iPRA).

## Results

For every nonsquare integer D >= 2, including nonsquare D that are not
squarefree, the development proves:

- Two bounded existence constructions: finite norm collisions and finite
  continued fractions.
- A continued-fraction period at most S = 2a(a+1), where a = isqrt(D).
- The fundamental positive solution within 2S convergents and coordinate
  bound (2a+1)^(2S).
- A finite proof of Legendre's approximation criterion, giving both
  fundamental minimality and the full odd-period criterion for negative Pell.
- Complete generation by powers of the fundamental unit, with an explicit
  fixed-fuel descent that computes the exponent.
- Negative Pell decision and classification; when a negative unit exists,
  its square is the fundamental positive unit.
- Uniform primitive recursive decision of x^2 - D*y^2 = N. For N != 0,
  if (A,B) is the fundamental unit, a complete seed box is
  0 <= y <= A*abs(N), 0 <= x <= (D*A+1)*abs(N).
- Strong divisibility of Pell y-coordinates, a residue return within h^2
  steps modulo h, and rational square-root enclosures with an explicit
  primitive recursive precision modulus.

The article proves the finite mathematical lemmas directly. It does not
assume real completeness, infinite pigeonhole, unbounded minimization,
choice, Markov's principle, or induction on arbitrary quantified formulas.

## Files

- `pell_ipra.tex`, `pell_ipra.pdf`: article source and compiled article.
- `build.py`: reproducible PDF build using pdflatex.
- `code/pell_reference.py`: exact finite reference algorithms.
- `code/test_pell.py`: deterministic validation suite.
- `code/test-results.json`: results from the actual successful test run.
- `code/cf-certificates.json`: seven worked exact continued-fraction traces.
- `code/export_certificates.py`: regenerates those traces.
- `code/README.md`: algorithm usage and validation scope.
- `lean/PellCore.lean`: an algebraic Lean starting point and solver specs.
- `lean/Transfer.lean`: the exact existing iPRA-to-native transfer API.
- `lean/ROADMAP.md`: pinned foundation files, object-theory proof target,
  module plan, and quantifier-free induction obligations.
- `lean/lakefile.toml`, `lean/lean-toolchain`: standalone core project setup.
- `evidence/provenance.json`: source revision, URLs, and source blob hashes.
- `evidence/validation.json`: delivered validation and formalization status.
- `MANIFEST.sha256`: checksums of delivered files, excluding the manifest itself.

## Verification status

The Python suite passes all 12 test methods. It checks every nonsquare
discriminant from 2 to 500 (478 cases), 7,758 convergent norm identities,
independent bounded minimality on 116 cases, and the other arithmetic
constructions on the ranges recorded in `test-results.json`.

The Python checks and JSON traces are not formal iPRA proof certificates.
The universal results are established by the article's mathematical proofs.

The Lean files were **not compiled**: the delivery environment has no Lean
or Lake executable. The short source proofs contain no admitted theorem
placeholders or added axioms, but are supplied as an unverified starting
point. A completed embedded iPRA derivation and native checker certificate
are not included. The roadmap identifies those remaining obligations,
including the distinction between an ordinary Lean theorem about integers
and a proof in the repository's object theory `PRAAx`.

## Reproduce

From the archive root, rebuild the PDF with:

```sh
python3 build.py
```

From `code/`, run:

```sh
python3 test_pell.py
python3 pell_reference.py
python3 export_certificates.py
```

The Python code requires only the standard library. The PDF requires
pdflatex with standard TeX Live packages. With the pinned Lean toolchain
and Mathlib available, run from `lean/`:

```sh
lake update
lake exe cache get
lake env lean PellCore.lean
```

Check `Transfer.lean` inside the pinned ProveIt ConciseIPRA project.

## ProveIt provenance

Inspected repository revision:

`f1b0582aada7262b10924ea1ba12e2e490d2934b`

Repository: https://github.com/VladimirReshetnikov/ProveIt

The foundational sources are under
`Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/`.
No remote repository changes are part of this deliverable.

