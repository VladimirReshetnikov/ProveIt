# A quantitative Jordan curve theorem in iPRA

**Prepared for Vladimir Reshetnikov — 15 November 2026**

The main deliverable is `jordan_ipra.pdf`, with its complete LaTeX source in
`jordan_ipra.tex` and `sections/`.

## Result

The paper gives a complete human-readable constructive argument for continuous
circle embeddings presented by:

- primitive recursive rational approximation routines;
- a primitive recursive forward continuity modulus;
- a primitive recursive positive inverse separation modulus.

For points with a supplied positive clearance from the curve, it constructs a
stable inside/outside bit. Equal bits yield a polygonal route and an explicit
positive clearance. Both bits are constructed arbitrarily near every curve
point. The bit-one region is inhabited and bounded; the bit-zero region is
inhabited and unbounded. A continuous path with differently labelled endpoints
has boundedly computed approximate intersections with the curve at every
requested precision.

The common-boundary statement uses rational witnesses of both bits in every
neighborhood. In the converse direction, finite nearest-sample selections and
the inverse modulus construct a primitive recursive circle name for a preimage.

The proof is not restricted to polygons, smooth curves, or rectifiable curves.
It does not assume a supplied Schoenflies homeomorphism.

## Precise logical scope

The iPRA result is an **arithmetic theorem schema for each fixed primitive
recursive presentation**, conditional on its explicit arithmetic regularity
premises. Real points are represented by fixed fast names; finite rational
points and certificates are number-coded.

This is not a first-order quantification over all real functions, and it does
not assume a primitive recursive universal evaluator for arbitrary primitive
recursive program codes.

The complement used is the **apartness complement**: points with a positive
distance witness. The two components are characterized by polygonal routes with
certified positive clearance. Approximate contact is proved for every crossing
path; an exact intersection parameter is not silently asserted.

## Main proof mechanism

Only crossing parity, a value in the two-element field, is needed.

1. Define parity by rational horizontal-ray comparisons with a half-open
   vertex convention.
2. Prove triangle replacement and query-path invariance by finite cancellation.
3. Show that a sufficiently short polygon near the curve has parity equal to
   a fixed bit times the curve's parity. The proof is edge-usage conservation
   on the finite parameter cycle.
4. Flood a finite rational honeycomb through links with certified clearance.
   A failed route produces a separating cycle. A local parallelogram detour
   proves that cycle changes parity between the endpoint regions. Factorization
   therefore makes failure impossible for equal curve bits.
5. Color a small rational square according to which parameter half-arc each
   segment avoids. A finite chain identity forces transition vertices of both
   curve bits.

The continuous routing and local-boundary strategy originates in Berg, Julian,
Mines, and Richman (1975). This package supplies a parity-only arithmetic
reconstruction with rational geometry, explicit scales, and an iPRA induction
audit.

## Contents

| Path | Purpose |
| --- | --- |
| `jordan_ipra.pdf` | Complete mathematical paper |
| `jordan_ipra.tex`, `sections/*.tex` | Complete LaTeX source |
| `artifacts/jordan_kernel.py` | Exact rational finite reference implementation |
| `artifacts/test_kernel.py` | Reproducible finite checks |
| `artifacts/test_results.json` | Recorded exact results |
| `artifacts/make_figures.py` | Reproduce the mathematical illustration |
| `artifacts/build_pdf.sh` | Compile the paper, with a private-format fallback for minimal TeX installations |
| `artifacts/README.md` | Code-specific scope and instructions |
| `figures/finite_routes.pdf` | Vector figure used by the paper |
| `figures/finite_routes.png` | Raster preview of the same figure |
| `lean/FiniteKernel.lean` | Uncompiled executable-definition scaffold |
| `lean/NativeTransfer.lean` | Uncompiled generic wrapper for the existing native translation |
| `lean/ROADMAP.md` | Dependency order, precise proof obligations, and completion gates |
| `sources.json` | Source URLs, pinned repository information, and inspected file hashes |
| `validation_summary.json` | Recorded scope and results of the delivery checks |
| `SHA256SUMS` | Integrity hashes for the package files |

## Validation and limitations

The exact rational Python run passed **142 checks**. They include ray
degeneracies, triangle replacement, all six honeycomb neighbor identities,
bounded flood fill, route clearances, separating-cycle extraction, and cyclic
factorization.

Recorded examples:

| Example | Result | Segments | Maximum-norm clearance |
| --- | --- | ---: | ---: |
| Square, inside to inside | Route | 3 | 11/8 |
| Square, inside to outside | Different bits, no safe route | — | — |
| Concave U, arm to arm | Route | 24 | 1/8 |
| Concave U, notch to far exterior | Route | 25 | 3/16 |

An annular coloring produces two boundary cycles of 54 and 18 edges. The
algorithm does not assume the whole finite boundary is one cycle.

These are executable checks of the finite reference kernel, **not a formal
verification of the general theorem**. The reference tests use polygons as
distance oracles; the paper proves the finite-net replacement for general
named curves.

Lean was not installed in the delivery environment. The two `.lean` files are
explicitly **uncompiled scaffolds**. They contain no added axiom declaration
and no `sorry` proof, but they do not supply a completed Jordan proof. The
roadmap distinguishes semantic Lean correctness from construction of actual
first-order `Prf PRAAx` derivations.

## Reproduce

From this directory:

```sh
python3 artifacts/test_kernel.py
python3 artifacts/make_figures.py
latexmk -pdf -interaction=nonstopmode -halt-on-error jordan_ipra.tex
```

The tests need only the Python standard library. Figure generation also needs
Matplotlib. PDF compilation needs a conventional LaTeX installation with the
packages declared in the main source.

Alternatively, run `bash artifacts/build_pdf.sh`. The helper uses `latexmk` on
a fully initialized TeX installation and can create a private format and font
map when an installation has the packages and engines but lacks those generated
files. Set `JORDAN_TEX_RUNTIME` to choose the private runtime directory.

The generated PDF was rendered and visually checked before packaging.

## ProveIt integration

The inspected repository commit is:

`620f5e3b959c3a4284060ada5efb651812612319`

The existing toolchain is Lean `v4.32.0`, with Mathlib `v4.32.0`. Relevant existing
interfaces are `PR`, `PTm`, `PRAAx`, `PRA.qfInd`, `Prf`, `NFm.ofPRA`, and
`pra_iff_native`. The native translation is applied only after an actual
arithmetic derivation is constructed.

No files were committed to or changed in the remote repository.

## References

- G. Berg, W. Julian, R. Mines, and F. Richman, *The constructive Jordan curve
  theorem*, Rocky Mountain Journal of Mathematics 5 (1975), 225–236.
  <https://doi.org/10.1216/RMJ-1975-5-2-225>
- P. Nguyen and S. Cook, *The Complexity of Proving the Discrete Jordan Curve
  Theorem*. <https://arxiv.org/abs/1002.2954>
- D. S. Bridges, *On the Constructive Theory of Jordan Curves*.
  <https://arxiv.org/abs/2502.09784>
- ProveIt, ConciseIPRA:
  <https://github.com/VladimirReshetnikov/ProveIt/tree/620f5e3b959c3a4284060ada5efb651812612319/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA>
