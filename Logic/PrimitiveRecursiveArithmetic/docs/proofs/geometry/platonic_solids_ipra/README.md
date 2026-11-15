# Exactly five Platonic solids in intuitionistic primitive recursive arithmetic

This package proves a finite constructive classification: exactly five
similarity classes of convex polyhedra with congruent regular polygonal
facets and constant vertex valence. The internal arithmetic inputs have
finite exact constructible-coordinate codes (rational arithmetic and
nonnegative square roots), with decidable order and equality.

The five representatives already lie in Q(sqrt(5)). Their vertex/edge/face
counts are respectively (4,6,4), (8,12,6), (6,12,8), (20,30,12), and
(12,30,20).

## Read first

- `paper/platonic_solids_ipra.pdf`: complete human-readable argument.
- `paper/platonic_solids_ipra.tex` and `paper/sections/*.tex`: full LaTeX source.
- `lean/FORMALIZATION.md`: dependency-ordered formalization plan and exact
  ProveIt interfaces.
- `verification/status.json`: machine-readable verification status.

## What the proof includes

1. Exact radical-tower arithmetic, including redundant extensions and
   explicit primitive recursive size bounds.
2. A finite lower-neighbor proof of Euler's identity.
3. The subtraction-free arithmetic identity
   `E*(p-2)*(q-2) + 2*p*q = 4*E`, leaving five cases.
4. Complete combinatorial uniqueness, including a short twelve-vertex
   reconstruction of the icosahedron.
5. Finite Cauchy rigidity, with algebraic quadratic-event selection in
   the corrected spherical arm argument and a rotation-permutation
   proof of the sign-count lemma.
6. Exact constructions of all five models, with complete supporting-facet
   classifications and regularity/valence proofs.
7. A primitive recursive similarity-witness construction and a precise
   account of quantifier-free induction.

The usual local definition is retained. Full flag symmetry is verified
for the examples, but it is not assumed in the classification input.
The internal theorem is not a claim to decide comparisons between
arbitrary computable real-number names. The ordinary arbitrary-real
classification is an external interpretation of the geometric proof.

## Verification status

The exact Python verification was executed successfully for all five
models. Regenerating the certificate reproduced its bytes exactly.
The PDF was compiled from the supplied LaTeX and visually reviewed.

**The Lean source is uncompiled.** Lean, Lake, and Elan were not available
in the production environment. The two source files contain no proof
holes or new axioms, but they must not be described as kernel checked.
`Arithmetic.lean` is an ambient arithmetic prototype conditional on the
incidence equations and Euler identity. It does not formalize geometry.
`ConciseBridge.lean` transports an already constructed embedded iPRA
derivation; its derivation premise is explicitly an assumption.
The full `Prf PRAAx [] classificationFormula` derivation remains to be
implemented along the included plan.

## Reproduce the exact finite certificates

Python 3.10 or later and the standard library suffice:

```sh
python3 code/exact_models.py --output certificates/certificates.json
```

Run Python normally, without `-O`, since the verifier uses assertions.
The program uses exact `Fraction` pairs `a+b*phi`, `phi^2=phi+1`.
It checks all supporting triples, all ordered facet boundaries,
regularity and face congruence, edge incidences, cyclic vertex links,
Euler/incidence counts, and exact orthogonal symmetries and flag orbits.
It is a finite-model generator/verifier, **not** a general input classifier
and **not** an iPRA proof checker.

The JSON schema stores vertices, faces, support planes, edges,
vertex-face incidences, metric data, and symmetry matrices. A scalar
`["a","b"]` means `a+b*phi`, where the strings are exact rationals.

## Regenerate the figure and compile the article

The existing vector figure is included, so rebuilding the article does
not require Python graphics libraries. With a normal TeX Live installation:

```sh
latexmk -cd -pdf -interaction=nonstopmode -halt-on-error paper/platonic_solids_ipra.tex
```

To redraw the figure, install the optional plotting dependencies in
`code/requirements-figure.txt` and run:

```sh
python3 code/draw_models.py
```

Only the renderer uses floating point; none of the proof checks does.

## Build the Lean arithmetic prototype

The target is the toolchain declared in the inspected ProveIt snapshot:
Lean 4.32.0 and Mathlib v4.32.0.

```sh
cd lean
lake update
lake exe cache get
lake build Arithmetic
```

Retain the `#print axioms` output. Fix any build issues before treating
the source as checked. `ConciseBridge.lean` is an integration adapter for
a ProveIt checkout with the existing `ConciseIPRA` library available;
it is not part of the standalone arithmetic target.

## Repository provenance

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit: `2811f73af20330d04bf3dae8428f87f7efa6580d`

The inspected framework supplies `PR`, `PTm`, `PRAAx`, `Prf`,
`PRA.qfInd`, `NFm.ofPRA`, and `pra_iff_native`.
The `docs/drafts` directory was listed, but no binary draft is assumed
as a verified mathematical dependency. No repository files were changed
or published by this task.

The article gives primary references for the corrected arm induction,
the classical rigidity method, and the repository framework.

## Package layout

```text
paper/          Compiled article, LaTeX sources, and exact-model illustration
code/           Exact Python verifier and optional figure renderer
certificates/   Complete exact model data
lean/           Uncompiled prototype, integration adapter, and proof plan
verification/   Execution log, build/inspection status, and provenance
SHA256SUMS      Checksums of all other distributed files
```
