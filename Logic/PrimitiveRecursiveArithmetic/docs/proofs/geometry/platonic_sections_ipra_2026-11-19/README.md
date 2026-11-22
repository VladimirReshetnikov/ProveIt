# Largest planar sections of the five Platonic solids

This packet gives the exact maximizing plane, polygon, and area for every
Platonic solid, with a complete human-readable constructive argument,
exact finite certificates, and a Lean formalization outline.

For edge length `a`, the maximum areas are:

| Solid | Attaining polygon | Maximum area |
|---|---|---|
| Tetrahedron | An equilateral face | `sqrt(3) a^2 / 4` |
| Cube | Rectangle with sides `a` and `sqrt(2) a` | `sqrt(2) a^2` |
| Octahedron | Equatorial square | `a^2` |
| Icosahedron | Nonregular centrally symmetric hexagon | `(2 + sqrt(5)) a^2 / 2` |
| Dodecahedron | Regular decagon, side `phi a / 2` | `5 sqrt(130 + 58 sqrt(5)) a^2 / 16` |

Here `phi = (1 + sqrt(5))/2`. A section includes supporting planes.
If only planes meeting the interior are allowed, the tetrahedral value
is an unattained supremum. The other four maxima are attained by
interior-cutting planes.

## Read the report

- `platonic_sections.pdf` is the complete report, including all five proofs,
  finite arithmetic interpretation, general-real input bridge, Lean plan,
  and all 283 nonzero coefficients of the two larger-solid certificates.
- `platonic_sections.tex` is the main LaTeX source. It includes the other
  root-level `.tex` files, all of which are supplied.
- `figures/maximal_sections.pdf` and `.png` show the exact attaining polygons.

## Verify the arithmetic

From this directory:

```bash
python3 code/exact_sections.py
python3 code/verify_central_reduction.py
python3 certificates/icosahedron/verify_icosahedron.py
python3 certificates/dodecahedron/verify_dodecahedron.py
python3 code/verify_small_solids.py
```

The first four use only Python's standard library. The last uses SymPy
to audit the explicitly displayed small-solid identities. Run all of them
and refresh `verification.log` with:

```bash
python3 code/run_all.py
```

The icosahedral and dodecahedral scripts independently verify their
supporting facets, reflection symmetries, cone cases, section formulas,
denominator boundary cases, and coefficient identities. They do not use
floating point or an optimization package. The independent witness code
computes the five exact sections by clipping and a convex-hull scan, then
uses the three-dimensional vector shoelace formula. Its minimum-distance
edge identification is specific to these five regular coordinate models;
it is not advertised as a generic algorithm for arbitrary polytopes.

The central-section reference construction checks twelve exact examples,
including supporting and degenerate slices. The universal mathematical
proof is the reflected-fiber/trapezoid argument in the report; those twelve
examples are supplementary checks, not a replacement for the proof.

## Rebuild the diagrams and PDF

The executed environment used Python 3, SymPy 1.14.0, Matplotlib 3.10.8,
and NumPy. The drawing code uses floating point only to render coordinates.
For the diagrams and optional symbolic audit, install `requirements.txt`.
Then run:

```bash
python3 code/make_figures.py
latexmk -pdf -interaction=nonstopmode -halt-on-error platonic_sections.tex
```

The report uses common TeX Live packages (amsmath, lmodern, microtype,
booktabs, longtable, graphicx, pdflscape, listings, and hyperref).

## Formalization status

The human proof gives a finitary iPRA construction. All exact arithmetic
verification scripts were executed successfully. **The Lean outline has
not been compiled, and the main theorem has not been supplied as a
kernel-checked `Prf PRAAx` term.**

- `lean/FiniteGeometry.lean`: concrete finite-data definitions and selected
  ring identities, plus the geometry implementation order.
- `lean/IPRAEndpoints.lean`: inspected ProveIt interface, small
  object-language identity proofs, and the defined target for the full
  arithmetic theorem. It deliberately does not assert the unfinished
  main theorem using an axiom or an admitted proof.
- `repo_provenance.json`: inspected repository snapshot and exact source
  blob identifiers. The repository's full transitive dependencies are not
  copied into this standalone outline packet.

The internal theorem quantifies over natural-number codes of planes in
`Q(phi)` and compares exact squared areas. The report then gives an
explicit contraction/plane-approximation argument for ordinary real
planes, and explains the finite precision schema for supplied primitive
recursive real names. It does not identify arbitrary reals with natural
number codes or assume decidable signs for arbitrary Cauchy reals.
The constructive area bound is interpreted through finite inscribed
polygon data, or a supplied area name with its geometric contract; it
does not uniformly compute section area from plane names at supporting
planes.

## Provenance

The resulting optima agree with Brandenburg, De Loera, and Meroni,
*The best ways to slice a polytope*, Mathematics of Computation 94 (2025),
1003–1042, DOI 10.1090/mcom/4006. The report supplies the explicit
arithmetic proofs and certificates used here; the optimizer mentioned in
that paper is not a premise of these checks.

Prepared 19 November 2026.
