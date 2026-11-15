# The sharp planar isoperimetric inequality in iPRA

Prepared for Vladimir Reshetnikov, 14 November 2026.

## Main deliverable

Read **isoperimetric_ipra.pdf** for the full human argument.
Its complete LaTeX source is **isoperimetric_ipra.tex**.

The scope is the classical planar inequality L² ≥ 4πA, its sharp
constant, and the equality characterization for the effective geometric
presentations specified in the report. Higher-dimensional and
non-Euclidean generalizations are not claimed.

The arithmetic core is a single uniform statement about finite rational
polygon codes:

    4 * piLower(k) * abs(signedArea(P)) <= S^2 + 2^(-k).

Here each nonnegative rational upper length u[i] satisfies
normSquared(edge[i]) <= u[i]^2, and S is their sum.
The rational piLower(k) is explicitly computed and is within 2^(-k)
of pi from below.

## Proof architecture

1. Construct dyadic roots of unity using positive quadratic radicals.
2. Prove the radical sign and order laws by explicit positive-cone
   certificates, including redundant quadratic extensions.
3. Derive the exact finite Fourier identity for area and edge energy.
4. Refine a rational polygon by an explicitly bounded allocation of
   subdivisions, padding to a power-of-two number of vertices.
5. Convert the resulting energy bound into the finite rational theorem.
6. Use explicit area and length error estimates for represented limits.
7. Prove rigidity using a finite weighted Fourier estimate and extract
   the limiting circle from coordinate extrema.

No compactness, infinite Fourier series, choice of a maximizing shape,
or general extraction of an arclength parametrization is used.

## Representation conditions

The first-order theorem concerns finite numerical codes. Curve statements
are schemas for fixed primitive recursive sampling families and supplied
moduli, not quantification over arbitrary real sets.

For a Jordan domain, ordinary enclosed area requires a compatible
polygonal-domain presentation or a separately verified representation
bridge. A numerical limit of polygonal perimeters must be certified to
equal the actual boundary perimeter before using the geometric equality
converse: Hausdorff convergence alone permits excess corrugation length.

The report also gives a lower-real perimeter formulation, which avoids
assuming a computable length. Rationalized samples are corrected back to
certified lower bounds on genuinely inscribed polygon lengths.

## Formalization status

The **human proof is supplied**. The **complete internal Lean derivation
is not yet supplied**.

The three Lean files are marked **uncompiled blueprint**. They specify
the finite rational data, exact piLower algorithm, numerical codecs,
checker, and first-order formula. Their actual completion target is

    Prf PRAAx [] (finiteFormula checkCode)

where checkCode must be the verified compilation of the specified
checker. No inhabitant of that target is claimed. The only theorem in
the integration file transfers an already supplied internal derivation
to the concise native calculus.

No Lean or Lake compiler was available in the execution environment.
The files add no axioms and contain no proof placeholders, but that does
not make the main theorem formally proved. See **lean/README.md** for
the precise implementation sequence and missing proof obligations.

The inspected ProveIt snapshot is:

    329161f8da0b319d51ba9f6246c4b19d243f7193

Its configuration specifies Lean 4.32.0 and Mathlib revision:

    81a5d257c8e410db227a6665ed08f64fea08e997

Repository observations and pinned source links are recorded in
**PROVEIT_INTEGRATION.md**. No repository changes or external publication
are part of this archive.

## Contents

| File or directory | Purpose |
|---|---|
| isoperimetric_ipra.tex | Complete human proof and formalization plan |
| isoperimetric_ipra.pdf | Compiled, visually checked report |
| build.sh | Standard LaTeX rebuild command |
| code/finite_core.py | Exact rational executable specifications |
| code/verify.py | Reproducible rational checks |
| code/dyadic_spectral_check.py | Exact positive-radical DFT diagnostics |
| lean/IsoperimetricIPRA/ | Concrete definitions and internal proof target |
| lean/README.md | Detailed path to a full internal formalization |
| verification/exact_checks.json | Rational diagnostic results |
| verification/dyadic_spectral_checks.json | Exact radical diagnostic results |
| verification/document_checks.json | PDF and source validation summary |
| PROVEIT_INTEGRATION.md | Repository inspection and pinned references |
| MANIFEST.sha256 | SHA-256 hashes of packaged files |

## Reproduce

From this directory:

    python3 code/verify.py
    python3 code/dyadic_spectral_check.py
    sh build.sh

The Python scripts use only the standard library. The LaTeX build needs
a functioning pdfLaTeX installation and the packages listed in the
preamble. The supplied PDF makes rebuilding optional.

The exact checks passed for 25 pi enclosures, 2,160 square-root cases,
845 polygon instances, and six fully expanded refinements. Four exact
radical examples with 4, 4, 8, and 16 vertices verify the Fourier
identities and all required signs. These are finite diagnostics,
not a machine-checked universal theorem.

