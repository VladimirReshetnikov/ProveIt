# Centered residue certificates and reusable Pell denominators

Research contribution for Vladimir Reshetnikov and ProveIt, 25 October 2026.
Developed with AI assistance. Start with **report.pdf** or its editable source
**report.tex**. This directory is self-contained for offline algebra checks.

## Main result

The principal direct equation is the explicitly emitted integer quartic

\[
P(x_0,\ldots,x_{257})=\sum_{j=0}^{185}R_j(x_0,\ldots,x_{257})^2=0,
\qquad x_i\in\mathbb Z.
\]

All 186 quadratic residuals are printed in the report and supplied literally
in `arithmetic/signed258/equation.json`. All **5,366 collected coefficients**
are in `arithmetic/signed258/expanded_polynomial.json`. The maximum absolute
coefficient is **128,446**, below 2^17. With the retained numerical-calculus
calibration, the ordinary mathematical proof gives

\[
\mathrm{ZFC}\vdash
\bigl[\neg\exists\mathbf x\in\mathbb Z^{258}\;P(\mathbf x)=0\bigr]
\longleftrightarrow\operatorname{Con}(\mathrm{ZFC}).
\]

This route uses the repository's finite C222 proof calculus directly. It
does not use a K215 simulation, Jones's universal equation, or a large
machine-coefficient tuple. The result improves the inspected incoming
282-integer direct parent by **24 variables, six residuals, and 125
monomials**, preserving degree and coefficient height.

A second branch gives ten-positive-variable equations with exact
operation/degree pairs **75/626**, **76/464**, and **77/460**. Their complete
formulas, all four fixed coefficient payloads, and a finite reconstruction
from the printed 436-character seed are included. This branch retains the
coherent radix-67 indexed native tuple; it makes a new arithmetic reduction,
not a new logical encoding.

## Exact selected equations

Here `N` includes zero. Compact witnesses are strictly positive. Domains
are part of the theorem and must not be interchanged silently.

| Data directory or circuit | Domain | Variables | Degree | Residuals or binary operations | Monomials | Height |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `arithmetic/signed258` | Z | 258 | 4 | 186 rows | 5,366 | 128,446 |
| `arithmetic/signed259` | Z | 259 | 4 | 185 rows | 5,361 | 128,446 |
| `arithmetic/natural222` | N | 222 | 4 | 172 rows | 9,522 | 83,954,186 |
| `arithmetic/natural221_high` | N | 221 | 4 | 171 rows | 10,216 | 2,445,412,949,744 |
| `arithmetic/natural223_sparse` | N | 223 | 4 | 173 rows | 6,858 | 83,953,724 |
| `compact/equation_XY_V2.json` | positive integers | 10 | 626 | 75 operations | not expanded | fixed tuple |
| `compact/equation_XY_bV.json` | positive integers | 10 | 464 | 76 operations | not expanded | fixed tuple |
| `compact/equation_q4_bV.json` | positive integers | 10 | 460 | 77 operations | not expanded | fixed tuple |

`arithmetic/audit261` preserves the first isolated radius reduction.
`compact/equation_q4_V2.json` preserves the simpler square-transport
alternative (76 operations, degree 622). These are useful proof checkpoints.

The operation count uses binary addition, subtraction, and multiplication;
squaring costs one multiplication, and an already computed intermediate
is reused without a second arithmetic charge. All circuit gates are live.
The quartet of very large constants consists of fixed integers, not extra
unknowns and not uncomputed coefficient ports.

## New mathematical mechanisms

### 1. Small canonical residues replace separate signed interval guards

The power certificate already implies, before factorial semantics,

\[
0\le r_i^0<D/15,\qquad r_i\equiv r_i^0\pmod D.
\]

For at most 56 residues, one quadratic row

\[
D^2=4\sum_i r_i^2+1+a^2+b^2+c(c+1)
\]

forces every `r_i` to be its canonical residue: the row gives
`|r_i| < D/2`. Conversely its gap is nonnegative at the canonical residues
and is representable as `a^2+b^2+c(c+1)`. The actual principal equation
uses groups of sizes seven, two, and two. Two product coordinates merge
the groups at `q^t` and `q^(t+1)` without increasing the final degree.

### 2. A compatible odd-square radix

The old radix output slack and its three sign witnesses can be replaced
by `q=(2z+1)^2`. Soundness first recovers the positive base `B`, then
`N=B^x`, then the representative indices at base `q+1`, and only then
`q=(BH_0)^x`. Thus it never assumes `q>1` to justify the power that proves
it. Completeness uses odd CRT periods to choose even `x` and odd `H_0`
while retaining the required even semantic anchor.

### 3. Recover a small modulus before recovering the full denominator

In the compact certificate, an admissible denominator `D` need only satisfy

\[
q^4\mid D,\qquad D\mid4XY^2,
\qquad X=wq,\quad Y=q^3s.
\]

One first recovers divisibility by `q^4`; the signed Pell argument then
identifies the exact main index and recovers full divisibility by `D`.
Both `D=XY` and `D=q^4` work. Reusing `XY` and removing the transport shift
give the new 75-operation equation. The report supplies all signed-branch
proofs, including the product-transport small-index exclusion.

## What the proof and checks establish

The report and new component proofs give ordinary unbounded mathematical
arguments formalizable in ZFC. They compose with the explicitly identified
inherited C222/ZF/ZFC and native calibration theorems. The required ordinary
source dependencies, source ledgers, interface Lean files, and licenses
are retained. Their transitive Lean development was not rebuilt here.

The finite checkers independently verify literal source changes, private
coordinate deletions, every monic restoration, integer translations,
nonnegative restoration certificates, and every quartic coefficient. For
the compact equations they check exact polynomial cut identities covering
every gate and their complete highest homogeneous parts. Modular scalar
comparisons are explicitly regression checks, not proofs of Pell lemmas.

The release is not a new end-to-end Lean/Rocq formalization and does not
prove either consistency or inconsistency. It proves the requested
equivalence through the named inherited calibration. Separate AI review
and independent code implementations were used; this is not a claim of
external human peer review.

There is no global minimality or literature-wide novelty claim. The audit
snapshot already contains nine-positive-variable equations, a
15-positive-variable circuit with fewer operations, and quartics with
fewer variables but a different coefficient architecture. The new direct
result improves the small-coefficient numerical-calculus family; the new
compact result improves its matched ten-positive-variable parents.

## Offline reproduction

Python 3.10 or later with only its standard library is sufficient:

```sh
python3 -B verify_all.py
```

This authenticates the release, runs normal and optimized checks, rebuilds
all six arithmetic profiles in temporary directories, reconstructs the
four compact circuits and all four coefficient integers, verifies the
independent signed and compact audits, and checks that the printed
residual appendices agree with their literal data. The delivered tree is
unchanged. To save a new receipt outside the sealed directory:

```sh
python3 -B verify_all.py --receipt ../new_verification.json
```

For a fast file-integrity check alone:

```sh
python3 -B verify_all.py --manifest-only
```

Individual entry points are described in `arithmetic/README.md` and
`compact/README.md`. Actual receipts are retained in `verification/`
and the components. Arithmetic rebuilds compare 42 generated JSON files
byte for byte; deliberate corrupted examples must be rejected.

To rebuild the PDF, use a working copy of this directory:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

Three passes settle the contents, citations, and table widths. A normal
LaTeX installation with the packages named in `report.tex` is sufficient.
Generated TeX logs and a freshly compiled PDF will naturally differ from
the sealed distribution's file census or metadata. To regenerate only the
data-derived TeX appendices after intentional equation edits, run
`python3 render_report_inputs.py` and then the algebra verifiers.

## Provenance and integration

The comparison is pinned to ProveIt commit
`e0c98c629bf10d30b695884f6b1d2ab361bdf513` and all six archives then present
in `docs/incoming`. `PROVENANCE.json` records their hashes and the new
equation identities. Component ledgers identify retained earlier source
commits, which are not being presented as the comparison snapshot.

The ZIP has one top-level directory and can be placed in `docs/incoming`
for review. It includes editable TeX, the compiled PDF, literal JSON,
coefficient payloads, standard-library Python, mathematical review notes,
source dependencies, licenses, and checksums. No remote repository state
was changed by preparing this package.

New material uses the root `LICENSE`; retained sources keep their own
notices and licenses. See `NOTICE.md` and the component notices.
