# Smaller explicit Diophantine equations for ZFC consistency

Prepared for Vladimir Reshetnikov and the ProveIt project, 23 October 2026.

**Main result:** an explicit polynomial in nine positive integers with exact
degree **15,534,796** and **655 live binary arithmetic operations**, and a
polynomial in ten unrestricted integers with exact degree **39,914,856**
and **651 operations**. Each has no solutions exactly when ZFC is
syntactically consistent, by the ordinary mathematical proof and the
inherited compiler/calibration theorems identified in the report.

Start with **report.pdf** (18 pages) and its complete LaTeX source
**report.tex**. All adjacent TeX inputs are required for compilation.

## Comparison against the reviewed repository

Reviewed commit: `124c07c0b77a9e20e84676514d8b1ff78536ea3f`.

| Construction | Domain | Exact degree | Primary operations |
| --- | --- | ---: | ---: |
| Previous package 45 | 9 positive integers | 129,875,980 | 788 |
| New uniform source, inherited tail | 9 positive integers | 29,157,244 | 562 |
| New uniform source, V8 tail | 9 positive integers | 24,399,300 | 568 |
| New uniform source, principal tail | 9 positive integers | 20,754,916 | 599 |
| New overlap source, V8 tail | 9 positive integers | 18,262,476 | 624 |
| **New overlap source, principal tail** | **9 positive integers** | **15,534,796** | **655** |
| Previous package 40 | 10 unrestricted integers | 237,520,456 | 782 |
| New uniform source | 10 unrestricted integers | 53,325,896 | 595 |
| **New overlap source** | **10 unrestricted integers** | **39,914,856** | **651** |

Every supplied nine-nonnegative-variable version has the same degree and
three more operations. The archive also retains the overlap source with
the inherited nine-variable tail: degree 21,823,612 at 618 operations.

The principal nine-variable point reduces degree by about 8.3603 times and
operation count by 133 relative to package 45. The ten-integer point reduces
degree by about 5.9507 times and operation count by 131 relative to package 40.
These are improvements to the reviewed explicit low-variable constructions;
they are not claims of global minimality. The 15-positive-variable P67 point
remains smaller by operation count alone.

## Three new ideas

1. **Isolate the monomials that occur.** Only 71 of the 528 possible padded
   quadratic monomials occur in the parent. Each of those 71 must be isolated
   against all 528; absent monomials may collide with each other. A certified
   weight vector has maximum 179, versus the previous full-Sidon maximum 799.
2. **Protect the tested output coefficients.** Row blocks may overlap away
   from their selected outputs. The exact certificate places the final target
   at 5775, instead of 7897 for the new uniform layout.
3. **Use a closer polynomial radical majorant.** Existing divisibility in the
   Jones registers permits a division-free approximation with a strict
   uniform gap. The existing witness h serves as the separating multiplier.
   The majorant introduces no new variable. Its exact defect identities also
   expose the cancellations required for an exact degree proof.

The overlap certificate checks 1,579,776 pair/output conditions. The
principal finalizer has degree 820t+12W+208 and diagonal leading coefficient
3·2^1494, with W=179 and t=18,942.

## Primary equations

- `refined/overlap_nine_positive_major2048.json`: principal nine-positive-variable polynomial.
- `refined/overlap_nine_natural_major2048.json`: its nine-nonnegative-variable version.
- `generated/overlap_ten_integer.json`: principal ten-unrestricted-integer polynomial.
- Other files in `refined/` and `generated/` provide the degree/operation tradeoffs.

The JSON files are literal division-free arithmetic DAGs over fixed integer
leaves and the listed variables. They contain only addition, subtraction,
and multiplication. All powers have fixed exponents and are expanded into
charged multiplication gates. Named registers are abbreviations, never
additional existential variables.

For positive-nine files the variable order is
`epsilon,g,h,s,w,phi,i,j,n`; the builder subtracts one from the three
coordinates epsilon, phi, n to obtain their mixed-domain versions.
For natural-nine files it adds one to the other six coordinates.
The ten-integer order is `f,g,h,k,l,w,x,y,z,m`.

### Degree-certificate distinction

The V8 degree-certificate graph evaluates the **same polynomial** as its
primary graph. The principal major2048 degree-certificate graph evaluates
**D^16 times the primary polynomial**. D is a specified nonzero polynomial;
subtracting its known degree recovers the degree of the primary equation.
The delivered primary equation has no extra factor and no division.
The auxiliary certificate costs are not charged to its operation count.

## Reproduction

Python 3.10 or later and its standard library suffice. No network, symbolic
algebra package, or proof-assistant installation is required for these finite
checks.

~~~sh
python3 verify_release.py
~~~

This verifies file hashes, provenance, exact coefficient payloads, the
source, all 26 primary/certificate graphs, and the independent symbolic
majorant certificates. Its summary is written to `RELEASE_VERIFICATION.json`.
The mathematical unbounded equivalence is proved in the report; this
command checks the finite construction and its algebraic certificates.

To regenerate the polynomial graphs and materialized fixed leaves:

~~~sh
python3 code/build.py
python3 code/build_refined.py
python3 code/materialize_fixed.py
~~~

To run the two main auditors directly:

~~~sh
python3 -O verify.py
python3 -O verify_refined.py
~~~

The latter verifies 16 refined graphs, 192 direct-formula fixtures, and
14 universal multivariate integer-polynomial identities. A separate
majorant auditor imports neither the builders nor either main auditor:

~~~sh
python3 -O proofs/check_majorant2048_independent.py
python3 -O proofs/check_support_independent.py .
~~~

Compile the report with a normal TeX Live installation:

~~~sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
~~~

The release PDF was rendered and visually inspected on all 18 pages.

## Fixed coefficients and provenance

`data/ports/` contains the entire coherent package-31 native tuple
(beta,K,MC,MF_source), totaling 533,099 uncompressed bytes. MF_source is
already shifted; do not shift it again or splice ports from another tuple.

`data/coefficient_recipes.json` explicitly defines each derived fixed leaf.
`data/fixed/` additionally contains all 16 materialized fixed leaves,
totaling 3,331,623 uncompressed bytes. Its manifest stores signs, bit lengths,
byte lengths, and SHA-256 hashes. No coefficient depends on knowing whether
ZFC is consistent.

`SOURCE_PROVENANCE.json` and `ADDITIONAL_PROVENANCE.json` identify the pinned
original source files under `inherited/` and `upstream/`. The hashes in
`SHA256SUMS` cover all release files except that checksum list itself and
the mutable release-run receipt.

## Mathematical and formalization status

The new source and finalizer arguments are ordinary mathematical proofs
formalizable in ZFC. Their composition retains the repository's native
compiler, Jones/Sun arithmetic bridges, literal K215 calibration, and
syntactic proof predicate. The ten-integer branch retains Sun's 2026
preprint theorem, explicitly cited in the report.

This package does **not** claim a new end-to-end Lean/Rocq proof, an exported
object-language ZFC derivation for the numerical coefficients, a reduction
in the number of variables, or a proof of either Con(ZFC) or its negation.
The existing Lean choice-based representation is distinguished from these
materialized coefficient circuits. See `proofs/FOUNDATION_AUDIT.md`.

New material is distributed under the repository's MIT No Attribution
license. Original inherited notices and the Wade/K215 notice are retained.
See `NOTICE.md` and `INTEGRATION.md`.

