PELL RESIDUES INSTEAD OF POWER VALUES
Explicit Diophantine consistency equations for ProveIt
23 October 2026

START HERE

Read report.pdf for the mathematical argument, comparisons, proof boundary,
and complete printed residual lists for the three principal quartics.
The report is 37 pages. Its source is report.tex, metrics.tex, and appendix/.

The main equations are fixed ordinary polynomials with integer coefficients.
For each equation, ZFC proves that existence of a zero over the specified
domain is equivalent to existence of a finite ZFC refutation. Equivalently,
ZFC proves that its no-zero sentence is equivalent to Con(ZFC).

This is a provable equivalence, not a proof of Con(ZFC) or a numerical
search for a refutation. The proof composes new ordinary mathematical
arguments with the explicitly identified inherited C222 calibration.
No new end-to-end Lean/Rocq proof term or encoded ZFC derivation is supplied.

RESULTS

Name          Domain       Variables  Rows  Degree  Monomials  Height
natural395    N including0       395   321       4       7323       83842758
natural394    N including0       394   320       4      39208       84233382
integer663    All integers       663   397       4       7268  2445790974704
integer687    All integers       687   421       4       5602       63906013

Height means the largest absolute coefficient after expanding and collecting
the entire sum of squares. Rows are quadratic residuals before squaring.

The natural395 form improves the inspected 407-variable direct quartic:
407 -> 395 variables, 8420 -> 7323 monomials, 83843774 -> 83842758 height.
The principal integer form improves the corresponding 888-variable form:
888 -> 663 variables (25.34% reduction), 10156 -> 7268 monomials.
The smaller-coefficient integer companion improves 917 -> 687 variables
and 6986 -> 5602 monomials, with height 63906036 -> 63906013.

The natural394 alternative saves one additional coordinate at the expense
of substantially more monomials. The source655 equation is also included
as the common, uncontracted arithmetic source.

Two additional polynomials in twelve unrestricted integers are included:
  centered12_integral2400: degree 2400, 210 live arithmetic operations;
  centered12_rational2368: degree 2368, 216 live arithmetic operations.
The word "rational" is an inherited construction name, not a change of
variable domain. Both are fixed integer-coefficient polynomials.

These are improvements in stated families and measures. Other incoming
archives contain fewer-variable constructions, including a 37-integer
quartic with a different coefficient architecture. No global-minimality
or worldwide-priority claim is made.

CENTRAL MATHEMATICAL STEP

Let X_n(A), Y_n(A) be the indexed Pell coordinates at A >= 2. Retain the
exact denominator q^H and impose one common root congruence:

  2 A (q+1) = (q+1)^2 + 1 + q^(H+1) h_0.

Then X_n(A) + (q+1-A)Y_n(A) is congruent to (q+1)^n modulo q^(H+1).
The proof evaluates the Pell quadratic ring at q+1-A modulo that modulus.
The resulting integer is positive. Its low digits therefore suffice for
the exact binomial and binomial-divisibility tests.

The old Pell growth equation is imposed on a lower bound L, with A=L+sigma.
This lets A range cofinally in the required residue class. The class always
exists because gcd(2(q+1), q^(H+1)) is 1 or 2, and the possible factor 2
divides (q+1)^2+1. Completeness and the soundness order are proved explicitly.

This removes all eleven full binomial numerator power graphs, leaving
twelve exact-power requests. The raw natural source falls from 690 to 655
coordinates. Previously proved signed Pell and sign-inference arguments
then give the stronger integer reductions. See NOTICE.txt for attribution.

HOW THE LITERAL EQUATIONS ARE STORED

For each equations/<name>/equation.json, let its ordered variables be
x_0,...,x_(v-1). Each residual's "terms" is a list of pairs [c, indices].
It denotes the sum of c times the product of x_i for the indices in that
pair. An empty index list denotes the constant 1; repeated indices denote
ordinary repeated multiplication. For example [-3,[2,2,5]] denotes
-3*x_2^2*x_5. The equation is the sum of the squares of ALL residuals = 0.

expanded_polynomial.json stores the already collected terms of that single
polynomial using the same coefficient/index convention. All coefficients
are literal integers. No variable exponent or unspecified source parameter
occurs in these final polynomials.

The integer equations require no additional sign conditions. Required signs
are encoded in their residuals. The natural equations are over N including
zero. Each printed appendix uses x_i for its own variable list, in exactly
the respective zero-based JSON order. The theorem may rename these dummy
variables to z or w when displaying several equations together.

The integer metadata retains an inherited certificate filename. Both
terminal_elimination_certificate.json and elimination_certificate.json
are provided there as byte-identical compatibility copies.

OFFLINE VERIFICATION AND REPRODUCTION

Python 3.10 or later and its standard library suffice. From this directory:

  python3 verify.py
  python3 -O verify.py
  python3 reproduce.py --output /path/to/new-empty-directory

The first two commands check the delivered equations without regenerating
them in place. They independently collect coefficients, bind the new
modular source to its literal graph, verify domain and inverse-projection
certificates, check the secondary polynomial translations, and run finite
arithmetic regression checks with corruption controls.

The reproduction command rebuilds every new endpoint from the bundled,
hash-pinned parent and compares the resulting JSON objects with the
delivered equations. It needs an empty output directory and no network.
Receipts from successful normal, optimized, and reproduction runs are in
receipts/. The final SHA256SUMS authenticates the delivered file set.

Finite checks are not substitutes for the unbounded proofs. In particular,
small Pell samples do not establish the universal Pell lemmas, and the
coefficient checker does not recompile the inherited logical calibration.
The report and proof notes separate those responsibilities explicitly.

To regenerate the printed residuals and compile the PDF:

  python3 code/render_residuals.py
  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex

A conventional LaTeX installation with the packages named in report.tex
is sufficient. The delivered PDF has been rendered and visually reviewed.

FILE MAP

report.tex, report.pdf       Article, ordinary proofs, comparisons, references.
metrics.tex, appendix/       Generated counts and complete printed residuals.
equations/                  Source and four direct quartic endpoint packets.
code/                       Builders, independent checkers, release helpers.
certificates/               Integer-domain bounds and accounting ledger.
proofs/                     Longer mathematical notes and independent review.
inherited/integer_domain/   Credited prior sign proofs with exact source pins.
supplemental/integer12/     Two centered circuits, proofs, checkers, and the
                            complete preserved 120-file parent dependency.
inputs/                     Original pinned 407/888 dependency ZIP.
provenance/                 Repository commits and bounded prior-art search.
receipts/                   Verification, reproduction, and document receipts.
LICENSE, NOTICE.txt         Repository license and dependency/contribution notes.
SHA256SUMS                  Release file digests, excluding this manifest itself.

SOURCE SNAPSHOT

Comparison repository:
  https://github.com/VladimirReshetnikov/ProveIt
Comparison commit:
  ec80841c07e91be8956ce6ed4af9a9c0b782d3d9
Inherited C222/refutation calibration commit:
  08200eb10fde2db408c69dffd840d6920a569b1f

Full pins and applicable notices are retained in the package. The numerical
C222 source is used directly; the main quartics do not simulate K215 or
instantiate Jones's universal polynomial. The secondary few-variable
package has its own inherited coefficient and encoding dependencies.
