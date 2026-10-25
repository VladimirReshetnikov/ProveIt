# Integral projections and lattice forms for Diophantine consistency

Prepared for Vladimir Reshetnikov and ProveIt, 25 October 2026, with AI assistance.

Start with **ConZFC_Integral_Projection_Lattice.pdf**. Its complete, standalone
LaTeX source is **ConZFC_Integral_Projection_Lattice.tex**. The paper prints
every one of the principal equation's 177 quadratic residuals.

## Completed equations

All unknowns range independently over **unrestricted integers**. All five
new equations have fixed integer coefficients and exact degree four.

| Profile | Variables | Residuals | Collected monomials | Height |
|---|---:|---:|---:|---:|
| gram/balanced — principal | 240 | 177 | 5,803 | 6,404 |
| gram/lowheight | 240 | 177 | 9,357 | 4,160 |
| projection/shared240_balanced | 240 | 177 | 5,477 | 15,107 |
| projection/shared240_lowheight | 240 | 177 | 9,217 | 4,512 |
| projection/factorialfree241 | 241 | 177 | 5,141 | 7,968 |

For each complete equation, the ordinary mathematical proof composed with
the identified inherited C222/ZF/ZFC calibration establishes:

> ZFC proves that the equation has no integer zero if and only if Con(ZFC).

The direct source does not simulate K215 or use Jones's universal polynomial.
The new transformations preserve the exact source's integer zero set, with
an explicit inverse for the eliminated coordinate.

## What is new in this contribution

**Eliminate through a coefficient of 2.** The parent has an affine row
A − 2z39 = 0 and a separate row z39 − (z11 + 2z38)² = 0.
Substituting z39 = A/2 keeps every residual quadratic. The surviving square
row forces A to be even at every integer zero, so no parity witness is
needed. The standard rational-root theorem gives a more general form.

**Change the residual combiner.** Instead of always taking a sum of squares,
use Q = rᵀHr/2 with a symmetric positive definite integer matrix of
even diagonal. The principal matrix has only thirteen nonzero cross terms.
Its exact positive-definiteness certificates contain blocks of orders five
and eight with determinants four and one. The rank-eight block is an E8
lattice Gram matrix; that classification is optional, since exact rational
LDL identities already prove the zero-set equivalence.

The shared240_lowheight projection reduces the inspected earlier
240-variable endpoint from 21,482 to 9,217 terms and from height 6,144 to
4,512. The main Gram form trades modest support growth against a 57.61%
height reduction relative to its projected balanced input. These are
improvements within a direct small-coefficient family, not a global minimum
or a universal variable-count record.

## Complete specifications

Each equation directory contains:

- **equation.json**: all residual coefficients, ordered variables, domain,
  and, for a Gram form, the signed mixed-product list;
- **expanded_polynomial.json**: every collected quartic coefficient;
- **METRICS.json**: exact support, height, degree and dimension;
- exact source bytes and a projection or Gram certificate.

A term [c,[i,j,...]] denotes c·xi·xj·...; an empty index list denotes
the constant c. Indices are zero-based. There is no variable exponent,
factorial, binomial primitive, hidden universal-polynomial index, or
undecidable coefficient choice in the final polynomials.

## Verify, rebuild and evaluate

Python 3.10 or later and its standard library suffice:

~~~sh
python3 -B verify.py
python3 -B -O verify.py
python3 -B verify.py --rebuild
python3 -B evaluate.py --profile gram-balanced point.json
~~~

The point file must be a JSON list of exactly 240 integers for the principal
form. Other evaluator profiles are gram-lowheight, sos-balanced,
sos-lowheight, and factorialfree (241 integers).

Verification is read-only unless a --receipt PATH is supplied. Rebuild
checks use temporary directories and compare exact mathematical data.
The checks validate actual source archive bindings, all projection maps,
the essential integrality premise, exact rational positive definiteness,
every expanded coefficient, all variable occurrences, and deliberate
corruption controls. They do not search for zeros or decide consistency.

Rebuild the report with a standard pdfLaTeX installation:

~~~sh
python3 -B build_report.py
~~~

The complete TeX is generated from report/report_template.tex and the
literal residual data. A new TeX installation can change PDF metadata or
font bytes; preserve the delivered checksum manifest until intentionally
regenerating it. The --skip-manifest option checks mathematical data after
an intentional report rebuild.

## Proof scope and sources

The comparison commit is
7a8da414376a80b90ecf799f37ceb26fb9ac674e.
The exact Shared Factorial Error and Factorial-Free Binomial CRT parent
archives are retained under sources/, together with the named logical
interface excerpts. SOURCE_LEDGER.json records their hashes and URLs.
The checker verifies that every copied source equation is byte-for-byte
the corresponding member of the actual original archive.

The new proofs are ordinary mathematics formalizable in ZFC. This release
does not supply a new end-to-end Lean/Rocq proof object or a rebuilt
transitive formal dependency closure. The retained reviews are separate
AI-assisted reviews, not external human peer review. No consistency
assumption or proof of Con(ZFC) is asserted.

## A concrete alternate compilation target

The directory **finite_theory/** contains a complete eleven-axiom theory
whose consistency is provably equivalent in ZFC to the principal
polynomial's having no integer zero, and hence to Con(ZFC) through the
inherited calibration.

Its language has only the eight fixed function symbols 0, 1, negation,
addition, multiplication, pairing, and two projections. Eight ring
identities and two pairing identities form the background. The final
sentence has the form forall z exists u: z encodes every input, u encodes
every arithmetic gate value, the gate equations hold, and the output is
nonzero. All tuples and conjunctions are balanced.

The delivered theory is literal data, with no unexpanded tuple macros:

- **2,736 arithmetic gates**, with arithmetic graph depth 23 edges;
- **107,353 syntax nodes** in all eleven closed sentences;
- maximum functional syntax depth **28 edges**;
- **697,036 bytes** for the complete theory JSON;
- exactly two quantifiers in the polynomial sentence; twenty-two
  quantifier nodes and maximum nesting three in the whole theory.

The independent checker validates all syntax, bound variables, projection
terms, gate equations, and all 5,803 output coefficients. The top-level
verifier binds these source bytes to the principal Gram polynomial.

This is a separate equiconsistency theorem and a concrete future
compilation target. Translating it to the exact binary-relation calculus,
materializing the resulting axiom codes, and compiling a smaller
Diophantine equation remain open. It is not counted as another
Diophantine frontier point.

## Incorporation

Copy the complete folder into a new ProveIt contribution directory.
Keep the original parent archives intact. No GitHub branch, issue,
pull request, or upstream file was changed by this work.

The new work uses the repository's MIT No Attribution license.
Inherited attribution and license notices remain inside the source archives.
MANIFEST.sha256 supplies local integrity checking, not an external signature.
