# Lower degree and fewer witnesses for Diophantine consistency

Prepared for Vladimir Reshetnikov and ProveIt, 25 October 2026, with AI assistance.

Start with **ConZFC_Trace_Radical_2026-10-25.pdf**. Its complete editable
source is report/main.tex, with all TeX inputs included. The paper gives
the complete compact formula and coefficient recipe and prints all 172
quadratic residuals of the sparse unrestricted-integer equation.

## Results

The principal compact equation has **10 strictly positive integer variables,
exact degree 232, and 87 live binary arithmetic operations**. It improves
the matched 87-operation, degree-304 parent without changing its fixed
coefficient tuple. Four further same-cost degree reductions are included:

| Operations | New degree | Matched parent degree |
|---:|---:|---:|
| 75 | 402 | 626 |
| 76 | 352 | 464 |
| 79 | 290 | 382 |
| 80 | 258 | 338 |
| 87 | 232 | 304 |

The direct-calculus component provides three different **unrestricted
integer** quartics:

| Equation | Variables | Quadratic residuals | Collected monomials | Coefficient height |
|---|---:|---:|---:|---:|
| direct/equations/self_power236 | 236 | 172 | 4,992 | 10,722 |
| direct/equations/self_power235 | 235 | 171 | 10,536 | 10,730 |
| direct/equations/shared_error234 | 234 | 171 | 21,385 | 44,800 |

For each literal equation, the ordinary mathematical proof composed with
the identified inherited arithmetic and refutation calibrations gives:

> ZFC proves that the equation has no solution in its stated domain
> if and only if Con(ZFC).

No consistency assumption selects the coefficients. No variable exponent,
factorial, binomial primitive, or external predicate remains in a final
polynomial. The compact component retains native/K215 ancestry; the direct
quartics compile the numerical C222 proof calculus without K215, Jones,
or a machine coefficient tuple.

These results improve particular inspected constructions. They do not
establish a global simplicity minimum or literature-wide novelty.
The 234-variable quartic reduces the matched 240-variable equation's
dimension and support, but increases coefficient height. The sparse
236-variable equation is a separate useful tradeoff.

## Main mathematical ideas

1. **Use the explicit strong Pell trace once.** The trace satisfies
   f = 1+2a = a+(1+a) and f = 1 modulo c. Replacing
   f²(cT-R)-c by f(cT-R)-c preserves both index-recovery
   congruences. The proof rechecks signed transport and the negative
   Lucas-rank cases. An explicit polynomial map preserves the complete
   parent polynomial and proves positive completeness.
2. **Project common quadratic directions.** A vector in the common
   kernel of all residual Hessians exposes a coordinate appearing
   only linearly after an integral shear. A unit slope allows its
   quadratic restoration without increasing residual degree.
   Six exact projections per direct branch are certified.
3. **Use the diagonal power F=t^t.** A coefficient-by-coefficient
   proof shows this already authenticates all proof-label
   multiplicities. A cofinal even-horizon construction retains every
   necessary binomial/beta-CRT parity and size property.

## Verify and rebuild

Python 3.10 or newer and the standard library suffice:

    python3 -B verify.py
    python3 -B verify.py --rebuild
    sh build_report.sh

The first command checks the final manifest, complete component
certificates in normal and optimized Python, all fixed coefficients
by exact reconstruction, circuit reconstruction, and literal report
inputs. The second additionally rebuilds the direct artifacts in a
disposable copy and compares their bytes.

The report needs a standard TeX Live installation. Rebuilding may alter
PDF metadata and hence the PDF hash; the canonical polynomial JSON
artifacts are independent of that. Rebuilding the PDF in the sealed
folder can intentionally make its old manifest hash stale.

The tests reject 90 compact operator corruptions and five direct
certificate/coefficients corruptions. They are exact finite algebra
checks, not searches for solutions. The unbounded mathematical arguments
and logical calibration remain separate.

## Files

- report/: paper source, generated literal appendix, coefficient recipe,
  exact comparison and degree tables.
- compact/: five complete polynomial circuits, fixed numeral payloads,
  proofs, predecessor closure, independent exact checker, and receipts.
- direct/: three complete residual specifications and collected
  polynomials, exact projection certificates, inverse maps, generators,
  evaluators, independent checker, and retained proof/calibration sources.
- review/: independent internal mathematical reviews of the new
  arguments and article. These are AI-assisted reviews, not external
  human peer review.
- verification/: root replay and PDF inspection receipts.
- SOURCE_SNAPSHOT.json: immutable source boundary and archive hashes.
- MANIFEST_SHA256.json: exact final file identities.
- INTEGRATION.md: suggested integration and formalization boundaries.

## Proof status

This package supplies ordinary mathematical proofs formalizable in ZFC.
It inherits the explicitly identified native or C222/ZF/ZFC calibrations.
It does not supply a new end-to-end Lean/Rocq development or encoded
object-language ZFC proof term, and it does not prove consistency.

The complete immutable comparison snapshot is ProveIt commit
b7e35224c04fe1031c0a53f80a395e9b32205022. Earlier source packets are
credited and preserved as dependency subsets; obsolete experiments
and historical PDFs are omitted. Use the new scoped entry points,
not an old whole-release manifest for an intentionally smaller subset.

New material follows ProveIt's MIT No Attribution license. Inherited
licenses and notices remain with their respective sources.
