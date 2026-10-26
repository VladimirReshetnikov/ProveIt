# Direct quartic consistency equations in 218 and 216 integers

Prepared for Vladimir Reshetnikov and ProveIt, 25 October 2026.
Source comparison: commit 953fb4d82d4229f4efc5f9db4cc2bf38ae329bb4.

## Result

The principal literal polynomial is

    P218(x0,...,x217) = R0^2 + ... + R154^2.

All 218 coordinates range over **unrestricted integers**. Every residual is
quadratic with explicit integer coefficients. The complete residual list is
printed in the article and provided as JSON and plain text. The collected
quartic is also supplied.

An ordinary argument formalizable in ZFC, composed with the identified inherited
C222/ZF/ZFC refutation calibration, proves:

    P218 has no integer zero  <=>  Con(ZFC).

The fully specified companion P216 has the same equivalence.

| Equation | Integer variables | Quadratic rows | Degree | Collected monomials | Polynomial height |
|---|---:|---:|---:|---:|---:|
| Inspected source 158 P225 | 225 | 162 | 4 | 7,867 | 128,446 |
| **P218, principal** | **218** | **155** | **4** | **7,726** | **45,161** |
| P216, fewer variables | **216** | **153** | **4** | **15,158** | **334,952** |

The principal residual height is 128; the companion residual height is 384.
All declared coordinates occur. No unknown exponent, coefficient parameter,
factorial primitive, or unstated domain restriction appears in either polynomial.

This construction directly encodes the numerical proof calculus C222. It does
not encode K215 or specialize Jones's universal polynomial. Its generic pooling
and projection ingredients are inherited from sources 158 and 159; the
factorial-free source is inherited from source 157. The new contribution is their
proved and completely emitted composition and its improved equations.

This is a measured improvement in the direct quartic family, not a claim
of global simplicity, literature-wide priority, a proof of consistency, or a
newly compiled end-to-end Lean/Rocq theorem.

### Later repository comparison

A final read-only check found sources 160–165 at commit
fb1bed5eb7196cf35abfaa746c18c6ee7eae6cfb. Their READMEs describe additional
tradeoffs: source 162 reports a 236-variable quartic with 4,876 monomials and
height 7,968; source 165 reports a 238-variable quartic with 5,236 monomials
and height 3,968. Our two forms use fewer variables, while these examples
have smaller support and height. The simultaneous improvement in the table
is specifically over the pinned source 158 P225, not every later direct
construction. Later metrics were read from the cited READMEs, not independently
recomputed; their exact paths and file identities are in
**provenance/LATE_REPOSITORY_CHECK.json**.

## Read first

- **report/report.pdf** and **report/report.tex**: article, proofs, comparisons,
  further research questions, and every principal quadratic residual.
- **algebra/equation218.json**, **expanded218.json**, and **residuals218.txt**:
  complete principal equation in three exact formats.
- **algebra/equation216.json**, **expanded216.json**, and **residuals216.txt**:
  complete companion.
- **composition/COMPOSITION_PROOF.md**: detailed arithmetic proof and signed bootstrap.
- **proofs/COMPOSITION_REVIEW.md**: separate mathematical review and independent binding audit.
- **algebra/ALGEBRA_PROOF.md**: exact integer projection and centering proof.
- **provenance/SOURCES.json**: immutable source paths, hashes, attribution, and dependency boundary.

The independent reviews are internal AI-assisted audits, not external human peer reviews.

## Reproduce the independent checks

Python 3.10 or later and its standard library suffice; no network or proof
assistant is required for these finite checks.

    python3 -B verify.py
    python3 -B -O verify.py
    python3 -B build.py

The verifier replays the inherited raw-to-242 source pipeline, all new literal
edits, private-wire maps, pooled powers, exact 36-square frame with all 17
actual power requests, radical and affine projections, row operations,
both collected quartics, and the printed principal appendix. It also invokes
independent deliberately corrupted-certificate controls.

The builder reconstructs the four new arithmetic stages in a temporary directory
and replays the frozen algebra certificates, comparing 27 JSON files byte for
byte. It leaves the delivered files untouched. To retain a reconstruction:

    python3 -B build.py --output /tmp/conzfc-rebuilt

The output directory must not already exist. Verification receipts can be
written with the option --receipt /tmp/check.json.

These checks do not prove an unbounded semantic theorem, search for zeros, or
decide consistency. The unbounded arguments and named logical dependencies are
spelled out in the article.

## Evaluate a specified tuple

    python3 -B evaluate.py 218 tuple.json
    python3 -B evaluate.py 216 tuple.json --residuals

Input is one JSON array containing exactly the indicated number of integers.
Use a single dash instead of the filename to read from standard input.
Boolean and noninteger values are rejected. Evaluation is not a root search.

## Build the PDF

The LaTeX source uses standard TeX Live packages. All generated inputs are included.

    python3 -B checks/export_report.py
    python3 -B checks/check_report.py
    cd report
    pdflatex -interaction=nonstopmode -halt-on-error report.tex
    pdflatex -interaction=nonstopmode -halt-on-error report.tex

PDF metadata can differ between TeX installations. Mathematical identities are
the literal coefficient arrays and printed residuals.

## Proof and source boundary

The fresh pipeline begins with source 157's factorial-free arithmetic
system and ends with the two literal equations above. The inherited
square-shell/C222 refutation interpretation and the declarations
KEndpoint.c222_iff_zf_refutation and
ConstructibleChoice.zf_refutation_iff_zfc_refutation provide the logical
calibration. Their source excerpts are retained; the complete formal
dependency closure was not freshly rebuilt.

The archive retains the source files needed for its independent finite checks
and new construction. It does not duplicate every historical source package;
retained historical notices describe those original packages.
Exact repository paths identify other inherited mathematics.

See **INTEGRATION.md** for additive placement in ProveIt.
**MANIFEST.sha256** identifies the release files.
