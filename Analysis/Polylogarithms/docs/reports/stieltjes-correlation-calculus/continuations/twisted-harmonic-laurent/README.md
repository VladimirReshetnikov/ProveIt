# Twisted Stieltjes Convolutions and Harmonic Laurent Identities

Research continuation prepared for Vladimir Reshetnikov's ProveIt project,
10 October 2026, with OpenAI assistance.

The article gives complete analytic proofs. Numerical checks are independent
diagnostics, not interval certificates or proof-assistant formalization.

## Main contributions

1. **The archived half-twist target is answered.** The all-index Stieltjes
   multiplication law is proved for every real nonintegral twist, with the
   full Dirac convolution identity, explicit endpoint finite parts, harmonic
   covariant contact corrections, rational Hurwitz coordinates, and unique
   covariant primitives. The exact zero-frequency subtraction recovers the
   untwisted calculus as the twist tends to zero.
2. **A convergent digamma integral evaluates at a quarter-Gamma value.**
   The half-twist gives an ordinary subtracted integral with value
   π[4 log Γ(1/4) − γ − 3 log(2π)] at the midpoint. The sign of its wrapped
   interval is part of the identity.
3. **Complete shifted harmonic Laurent data.** For the Dirichlet series
   E_r(s;a) = sum H_(n−1)({1}^r)/(n+a)^s, the article determines every
   principal Laurent coefficient and finite part at all nonpositive
   integers, as well as the data at s=1. It retains the complex outer shift.
4. **Exact transformation and integration laws.** The finite-part polynomials
   satisfy residue-aware differentiation, depth-mixing reflection, rational
   multiplication, and a complete repeated-antiderivative ladder.
5. **Two concrete source corrections.** The proposed patch repairs the
   real arctanh integral's logarithmic branch for negative parameters and
   removes an unsupported non-elementarity description.

The untwisted periodic Bell algebra, contact terms, primitive tower, and
polylogarithm kernel were already developed in archived ProveIt continuations.
The article consolidates and independently checks them, with explicit
attribution. The positive harmonic beta method, unshifted height-one
literature, Lerch functions, modified Stieltjes constants, and nonsingular
alternating convolution are also credited.

The surviving S6 and newer S8 conjectures remain open. The older rejected S8
vector is distinguished from the newer candidate. No universal literature
priority claim is made.

## Files

| Path | Purpose |
|---|---|
| polylogarithms_finite_parts.pdf | Complete research article. |
| polylogarithms_finite_parts.tex | Modular main LaTeX source. |
| article_standalone.tex | Equivalent single-file source, with every section and reference included. |
| sections/ | Modular proofs, examples, source audit, and research agenda. |
| references.tex | Repository and primary-literature bibliography. |
| code/build_article.py | Build, standalone expansion, reference and overflow checks. |
| code/verify_periodic_calculus.py | Untwisted exact coefficients and independent quadrature. |
| code/verify_twisted_calculus.py | Twisted table, contact, rational and Fourier checks. |
| verification/harmonic_coefficients.py | Exact harmonic Laurent, reflection, multiplication, and primitive checks. |
| verification/harmonic_mellin_numeric.py | Independent scalar continued-Mellin evaluator. |
| verification/additional_numeric.py | Convergent half-twist and branch-correction checks. |
| verification/run_all.py | Sequential replay of all five verification scripts. |
| data/ and verification/*.json | Recorded results, exact tables, and production receipts. |
| verification/independent_review.md | Independent mathematical derivations and source-overlap audit. |
| verification/harmonic_source_overlap.md | Targeted harmonic antecedent comparison. |
| integration/claim_ledger.json | Proof, source, correction, and open-target status. |
| integration/source_manifest.json | Pinned Git blob, SHA-256, and archive-member provenance. |
| integration/INTEGRATION.md | Suggested placement and extraction guidance. |
| integration/confirmed_source_corrections.patch | The two scoped source edits. |
| SHA256SUMS | Integrity hashes of delivered members. |

The package includes all inputs needed to rebuild the article and rerun the
checks. It does not bundle third-party papers, the whole upstream manuscript,
or the already archived incoming ZIP.

## Build the PDF

Requires a standard TeX Live installation with pdfLaTeX, latexmk, AMS packages,
Palatino mathpazo, Latin Modern, microtype, geometry, booktabs, tabularx,
enumitem, hyperref, bookmark, and fancyhdr. These are standard TeX packages.
Poppler's pdfinfo is used for the build receipt.

From this directory:

~~~sh
python3 code/build_article.py
~~~

Or run:

~~~sh
make pdf
~~~

To compile the single-file version independently:

~~~sh
pdflatex -interaction=nonstopmode -halt-on-error article_standalone.tex
pdflatex -interaction=nonstopmode -halt-on-error article_standalone.tex
pdflatex -interaction=nonstopmode -halt-on-error article_standalone.tex
~~~

The build script regenerates article_standalone.tex from the modular source.
Edit the modular sections when maintaining the package.

## Replay the verification

The recorded Python environment is Python 3.12.14, SymPy 1.14.0, and
mpmath 1.3.0. Install dependencies in a virtual environment if needed:

~~~sh
python3 -m pip install -r requirements.txt
python3 verification/run_all.py
~~~

The full numerical replay may take several minutes. Each script may also be
run separately. The runner stops on any failed assertion or process and
records its result in verification/replay_run.json.

The harmonic continued-Mellin script uses 110 decimal digits and compares
local truncation degrees 80 and 100. Its Laurent tests verify the predicted
O(epsilon) remainder in four cases, including a nonzero outer shift.
The extra half-twist script uses 60 decimal digits, with analytic Taylor
quotients at a cancelling endpoint. Exact symbolic tests and floating-point
diagnostics have separate records.

Reruns overwrite their result JSON files. Run on a working copy when the
original delivery records should remain unchanged. Build timestamps,
execution timings, and generated PDF bytes can change on replay.

To verify the original package without regenerating anything:

~~~sh
sha256sum -c SHA256SUMS
~~~

## Source baseline and integration

Pinned repository commit:

e0d9463bdee9685dfb1dddb819059cc738540c57

The source manifest authenticates 87 repository files: 72 chapter sources,
eight manuscript support files, the intake README, the incoming archive,
and five relevant archived report sources. All expected Git blob hashes
match. It also records the incoming archive's member hashes and distinguishes
extracted text from unextracted members.

The proposed source patch is separate from accepting or integrating the new
article. See integration/INTEGRATION.md and the claim ledger. Preserve the
definitions of the finite parts, the outer-shift convention, the full Dirac
unit in the twisted case, and all domains when extracting individual formulas.

Seven further research questions are included in the article, covering
unequal twists, regular Laurent coefficients beyond the finite part,
global reflection/multiplication defects, rational-twist arithmetic,
translated higher Gamma products, collision prescriptions, and the remaining
S6/S8 targets.

No remote repository files were modified during preparation.

