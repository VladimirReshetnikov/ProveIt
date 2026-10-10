# Polylogarithm arithmetic bridges: research continuation

**Sharp Remainders and Exact Reductions in Polylogarithm Arithmetic Bridges**  
Prepared for the ProveIt Polylogarithms project with OpenAI assistance, 10 October 2026.

## Start here

- **article.pdf** is the complete research article.
- **article.tex**, **sections/**, and **references.tex** are the complete editable LaTeX sources.
- **claim_ledger.json** records the status and scope of each principal claim.
- **proposed_changes/** contains a checked patch and integration notes.
- **scripts/** and **data/** contain standalone verification programs and their results.
- **source_manifest.json** pins the examined repository sources.
- **SHA256SUMS** records checksums of the delivered files.

Baseline repository:
https://github.com/VladimirReshetnikov/ProveIt

Baseline commit:
78f9e5df05eb0abb16c89fb00b9e89403598bd17

Primary manuscript path:
Analysis/Polylogarithms/docs/manuscript

## Principal results and their status

| Topic | Result | Status |
|---|---|---|
| Log-gamma moments | Late-coefficient growth, least-term location, and a sharp remainder equal asymptotically to half the first omitted term, with two corrections | Analytic proofs |
| Herglotz derivatives | Effective exponentially small remainder, explicit oscillatory expansion, sharp rate, and infinitely many signs | Analytic proofs |
| Rational Herglotz derivatives | Finite Bernoulli–Hurwitz evaluator with explicit coefficients | Constructive refinement of classical closure |
| Cyclotomic doubles | All-weight dimensions for a specified imaginary single-product relation quotient at levels 3 and 4 | Exact formal-algebra theorems; no period-independence claim |
| Gaussian relations | All-exponent mixed endpoint identity, two weight-five shuffle reductions, and explicit inverse-argument corrections | Exact identities |
| S4 | Equivalent simplified forms and a formal obstruction to deriving it from the restricted row family alone | Original conjecture remains open |
| S6 | New weight-seven reduction, frozen integer coefficients, independent numerical checks, and an exact rational residual enclosure below 10^-260 | Conjecture; small residual is certified, equality is not proved |
| Cubic log-gamma moment | Tornheim–Witten derivative evaluation, independent proof and evaluator | Classical Bailey–Borwein–Borwein result, correcting stale open-problem wording |

The underlying fixed-length moment expansion, rational Herglotz closure, divisor representation, and one-sector Tricomi asymptotics are credited to their existing sources. Novelty is assessed relative to the inspected corpus and cited literature; the article does not claim an exhaustive worldwide priority search.

## Requirements

The delivered computations were run with Python 3.12 and the exact package versions in **requirements.txt**. The numerical/figure environment requires Python 3.11 or later. The rational S6 certificate uses only the Python standard library.

For the PDF, install a normal TeX Live distribution with pdflatex, latexmk, Latin Modern, AMS packages, mathrsfs, mathtools, booktabs, enumitem, graphicx, xcolor, microtype, xurl, fancyhdr, hyperref, and bookmark.

    python3 -m pip install -r requirements.txt

No network access is needed after dependencies are installed.

## Build and verify

Run these commands from this directory.

    make pdf
    make exact
    make numeric
    make figures

The included figures and data already allow the PDF to be built without rerunning numerical research. All checks can be run individually:

    python3 scripts/certify_s6.py --output data/s6_rational_certificate.json
    python3 scripts/verify_relation_spaces.py --output data/relation_space_certificates.json
    python3 scripts/verify_moments.py --dps 180 --output data/moment_checks.json
    python3 scripts/verify_herglotz.py --dps 70 --output data/herglotz_checks.json
    python3 scripts/verify_tornheim.py --dps 80 --degree 120 --diagonal 240 --output data/tornheim_checks.json
    python3 scripts/verify_analytic_identities.py --output data/analytic_identity_checks.json
    python3 scripts/verify_s6_mellin.py --output data/s6_mellin_check.json
    python3 scripts/series_crosscheck.py --output data/series_crosscheck.json
    python3 scripts/make_figures.py

The S6 Mellin computation and independent Euler-series computation use 220 and 300 working decimal digits respectively. The exact rational certificate is much faster and verifies the advertised 260-digit residual bound directly.

The moment script checks six orders at 180 digits and repeats orders 20 and 80 at 215 digits. It integrates to infinity; replacing this with an arbitrary finite cutoff can destroy the least-term error check. The Herglotz script raises precision to handle cancellation in high-order exact Bernoulli sums.

## What is certified

**Exact:** the S6 residual enclosure, rational relation-space calculations, sparse separating functional, and low-order coefficient-polynomial checks.

**Analytic bounds with floating-point evaluation:** the Herglotz sector tails and Tornheim series truncation. The mathematical tail inequalities are proved; ordinary mpmath rounding and quadrature are not themselves interval-certified.

**Conjectural:** S4 and S6 as exact equalities. An interval containing zero and narrower than 10^-260 is powerful evidence, but does not prove that zero is the exact value.

The mathematical proofs have undergone internal independent audits. This is not an external referee report or a formal proof-assistant certification.

## Proposed repository changes

The patch in **proposed_changes/manuscript-corrections.patch** was checked with git apply --check against the exact pinned source bytes. It covers:

1. The named cubic-moment evaluation, including its bibliographic entry.
2. The two weight-five shuffle rows and sharper spanning statement.
3. The coefficient-label typo in the sixth-point Stieltjes proof.
4. The corresponding cubic-moment discovery wording.

The inverse-argument mixed survivor correction is supplied separately as an insertion component and reconciliation note because several historical tables must be updated consistently. See **proposed_changes/README.md**. The article's correction register provides the full mathematical rationale.

Example patch review from a checkout at the baseline:

    git apply --check /path/to/manuscript-corrections.patch
    git diff

The patch is a proposal; review it against later upstream changes before application. The full article is intended as a new research continuation, and the S6 formula belongs in the conjecture ledger.

## Data integrity and provenance

Run the standard checksum verification from this directory:

    sha256sum -c SHA256SUMS

The source manifest records Git blob SHA-1 and SHA-256 hashes for 31 examined source files. The original repository source files and third-party papers are referenced rather than redistributed. The bibliography links to primary sources.

The package excludes abandoned searches and unaccepted exploratory candidates. The exact integer S6 vector is identical in the Mellin, Euler, and rational-certificate programs.

