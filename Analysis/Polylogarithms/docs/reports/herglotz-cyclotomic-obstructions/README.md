Cyclotomic Obstructions and Optimal Truncation
for the Herglotz--Zagier Function

Research continuation for Vladimir Reshetnikov / ProveIt
8 October 2026 (UTC)

1. What this package contains

The main article is herglotz_research.pdf, with its complete LaTeX source in
herglotz_research.tex. It develops two related parts of the Herglotz--Zagier
research thread in Analysis/Polylogarithms:

  * An all-conductor theorem determining every rational linear relation
    among the cyclotomic exterior symbols beta_q(a), followed by complete
    criteria for formal rational-dilogarithm reduction, a recurrence
    parametrization, a constructive rational core algorithm, and a complete
    formal classification of J(2/q).

  * Sharp real optimal-truncation laws for the Bernoulli--zeta expansion,
    including uniform correction terms, unique cutoff transitions, an
    exponentially smaller arithmetic displacement, and positive-measure
    bounds that produce exact rational error certificates.

The article also proposes targeted corrections to the supplied drafts and
records an exact counterexample to a finite-field identity in the inspected
2020 Radchenko--Zagier preprint. It does not claim to audit every formula in
all the source documents.

2. Mathematical scope

Throughout, "formal reduction" means reduction in the rational pre-Bloch
group by the standard five-term calculus, with logarithmic products and
rational multiples of pi^2 allowed in the analytic realization. The exact
criterion for a reduced positive rational p/q is

    p^2 == +1 or -1 (mod q), and q^2 == +1 or -1 (mod p).

The signs are independent; the condition modulo 1 is vacuous. Successful
formal reductions give actual dilogarithm identities. A nonzero exterior
symbol rules out a certificate in this calculus; it does not prove that no
accidental numerical relation can exist. No transcendence or numerical
independence statement is inferred from a failed integer-relation search.

The core program computes C(p/q) such that

    F(p/q)-F(1)-C(p/q)

is a combination of logarithmic products and pi^2. It does not compute that
remaining logarithmic expression. All dilogarithm arguments in the produced
core lie strictly between 0 and 1. The consecutive-integer shortcut keeps
the number of terms O(log max(p,q)); optional diagnostic prime factorization
is a separate computation and has no asserted polynomial bit complexity.

The sharp asymptotic laws are real-variable statements with the uniformity
conditions stated in the article. Algebraic expansions and exponentially
small displacements are distinguished by defining the reference transition
exactly before subtracting it.

The article contains mathematical proofs. The scripts provide finite exact
checks, symbolic calculations, numerical cross-checks, and rational interval
certificates; they are not a proof-assistant formalization. The work is an
AI-assisted research draft and has not been externally refereed. A limited
literature search does not establish worldwide priority for every result.

3. Source provenance

Repository:
  https://github.com/VladimirReshetnikov/ProveIt

Inspected directory:
  Analysis/Polylogarithms/docs

Source snapshot commit:
  c78c7c3dc2fc742a1af9492e47d578b3fb4e01e7

data/source_snapshot.json preserves the collected repository inventory and
blob hashes byte-for-byte from the input snapshot. It is metadata, not a
complete copy of the original repository.
The article identifies the relevant reports and distinguishes corrections
to repository drafts from the separate inspected-preprint counterexample.

Principal published starting point:
  D. Radchenko and D. Zagier,
  Arithmetic properties of the Herglotz function,
  J. reine angew. Math. 797 (2023), 229--253.
  https://arxiv.org/abs/2012.15805
  https://people.mpim-bonn.mpg.de/zagier/files/preprints/HerglotzFunction.pdf

The finite-field counterexample is scoped to arXiv:2012.15805v1, Section 7.2,
page 16 of the inspected 18-page preprint. It is not automatically an
assertion about the separate, uninspected typeset journal version.

4. Build the article

Run commands from this package's root directory. A normal TeX Live or MiKTeX
installation providing pdfLaTeX, latexmk, and the packages loaded in the
source is sufficient. The source uses standard article, AMS math, Latin
Modern, geometry, microtype, longtable, graphicx, fancyhdr, xurl, and
hyperref packages. Preserve the relative paths of any accompanying figures.

The standard-library build runner selects latexmk when available and
otherwise runs pdfLaTeX three times. It sets the working directory to the
package root, so it also works when invoked by an absolute path from another
directory:

    python build.py

To select the fallback explicitly, or inspect the commands without running
them:

    python build.py --engine pdflatex
    python build.py --dry-run

Alternatively, invoke the TeX tools directly from the package root:

    latexmk -pdf -interaction=nonstopmode -halt-on-error herglotz_research.tex

If latexmk is unavailable, run three pdfLaTeX passes:

    pdflatex -interaction=nonstopmode -halt-on-error herglotz_research.tex
    pdflatex -interaction=nonstopmode -halt-on-error herglotz_research.tex
    pdflatex -interaction=nonstopmode -halt-on-error herglotz_research.tex

Check the final log for cross-reference or table-of-contents rerun warnings;
an additional pass can be required after changes to pagination. The main
output filename is herglotz_research.pdf. The supplied figures can be used
directly and do not need to be regenerated before compilation.

5. Python dependencies

Use Python 3.11 or newer for the complete package. The exact cyclotomic,
recurrence, rational-core, and rational-interval programs use only the
standard library. The numerical programs require mpmath; the coefficient
generator requires SymPy; the figure generator directly imports Matplotlib
and NumPy.

The supporting computations were run with Python 3.12.14, mpmath 1.3.0,
SymPy 1.14.0, Matplotlib 3.10.8, and NumPy 2.3.5. These four direct dependencies
are pinned in requirements.txt. Install them in a chosen Python environment:

    python -m pip install -r requirements.txt

No third-party Python package is required merely to read the PDF or compile
the already supplied LaTeX and its accompanying figure files. Invoking the
TeX tools directly does not require Python at all.

6. Reproduce the supplied checks

The following commands are valid from the package root. Default output
paths are resolved relative to each script, so generated data go under
data/ and the reproduced figures go under figures/.

Exact cyclotomic matrices, ranks, and J-boundary classification:

    python code/verify_cyclotomic.py

This checks moduli 1 through 200 in detail, uses exact rational Gaussian
elimination through 80, and writes the rank table and J classification
checks through 1000. It also verifies the exact modulus-7 preprint defect.

Recurrence parametrization and rational boundary certificates:

    python code/verify_recurrences.py --bound 500

This compares all 1076 admissible coprime pairs 1<=p<=q<=500 with the three
recurrence families. Every selected core has its rational exterior boundary
checked exactly. The output is recurrence_checks.json and recurrence_pairs.csv.

Constructive cores, including exhaustive checks through 1000:

    python code/dilogarithm_cores.py --verify-bound 1000

This writes 18 illustrative examples and checks all 2106 admissible pairs
through 1000 in both orientations: 4212 exact rational boundary checks.
The longest optimized core in that range has 13 terms, at 610/987.

Individual examples, printed as JSON:

    python code/dilogarithm_cores.py 5 13
    python code/dilogarithm_cores.py 3 8
    python code/dilogarithm_cores.py 10 33
    python code/dilogarithm_cores.py 2 7

The last example correctly reports a formal obstruction. Use --output PATH
to save a single example. For very large integers, --no-prime-certificate
omits the optional trial-factorization check while retaining the exact core
construction and descent identities.

Independent J evaluations from the defining real integral:

    python code/verify_J_evaluations.py --digits 80 --max-even-m 40

This checks five exceptional formulas and the even-denominator family
J(1/m), m=2,4,...,40: 25 checks in total. The supplied run's maximum absolute
residual is about 2.06e-79. The reference integral does not use F values or
the finite dilogarithm sum. This is a floating-point check, not a rigorous
quadrature enclosure. It normally takes only a few seconds in the tested
environment.

Exact rational enclosures for F(2), F(4), F(8), and F(16):

    python code/certified_intervals.py

The JSON contains exact fractional endpoints and outward-rounded decimal
displays. These certificates use the proved positive-measure bounds and a
first-omitted-term zeta bound proved using the positive coth kernel. The exact
fractions, rather than a floating-point residual, are the certificate data.

Numerically corroborate the exact certificates at 400 decimal digits:

    python code/verify_interval_cross_checks.py

This independently compares 54 zeta values with the rational zeta bounds
and F(2), F(4), F(8), F(16) with their rational intervals. The reference F
values use the finite log-sine formula. All 58 comparisons passed in the
supplied run. These floating-point containment checks corroborate the
implementation; the exact inequalities and rational arithmetic supply the
certificates. Use --digits to change the working precision.

Independent checks of the corrected even-conductor derivative formula:

    python code/verify_derivative_correction.py --dps 65

The reference values come from the positive Binet derivative integral.
The script checks q=4,6,8,12, the missing-midpoint correction, the error
caused by counting that correction twice, and the elementary value
F'(1/2)=2+pi^2/4. It also checks the approach of cot(theta)*Cl_2(theta) to
-log(2) at theta=pi. These are numerical checks, not interval proofs.

Generate the first four exact remainder-coefficient polynomials:

    python code/truncation_coefficients.py --order 3

The coefficients C_0 through C_3 are printed to standard output. Increasing
--order requests further exact symbolic terms; runtime grows with the order.

Reproduce the supplied 90-digit transition and sharp-remainder checks:

    python code/verify_truncation.py --digits 90

The transition calculation uses generalized exponential integrals, includes
independent positive-real gamma quadrature checks, and records analytic
bounds for omitted Dirichlet terms. Its high-precision root approximations
remain floating-point results, distinct from rational_intervals.json.

A smaller demonstration can be saved separately without replacing the full
data file:

    python code/verify_truncation.py --quick --digits 55 --output data/truncation_quick_checks.json

Reproduce the article's PDF and PNG figures:

    python code/reproduce_figures.py

The rank figure reads data/rank_table.csv and checks the displayed rank
formula against its exact entries. The optimal-error figure evaluates the
proved first correction coefficient. Both are written to figures/; the PNG
resolution defaults to 300 dpi. No interactive display, network connection,
or external TeX installation is needed for this command. Use --output-dir
PATH to save another copy or --dpi NUMBER to change the PNG resolution.

The scripts with adjustable settings document them through --help.
verify_cyclotomic.py has a fixed verification grid and takes no options.

To check that the supplied files match the final package's hash manifest,
run the following from the package root on a system providing sha256sum:

    sha256sum -c MANIFEST.sha256

The manifest records package-relative SHA-256 digests and excludes itself.
Rebuilding or regenerating artifacts may change their bytes; a resulting
digest change is not, by itself, a mathematical discrepancy.

7. File inventory

Main document and metadata:
  herglotz_research.tex              Complete article source.
  herglotz_research.pdf              Compiled article.
  README.txt                        This guide.
  build.py                          Standard-library LaTeX build runner.
  requirements.txt                  Pinned direct Python dependencies.
  MANIFEST.sha256                   Package-relative artifact SHA-256 digests.
  data/theorem_ledger.json           Proved results, known inputs, and open issues.
  data/source_snapshot.json          Original repository inventory and blob hashes.
  data/proposed_corrections.json     Scoped corrections and supporting evidence.

Exact algebraic checks:
  code/verify_cyclotomic.py          Regular-representation and formal J checks.
  data/cyclotomic_checks.json        Detailed integer/rational verification record.
  data/rank_table.csv               Boundary ranks for conductors 1 through 1000.
  code/verify_recurrences.py         Complete bounded recurrence comparison.
  data/recurrence_checks.json        Verification summary and sample cores.
  data/recurrence_pairs.csv          All 1076 selected pairs through 500.
  code/dilogarithm_cores.py          Exact rational-core construction and certificates.
  data/dilogarithm_cores.json        Examples and exhaustive checks through 1000.

Analytic calculations and certificates:
  code/verify_J_evaluations.py       Independent direct-integral J evaluations.
  data/J_evaluation_checks.json      All 25 numerical comparison records.
  code/verify_derivative_correction.py  Independent even-conductor derivative checks.
  data/derivative_correction_checks.json  Formula and midpoint-limit comparisons.
  code/certified_intervals.py        Exact rational enclosures for four F values.
  data/rational_intervals.json       Fractional and outward-rounded endpoints.
  code/verify_interval_cross_checks.py  Independent zeta and finite-F comparisons.
  data/interval_cross_checks.json    Numerical corroboration at 400 digits.
  code/truncation_coefficients.py    Exact SymPy coefficient generator.
  code/verify_truncation.py          Sharp remainder and transition verification.
  data/truncation_checks.json        Supplied full 90-digit analytic check grid.

Figures:
  code/reproduce_figures.py          Reproduces both figures from the data/formulas.
  figures/cyclotomic_rank.pdf        Vector plot of exact ranks through q=200.
  figures/cyclotomic_rank.png        Raster copy of the rank plot.
  figures/optimal_correction.pdf     Vector plot of the optimal-error coefficient.
  figures/optimal_correction.png     Raster copy of the correction plot.

The PDF figures are referenced by relative path in the LaTeX source. The
original repository reports remain separate source material; the snapshot
metadata does not imply they are bundled here.

8. Reading and extending the work

Read the formal-reduction definitions before interpreting a negative result.
Consult data/theorem_ledger.json for the distinction between newly derived
theorems, classical inputs, supporting numerical data, and unresolved work.
The further-research section of the article gives the proposed continuation.
Particularly concrete next steps are an algorithm for the full logarithmic
remainder of a successful core, additional arithmetic sectors in the sharp
transition expansion, and proof-assistant formalization of the exact algebra.

9. Final verification records

  data/verification_run.json        Integrated package verification command results.
  data/truncation_quick_checks.json Additional 55-digit quick-run comparison data.
  data/remainder_coefficients.txt   Exact C_0 through C_3 generated by SymPy.
  data/document_validation.json     Final PDF build and visual inspection record.

The final article is 29 pages. Its cross-references and citations resolve,
and the final LaTeX log has no overfull boxes, underfull boxes, or warnings.
All pages were rendered and visually reviewed; selected mathematical pages
were inspected at full resolution. The PDF includes selectable text and
relative-path figure assets, which are included in this package.
