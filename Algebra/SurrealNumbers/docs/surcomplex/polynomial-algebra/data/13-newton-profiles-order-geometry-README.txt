SURCOMPLEX POLYNOMIAL ALGEBRA
Order Geometry, Newton Profiles, and Scale-Resolved Stability
September 21, 2026

CONTENTS

surcomplex_polynomial_algebra.pdf
    The complete 39-page article, including its title page, two-page table of
    contents, 18 main sections, three appendices, and internal bibliography.

surcomplex_polynomial_algebra.tex
    Standalone LaTeX source. No external images or bibliography database are
    required. Standard LaTeX packages and Latin Modern fonts are referenced;
    no font files are included in this archive.

verify_examples.py
    Reproducible exact symbolic checks. Requires Python 3 and SymPy.

verification_report.txt
    The report from the supplied run: 189 exact checks passed, using
    Python 3.13.5 and SymPy 1.14.0. Includes 20 generated matching cases
    of degrees 2 through 6, with seed 20260921 and rational exponent
    denominators 1, 2, 3, and 5. Finite Hensel recursions are checked
    through the fifth power of the uniformizer.

README.txt
    This guide.

READING GUIDE

Sections 1-3: Workspaces, valuation versus modulus, finite factorization,
              division, Hermite interpolation, and Newton sums.
Sections 4-6: Root bounds, Gauss-Lucas, Jensen, the Schoenberg inequality
              with equality case, and polynomial Rouche on order circles.
Sections 7-10: Initial polynomials, arbitrary-rank Newton profiles, exact
               image balls, and scale-resolved critical-point counts.
Section 11: Support-controlled coprime factor lifting, including ordinary
            holomorphic parameters on a fixed domain.
Sections 12-13: Optimal multiset root matching, separated-root stability,
               Newton corrections, discriminants, and sharp examples.
Section 14: Polynomial residue duality, traces, norms, and resultants,
            with explicit repeated-root formulas.
Section 15: Polynomial systems, the Nullstellensatz, finite local algebras,
            and a coupled infinitesimal example.
Sections 16-18: Comparison with the supplied Hahn-coherent manuscripts,
               theorem map, limitations, and further directions.

BUILDING THE PDF

    latexmk -pdf surcomplex_polynomial_algebra.tex

Alternatively run pdflatex three times to stabilize the table of contents
and cross-references:

    pdflatex -interaction=nonstopmode -halt-on-error surcomplex_polynomial_algebra.tex

A standard TeX Live or MiKTeX installation with the packages listed in the
source is sufficient. The supplied PDF was compiled with pdfLaTeX. Its final
build had no undefined references, citation warnings, or overfull boxes.
All pages were rendered and visually reviewed; key theorem and table pages
were also inspected at full size.

RUNNING THE CHECKS

    python verify_examples.py

If SymPy is not installed in the chosen Python environment:

    python -m pip install sympy

The script writes verification_report.txt beside itself and exits nonzero
on a failed check. It requires no network access during execution. Rerunning
it overwrites that report. Execution time in the report is environment-
dependent; all mathematical calculations and the matching-test seed are
specified and reproducible.

SCOPE AND PROVENANCE

The article is a continuation of the three user-supplied manuscripts:
    surcomplex_analysis(3).tex
    surcomplex_research.tex
    surcomplex_global_theorems.tex

Their definitions and relevant results are explicitly credited in the
article. Their original files are not duplicated in this archive. The
article includes the definitions and polynomial proofs needed for its
own main results, so those source files are not compilation dependencies.
Published primary references and the user-specified orientation reference
are listed in the internal bibliography.

Polynomial degrees are ordinary finite integers. The natural valuation,
order-valued modulus, and Hahn-coherent contour constructions are kept
separate. Infinite constructions use set-sized supports and explicit
well-ordering conditions.

Several results are classical over real-closed or valued fields. The
article does not certify publication priority or claim the solution of a
named open conjecture. Its proofs have not been independently refereed or
verified in a proof assistant. The symbolic checks test finite identities
and examples, not arbitrary Hahn supports or the universal theorems.
