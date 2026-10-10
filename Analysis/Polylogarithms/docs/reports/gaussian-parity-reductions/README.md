# From Polylogarithm Conjectures to Exact Reductions

**Shuffle certificates, complementary-power ladders, and effective log-gamma moment asymptotics**

Research continuation prepared for Vladimir Reshetnikov and the ProveIt project, 9 October 2026.

## Read first

The complete article is **polylogarithms_exact_reductions.pdf**. Its editable master is **article/polylogarithms_exact_reductions.tex**, with all section sources, references, and the vector figure included.

The audited source checkpoint is commit **afed07429d3d37eceb6c8e9e54cf4da2d3f39d53**:

https://github.com/VladimirReshetnikov/ProveIt/tree/afed07429d3d37eceb6c8e9e54cf4da2d3f39d53/Analysis/Polylogarithms/docs/manuscript

No upstream repository files have been modified. This package is intended for review and integration. Later repository revisions may already incorporate some of these conclusions.

## Principal results

Eleven identities recorded numerically in the audited manuscript receive explicit local proofs:

| Manuscript family | Number | Proof mechanism |
|---|---:|---|
| Weight-five Gaussian double relation | 1 | Two exact shuffle products |
| Weight-six Gaussian double evaluations | 5 | An explicit binomial parity formula |
| Weight-four Gaussian triple evaluations | 3 | Height-one antiderivative, specified branches, and shuffles |
| Cubic and quartic trilogarithm ladders | 2 | Landen, Kummer, and Rogers certificates |

Additional results include:

- An exact formal shuffle quotient count in every weight and depth, with a rational normal-form algorithm. The ten weight-six depth-three words have three indecomposable Lyndon generators.
- A strengthening of the weight-five spanning statement from three same-argument quantities to **at most two**, modulo the indicated single-value products.
- An all-weight double parity formula, valid at every point of the unit circle except one and when an index is one.
- Classical reductions for every index containing exactly one 2 and otherwise ones, at arbitrary depth and in any position.
- A uniform complementary-power trilogarithm identity for bases satisfying rho^a + rho^b = 1.
- Exact Gaussian double reductions through weight twelve, supplied as JSON and LaTeX rows.
- A meromorphic continuation of the log-gamma moment generating function, with its poles and residues.
- A late-coefficient asymptotic for the known moment expansion, proving divergence at every fixed moment.
- An explicit remainder bound when the number of retained terms grows with the moment.
- An integer outward-interval certificate fixing **112 common decimal places** of the cubic log-gamma moment.
- Twelve further research questions with precise targets and proposed methods.

The coefficient asymptotic uses

    c_k = (1/k) [u^(k-1)] Gamma(1-u)^k,
    -tau psi(1-tau) = 1,
    rho = tau/Gamma(1-tau), alpha = -log(rho).

The article proves c_k ~ C rho^(-k) k^(-3/2), with a full inverse-power expansion. For the moment M_n and K = floor(n/alpha - sqrt(n)), n >= 7, the explicit normalized remainder bound has the scale (e alpha/n)^n. Section 7 gives every constant and hypothesis.

## Attribution and unresolved questions

The general parity theorem, the Lyndon structure of shuffle algebras, and the classical functional equations are established literature. The article supplies independently checkable specializations and certificates. It does not claim to have discovered these general tools.

Two literature corrections matter:

1. The cubic log-gamma moment already has a Tornheim-derivative evaluation in Bailey–Borwein–Borwein, The Ramanujan Journal 36 (2015), Theorem 6.
2. The fixed-order factorial moment expansion is already Theorem 8.1 of Amdeberhan–Coffey–Espinosa–Koutschan–Manna–Moll, Proceedings of the AMS 139 (2011).

The coefficient asymptotic and effective growing-truncation bound are the quantitative extension developed here. No exhaustive global priority claim is made over the inverse-gamma literature.

Four inverse-argument mixed reductions are rederived to reconcile the consolidated manuscript with the project's previous continuation. They are **inherited results**, excluded from the eleven promotions.

The S4 mixed Gaussian identity remains a conjecture. The article proves a simpler equivalent form and gives an independent numerical diagnostic. That diagnostic is not an equality proof. Higher golden ladders still require the local certificates requested here; this is not a claim that every such formula is globally unknown in the literature.

No numerical linear or algebraic independence result is claimed for the surviving constants. A formal quotient dimension is not automatically the dimension of a space of numerical periods.

## Files

| Location | Contents |
|---|---|
| polylogarithms_exact_reductions.pdf | Complete article |
| article/polylogarithms_exact_reductions.tex | Master LaTeX source |
| article/sections/ | Seven source files containing all nine article sections |
| article/references.tex | Bibliography used by the master |
| article/figures/ | Vector PDF, PNG, plotting data, and standalone figure reproducer |
| code/run_checks.py | Fast and full verification entry point |
| code/shuffle_certificates.py | Exact rational word algebra and normal forms |
| code/depth/ | Exact coefficient checks, quadratures, and formulas through weight twelve |
| code/ladders/ | Exact algebraic substitutions and rational rows, plus diagnostics |
| code/moments/ | Integer cubic certificate and high-precision moment diagnostics |
| code/verify_s4_candidate.py | Numerical comparison for the unresolved conjecture |
| data/ | Shuffle normal forms, verification reports, and S4 diagnostic |
| provenance/integration_register.json | Detailed status mapping for integration |
| provenance/integration_register.csv | The same nineteen entries in tabular form |
| provenance/source_manifest.json | Pinned source paths, hashes, and generation environment |
| provenance/analytic_cross_review.md | Independent proof-audit notes and resolved issues |
| SHA256SUMS | Integrity hashes of the shipped package files |

In generated Gaussian tables, g denotes the imaginary part at even weight and h the real part at odd weight. L=log(2), G=beta(2), and Bn=beta(n) for even n.

The descending-index convention throughout is

    Li_{a,b}(z,1) = sum_{n>m>0} z^n/(n^a m^b).

The word convention is outer letter first: 0^(a-1)1 0^(b-1)1. Retain these conventions when importing formulas or comparing with papers using increasing indices.

## Reproduce the calculations

Python 3.10 or later is recommended. Dependency versions are pinned in requirements.txt; the delivered run used Python 3.12. From the extracted archive root:

    python -m pip install -r requirements.txt
    python code/run_checks.py --fast

The fast command re-expands 511 word normal forms through weight nine, checks 45 bigraded counts, checks all eight source double/triple expressions exactly, replays the 35 exact ladder checks, and regenerates the integer cubic certificate. Every field of the latter must agree exactly with the shipped reference.

For the independent numerical diagnostics as well:

    python code/run_checks.py --full

This adds the 64 depth quadratures, 22 inherited-mixed checks, 100/200-digit ladder checks, the S4 comparison, 180-digit moment diagnostics, and figure regeneration. It may take several minutes. Success is recorded only after every selected program completes.

Fast and full reports are separate: data/validation_fast.json and data/validation_full.json. A delivered full report subsumes the fast checks; fast mode need not be run first.

Individual components can be run directly:

    python code/shuffle_certificates.py --max-weight 9 --output data/shuffle_verification.json
    python code/depth/verify_depth.py
    python code/depth/verify_mixed.py
    python code/ladders/verify_ladders.py --digits 100 200 --output code/ladders/verification.json
    python code/moments/certify_cubic.py --order 360 --digits 130
    python code/moments/verify_moments.py
    python code/verify_s4_candidate.py
    python article/figures/make_moment_figure.py

Programs overwrite their own recorded outputs when rerun. SHA256SUMS identifies the original shipped files. Timing fields and PDF metadata can differ between runs; exact mathematical certificate fields should agree. No network access is needed after installing dependencies.

### Meaning of verification

The shuffle and algebraic programs use exact arithmetic. They verify finite witnesses for analytic statements whose functional equations are proved or cited in the article.

The cubic enclosure combines outward integer arithmetic with proved analytic remainder estimates. Its endpoints share 112 **truncated** decimal places. This is a rational enclosure.

Ordinary mpmath residuals and plotted data are **diagnostics**. They are not interval bounds and do not prove the S4 conjecture or period independence.

The proofs were checked by independent derivations and code paths in this research workflow. The package is not represented as proof-assistant formalization or external journal peer review.

## Build the PDF

A standard TeX Live installation with latexmk, pdflatex, Latin Modern, AMS packages, mathtools, booktabs, longtable, enumitem, graphicx, xcolor, microtype, xurl, fancyhdr, hyperref, and bookmark is sufficient:

    make pdf

This compiles under article/ and copies the PDF to the archive root. No BibTeX pass is needed because references.tex supplies the bibliography. No network access is required.

Without make:

    cd article
    latexmk -pdf -interaction=nonstopmode -halt-on-error polylogarithms_exact_reductions.tex

The supplied PDF has resolved cross-references and was inspected after rendering. The make clean command removes auxiliary TeX files while retaining the source and PDF.

## Integration guidance

Use the JSON or CSV integration register as the editorial checklist. Its nineteen entries comprise eleven promotions, two known-literature corrections, four inherited reductions, and two open groups.

For each source formula, retain its existing label where it has one, replace numerical-status wording with the supplied proof or a reference, and preserve the convention. Unlabelled entries are identified by their section and display; the register does not invent labels for them.

- **Chapter 4:** incorporate the two-product weight-five proof and stronger spanning bound; prove the five weight-six doubles and three weight-four triples; explain the formal rank-seven quotient; reconcile the inherited mixed values.
- **Chapter 3:** add the complementary-power theorem and local cubic/quartic certificates. Keep higher-weight numerical ladders distinct from these proved weight-three identities.
- **Chapter 7:** cite the published cubic Tornheim representation and fixed-order expansion. Replace the old named-atom question with a specified smaller-algebra reduction problem. Add the coefficient and effective remainder theorems if within the chapter's scope.
- **Discovery discussion:** retain S4 as conjectural and make exact certificate generation the next step after numerical recognition.

The article sections can be split for integration. Labels are stable, while theorem numbering is supplied by the master and may change in the destination. Bibliography keys may need reconciliation with existing repository keys.

## Primary references

- Radford, A natural ring basis for the shuffle algebra and an application to group schemes, Journal of Algebra 58 (1979), 432–454. https://doi.org/10.1016/0021-8693(79)90171-6
- Panzer, The parity theorem for multiple polylogarithms, Journal of Number Theory 172 (2017), 93–113. https://arxiv.org/abs/1512.04482
- Umezawa, An explicit parity theorem for multiple polylogarithms, arXiv:2508.02040 (2025). https://arxiv.org/abs/2508.02040
- Zagier, Special values and functional equations of polylogarithms, in Structural Properties of Polylogarithms (1991), 377–400. https://people.mpim-bonn.mpg.de/zagier/files/tex/LewinPolylogarithms/fulltext.pdf
- Nakamura and Shiraishi, Landen's trilogarithm functional equation and l-adic Galois multiple polylogarithms (2025). https://arxiv.org/abs/2210.17182
- Amdeberhan et al., Integrals of powers of loggamma, Proceedings of the AMS 139 (2011), 535–545. https://www.math.tulane.edu/~vhm/papers_html/lg-subm.pdf
- Bailey, Borwein, and Borwein, On Eulerian log-gamma integrals and Tornheim–Witten zeta functions, The Ramanujan Journal 36 (2015), 43–68. https://www.davidhbailey.com/dhbpapers/log-gamma.pdf
