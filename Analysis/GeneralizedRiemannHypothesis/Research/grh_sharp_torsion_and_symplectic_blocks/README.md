# Beyond Dirichlet GRH

Open **report.pdf** for the 12-page paper. The main LaTeX file is **report.tex**. It includes the five section sources in this directory and the chart in figures/rank_laws.pdf.

## Results

* Section 2 gives the sharp exponent for a fixed Gauss valuation, exhibits a polynomial that attains the bound, and computes the exact threshold for a prescribed finite set of primitive orders. The result extends to integral power series and independently selected coordinates.
* Section 3 determines the exact zero-tolerance obstruction cost for polynomials over any finite p-adic field. At positive rational tolerance a finite congruence procedure computes it. For primitive fourth roots, a quadratic-defect formula gives the complete answer. Two fields with the same ramification and cyclotomic intersection already separate at tolerance 1/4.
* Section 4 transfers the positive-type estimate to random symplectic matrices, proves a uniform range for arbitrary rectangular compressions, and obtains the exact limiting total variation distance for a family of isotropic blocks at each fixed deficit.
* Section 5 computes the information surviving a support restriction on Frobenius types, including the cost of mixed character signs for A5. For the splitting field of X^4-X-1 the analytic RH assertion reduces to an explicit prime inequality. A proof of that inequality remains open.

The two local results and the random-matrix result use ideas inside the Lean proof. The direct use of Dirichlet GRH in Section 5 establishes RH for the abelian base field. The downstream results are mathematical proofs accompanied by finite checks. This work does not include a Lean formalization of them or a fresh build of the upstream projects. The paper identifies its closest known and supplied precedents. Broader publication priority is unverified.

## Reproduce

A standard current TeX Live installation with pdfLaTeX suffices to build the paper. The chart PDF is included.

    pdflatex -halt-on-error report.tex
    pdflatex -halt-on-error report.tex

The five checkers require only Python 3 (3.8 or newer is recommended; tested on this workspace's Python 3). Run from the extracted archive directory.

    python3 checks/check_fixed_radius.py
    python3 checks/check_local_fields.py
    python3 checks/check_symplectic.py
    python3 checks/check_support.py
    python3 checks/check_quartic.py

checks/results.txt records their outputs. The fixed-radius script enumerates small root configurations, and the local-field script checks all residues needed for the seven quadratic extensions at order four. The symplectic script enumerates small isotropic frames and checks exact rank counts. The support script computes the rational A5 table. The quartic script obtains the factorization types by polynomial gcds and checks their parity against the quadratic character. These are finite checks; the proofs for general parameters are in the paper.

To regenerate the chart, install Matplotlib and run:

    python3 figures/plot_rank_laws.py

lean_sources.tsv gives Git blob hashes and permanent links for the Lean source files. prior_archives.tsv lists the 31 GRH-related incoming archives compared, at ProveIt revision 274841c1cb137aafbb60ab5f519c51fd42eee98e. SHA256SUMS records the integrity hashes of the other files in this directory.
