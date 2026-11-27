GRH transfer supplement, 26 November 2026

report.pdf        Two-page proof and provenance.
report.tex        Self-contained LaTeX source. Run pdflatex twice.
check_constants.py  Exact rational checks for the numerical margins
                    used in the proof (stdlib only, python3).
SHA256SUMS        Hashes of the report, source, check script and README.

The deductions are not formalized in Lean. The cited audit is for the
upstream Dirichlet GRH theorem, not the supplement. The centered
shrinking-window bound is related to, and weaker than, Zhao's
second-order estimate; the supplement gives explicit coverage of
arbitrary centers with a freely tunable bandwidth.
