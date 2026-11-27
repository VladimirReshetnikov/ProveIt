Detecting prescribed gaps between Dirichlet L-function zeros from finite Li data
26 November 2026

li_zero_separation.pdf     Paper, proofs, sources and numerical results
li_zero_separation.tex     Complete standalone LaTeX source
verify_collisions.py      Recomputes all four separation inequalities and signs
verify_zeta_moments.py    Recomputes the independent six/ten-moment zeta counts
collisions-output.txt     Output of the first verifier
moments-output.txt        Output of the second verifier
requirements.txt          Pinned numerical dependency

Reproduce the numerical certificates with a standard Python 3 environment:
    python -m pip install -r requirements.txt
    python verify_collisions.py
    python verify_zeta_moments.py

Run with assertions enabled (the default). The scripts use Arb enclosures and
need no zero tables or network access after dependency installation. Numeric
output can differ in its last printed digits on different library builds.
The programs verify the numerical inequalities, while the general statements
and the link from inequalities to zero spacings are proved in the paper.

Build the paper with a standard LaTeX installation:
    pdflatex li_zero_separation.tex
    pdflatex li_zero_separation.tex
