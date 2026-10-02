# Degree four preorder support polynomials

The 17-page article proves rank-ultra-log-concavity for the unweighted support
polynomial of every finite preorder of actual degree at most four. Each feasible
ordered pair of disjoint endpoint sets is counted once, regardless of how many
matchings witness it. The proof combines ordinary structural reductions and exact
rational polynomial certificates for unbounded integer populations.

Start with article/preorder-degree-four.pdf. Its editable LaTeX source is beside
it. A standard TeX Live or MiKTeX installation with the listed LaTeX packages can
rebuild it; run `sh build.sh`, or run pdfLaTeX three times in article/.

To verify the new finite algebra and complete coverage:

    cd reproducibility
    python verify.py --mode fast

For independent bounded-core enumeration as well, use `--mode full`. Fixed
certificate replay needs Python 3.11+ standard library; full regeneration also
needs GNU g++ with C++17 support. Do not use Python -O, -OO or PYTHONOPTIMIZE.
The full mode's ten-element enumeration can be expensive. Read
reproducibility/README.md for precise trust boundaries and commands for the
included prior degree-three and bipartite rank-four dependencies.

All 76 final templates are covered. The four-attachment global ledger contains
50 rational identities and 15,408 square orbits. Ordinary theorem proofs,
independent audit records, counterexamples to stronger assertions, and exact
checkers are included. This is a computer-assisted mathematical proof; no Lean
formalization or global priority claim is made.
