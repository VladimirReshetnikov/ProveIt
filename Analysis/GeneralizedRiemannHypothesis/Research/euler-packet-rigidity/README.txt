Rigidity and gaps in Euler-factor matching
Dirichlet characters of odd prime order
27 November 2026

euler-packet-rigidity.pdf is the 11-page paper. Its standalone LaTeX source is
euler-packet-rigidity.tex. The figures are drawn directly in LaTeX.

The first theorem classifies the two lowest values of normalized prime
disagreement for every odd prime exponent and every rank at least two.
The second theorem gives the small-packet sharpness criterion.
Section 5 gives a complete five-factor spectrum at exponent seven and rank two.
Section 6 gives the two versions of the finite-interval estimate under
Dirichlet GRH. Section 7 records provenance and comparisons to prior work.

To rebuild with a standard TeX Live installation, run twice:
    pdflatex -interaction=nonstopmode -halt-on-error euler-packet-rigidity.tex

To reproduce the finite checks, use Python 3.9 or later and run:
    python3 checks/check_packets.py
    python3 checks/check_prime_gap.py
    python3 checks/check_difference.py
    python3 checks/nonsplit_prime_example.py

Expected output is in the corresponding .txt files. The expected output
for check_packets.py is checks/output.txt. No third-party Python packages
or external data are needed.

check_packets.py checks all 189,471 distinct unordered packet pairs in the
specified small planes and sizes and 103 explicit geometric constructions.
check_prime_gap.py checks normalized two-set examples at four odd primes.
check_difference.py checks the flat-difference bound on 24 rank-three
constructions, including equality cases. nonsplit_prime_example.py enumerates
every reduced residue class modulo 1247 and the primes through one million.

Repository snapshot
    VladimirReshetnikov/ProveIt
    c0f2782360ddffd79a20c6d828d582e214a2b8c3
Vendored upstream
    lsernau/grh-lean
    72fead102f663d5c7a407964a13dc0cf9d977207

The submitted theorem has a mathematical proof and finite checks. The Lean
declaration used for the analytic corollary is pinned in the paper.
