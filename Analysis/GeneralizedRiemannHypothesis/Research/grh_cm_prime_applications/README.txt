Applications of the Dirichlet GRH theorem in grh-lean
Research note | 25 November 2026

Begin with report.pdf. The main result is the four-term exclusion in
degree at least six; the candidate table is in Section 2. The main LaTeX file is report.tex. The other TeX
files supply sections and belong in the same directory. The paper includes
links to the pinned upstream repository, independent verifier's report and
primary mathematical literature. The applications and the sparse-twist
criterion are mathematical proofs on paper. The upstream RH and Dirichlet
GRH theorems were kernel-checked by the cited projects. Our local source
audit checks the byte identity of selected source files.

Rebuild with a normal TeX Live installation

    pdflatex -halt-on-error report.tex
    pdflatex -halt-on-error report.tex

The Python checks use Python 3.10 or later and its standard library.
The full discriminant census also uses the C++ commands below.
Use ordinary Python with assertions enabled. Run from this directory.

    python checks/verify_4075.py
    python verify_four_term.py
    python verify_cm_support.py
    python checks/verify_mills.py
    python checks/cube.py
    python checks/fourth.py
    python checks/verify_exception_lists.py

The final four-term candidate list (79 discriminants) is in
checks/four_term_candidates.tsv and printed in the paper.
checks/cm_small_unresolved.txt is the intermediate list before the final
complex determinant proof removes discriminant -4075.

The CM checker enumerates reduced forms for the stated examples and counts
7,958 certified denominators at the specified discriminant. The Mills
checker proves primality recursively, rejects the earlier composite
candidates, checks powers and intervals exactly, and emits outward-certified
decimal prefixes. Its data file includes all numbers and Pocklington
witnesses, including a 1,577-digit terminal prime. For the large witnesses beyond level seven, the search
used candidates P=1+kF with a smooth divisor F=2^u 3^v exceeding sqrt(P).
The verifier only needs the resulting integers and their certificates. The infinite continuation uses the RH gap theorem proved
in the literature. No infinite computation is required.

The additive scripts combine finite integer checks with the paper's tail
argument. Their .out files contain the complete exception lists. The
independent list verifier computes both sets again by binary shifts of a
prime bitset through two million. It compares every exception with both
lists. The reference transcripts are in checks/.

For the upstream source audit, use the networked checker

    python checks/audit_upstream.py

or a local clone

    git clone https://github.com/lsernau/grh-lean.git
    git -C grh-lean checkout 72fead102f663d5c7a407964a13dc0cf9d977207
    python checks/audit_upstream.py --checkout grh-lean

The expected Git blob IDs and the upstream audit transcript are included.
The C++ discriminant sieve can be rebuilt with g++ or clang++ (C++17,
including 128-bit integer support)

    g++ -O3 -std=c++17 checks/cm_range.cpp -o cm_range
    ./cm_range
    sh checks/run_cm_small.sh

To check the archive contents after extraction, run

    sha256sum -c SHA256SUMS

Incoming reports consulted at ProveIt revision
1e1728ad221d69e48fea09bf754b73422af44943 (docs/incoming). SHA-256 hashes

c79d85f7418b2f801f12d305a2f7f19e511a1c18113e7d14ef3c9b84df350b34  grh-lean-transfers.zip
6a2ea786df066953aa0b3ea774588ccc7f3d6096cfe4a37e74eeba52c90459fb  grh-transfer.zip
4a35c53b88d462224ae81463035f7344268e3910e0b9dc7728dae4be5d249099  grh_transfers.zip
