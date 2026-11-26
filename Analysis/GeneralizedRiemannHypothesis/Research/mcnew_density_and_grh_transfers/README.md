# A density separation for geometric progressions

Open **report.pdf** for the paper. The main result answers Nathan McNew's Question 7.4 in the 2015 Mathematics of Computation paper. The difference between the two suprema of natural densities exceeds 0.0001306. The proof and its finite computations are unconditional.

Theorem 4.1 gives restricted cases of McNew's Conjecture 7.2. The section on Frobenius events gives an exact binary-weight classification and a prime-counting criterion for Dedekind RH. The nonabelian prime estimate is an open obligation. Appendix A treats a proposed approach through Jensen polynomials and gives an exact finite obstruction for a model family of kernels.

## Reproduce

With Python 3.10 or later, run these commands from this directory. Leave assertions enabled. No third-party modules are needed.

    python3 checks/verify_separation.py
    python3 checks/check_exchange.py
    python3 checks/check_bridge.py
    python3 checks/verify_rankin.py
    python3 checks/verify_integer_ratio.py
    python3 checks/binary_detector_check.py
    python3 checks/verify_jensen.py

The first two commands independently prove the same local exchange inequality. One reads the list in replacement.txt. The other reconstructs it, checks equality of the lists, enumerates triples by their endpoints and proves a weighted vertex-cover bound. The third checks the explicit density gain by sieving primes. Each calculation has a corresponding results file. The integer-ratio construction is supplied as an explicit support, so verifying it requires no optimization software.

For the PDF, run pdflatex report.tex twice with a standard TeX Live installation. Keep frobenius.tex and jensen.tex beside report.tex. With a Unix SHA-256 tool, sha256sum -c SHA256SUMS verifies the archived bytes before any rebuild.

## Provenance and proof status

The evidence directory records the pinned Lean revision, source blob identifiers and the ProveIt manuscript inventory. The paper distinguishes results proved in the manuscript, published input and statements requiring a new prime-sum estimate. The added mathematics has paper proofs with exact executable checks. The upstream Lean build was not independently replayed in preparing this report. Historical priority of the new arguments has not been established.
