# What Dirichlet GRH settles beyond the zero theorem

Open **report.pdf** for the research note. **report.tex** is the entry point to the editable LaTeX sources. The note develops applications to primes in geometric intervals, a divisibility question of Pomerance, additive representations, and even-degree isogeny uniformity. Its final analytic result gives a one-sided criterion for the remaining Dedekind-zeta zero problem. The proofs of the new deductions are on paper. The executable checks concern finite computations.

## Rebuild the paper

From the extracted directory with a standard TeX Live installation, run twice:

    pdflatex -interaction=nonstopmode -halt-on-error report.tex

Keep all the section files beside report.tex. References are embedded hyperlinks.

## Reproduce the finite computations

Use Python 3.10+ with assertions enabled and a C++17 compiler supporting 128-bit integers (GCC or Clang). From the extracted directory run:

    python3 reproduce.py

This checks the supplied outputs byte for byte. The C++ binaries are built in a temporary directory. Checking the provided high-range certificate needs only Python's standard library. Running checks/make_large_certificate.py to regenerate the JSON certificate also requires SymPy. Run the generator in a copy of the extracted directory to preserve the supplied JSON.

| Programs in checks/ | What they establish |
| --- | --- |
| prime_plus_cube_multiple.py | Least-prime and primorial bounds, complete enumeration of the 62 exceptions, independent bitset check and the seven square exceptions |
| progression_windows.cpp | Two prime windows, each covering all 144,390,310 reduced pairs for moduli 45,001 through 50,000 |
| least_primes.cpp | First primes in class 1 for prime moduli through ten million and earlier primes at the required 671,350 prime powers |
| isogeny_sieve.py | Finite group cycle shapes, 66 candidates through 253,507 and the explicit endpoint tetrahedral field |
| simultaneous_witness.py | A single tetrahedral sextic field meeting the local test for all 66 candidates at once, using 5,093 prescribed primes |
| cubic_tail.cpp | Exhaustive exclusion above 253,507 through 11 trillion, using the strict integer inequality |
| verify_large.py | Independent proof of coverage above 100 billion using large_certificate.json and exact endpoint inequalities |
| alternating.py | Exact cycle partition calculations and an independent enumeration of small group actions |
| rigidity.py | Exact Chebotarev density and mean-square formulas in four example permutation groups |

The two large parameter files each give A and B on separate lines for t = A/B. To regenerate them, pass --write-parameter to the corresponding field checker in a copy of the archive. Ordinary verification reads them without modification. The 66 primes pass a necessary arithmetic condition. Existence of an elliptic curve at each listed prime is a separate question.

## Source identity

The upstream repository is https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207. With a checkout containing that commit, run:

    python3 checks/source_identity.py /path/to/grh-lean

The expected transcript is checks/source_identity.txt. The report uses Andrew Sutherland's independently published Lean build and kernel-replay records at https://math.mit.edu/~drew/shortgrh/. The local work checked the pinned source. The downstream deductions have written proofs.

The predecessor reports are in https://github.com/VladimirReshetnikov/ProveIt/tree/a92443f00663b1b8b3c233d17df0ad49dc4f2b2c/docs/incoming. The inspected ZIPs have the following Git blob IDs:

| Archive | Blob |
| --- | --- |
| grh-lean-transfers.zip | ecce11d7f5d919b3c5fed4e310a0ac56ebc0b456 |
| grh-transfer.zip | e8cba45276d211569726bc45eb24fee0d467b9a0 |
| grh_transfers.zip | 10ba8d2ac5e04809d70c468bc79ecdae31dedd19 |
| grh_transfer_analysis.zip | 68caedfbe84e88899ec097e2e1a7b92ae7657bd5 |
| grh_transfer_analysis_2026-11-25.zip | 2ec837a7b74075f98caa840b11ed467dd3e11509 |

Verify the contents against the included manifest with:

    sha256sum -c SHA256SUMS
