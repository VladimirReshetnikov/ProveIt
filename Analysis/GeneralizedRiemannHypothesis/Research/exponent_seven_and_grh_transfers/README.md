# The exponent-seven census and four transfers from the Lean proof of Dirichlet GRH

Start with **exponent_seven.pdf**. Its eight pages contain the field and order classification, the finite-exclusion and analytic arguments, all 33 field discriminants and seven additional order discriminants, and references to the prior census, its published gap and the work in ProveIt. The CSV gives the group and generators as primitive positive definite binary quadratic forms for each order.

The classification combines published results, quadratic Dirichlet GRH, a mathematical argument, and reproducible finite computations. The upstream formal theorem concerns Dirichlet L-functions. Its repository and the verification record are cited in the main note. This package gives a source-level analysis of that development. The new proofs have not been formalized in Lean or independently peer reviewed.

## Reproduce the main proof

Run these commands from the extracted directory, using Python without optimization so that assertions execute. The calculation used Python 3.12.14, NumPy 2.3.5, SymPy 1.14.0 and GNU coreutils 9.7. NumPy is used only for exact residue masks and candidate selection. SymPy is needed for the sampled cross-check. Put a proof-enabled GNU coreutils 9.7 executable named factor on PATH. The factorization backend and binary hash are documented in evidence/factor_version.txt.

| Command | What it checks |
| --- | --- |
| `python3 checks/equal_norms.py --workers 4` | All 256,686 unordered prime pairs for equal coefficients. Every one of 191,603 candidates above the threshold has a contradiction. |
| `python3 checks/ratio_norms.py --workers 4` | The 45 reduced unequal ratios. All 231,471 divisor candidates from 1,963,144 locally eligible ordered prime pairs have a contradiction. |
| `python3 checks/explicit_bound.py` | Rational enclosures for all fourteen explicit-formula inequalities. Every forced lower bound exceeds the top of its interval. |
| `python3 checks/check_class_groups.py` | Powers all 364 classes in the 40 orders, verifies the proposed generators and regenerates class_groups.csv. |
| `python3 checks/verify_small_range.py` | Enumerates every order discriminant through absolute value 118,843 and recovers exactly the recorded 40. The larger previously enumerated field range is covered by the cited EKN theorem. |
| `python3 checks/review_bounds.py` | Independently computes the fourteen analytic margins at 65-digit working precision. The primary rigorous analytic certificate is explicit_bound.py. |
| `python3 checks/review_masks.py checks` | Independently reconstructs the 48,492 local masks and verifies the complete eligible pair sets. |
| `python3 checks/crosscheck_ratios.py checks` | Compares independently generated arithmetic and divisor results on a reproducible sample of 1,800 ordered prime pairs and ratios. |

The first two commands perform the exhaustive factor and divisor searches. Their worker count can be changed. The retained transcripts are in **evidence/**. Its repository manifest identifies selected Lean source files at commit 72fead102f663d5c7a407964a13dc0cf9d977207. The notes link to the earlier ProveIt reports at commit d31039a48d963692e5a5176f47b6603fc9e9d9cf.

## Companion notes

| PDF in other-results/ | Scope and reproduction |
| --- | --- |
| local_specialization.pdf | Exact obstruction cost for simultaneous torsion evaluations over finite abelian local fields. Its LaTeX source inputs quadratic_towers.tex. Run eighth_roots.py, check_balancing.py and check_lower_shells.py for the finite checks. |
| sparse_places.pdf | Exact criterion for the primes at which the sparse-place construction can work. Run verify_sparse.py for the explicit 120-place construction, sieve and primality certificate. |
| signed_zero_decoder.pdf | A rigorous stopping rule for reconstructing two integer parameters from a single sufficiently high band of signed zero data. Run check_decoder_example.py to check the worked precision budget. The example checks inequalities and does not compute any zeros. |
| deep_rh_exceptional_sets.pdf | A quantitative exceptional-set theorem for a fixed character at the central Euler product. The proof is analytic. The full deep Riemann hypothesis remains open in this analysis. |

The companion checks use the Python standard library. For example, run `python3 other-results/verify_sparse.py` from the extracted root. Rebuild a PDF by running pdflatex twice on the matching source from its own directory with a standard LaTeX installation. To verify the archive files after extraction on a system with GNU coreutils, run `sha256sum -c SHA256SUMS`.
