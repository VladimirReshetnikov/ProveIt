# Prime counting in intuitionistic primitive recursive arithmetic

Open **prime-counting.pdf** for the complete argument. The editable entry point is **prime-counting.tex**. The section files must remain together in the sections directory.

## Where to start

- Sections 1–4 give the prime indicator, inverse rank, arithmetic progressions, survivor and factorial formulas, Golomb's theorem, and finite midpoint inversion.
- Sections 5–7 give weighted counts, both partial summations, the Mellin transform in the half-plane of absolute convergence, and the trivial-zero correction.
- Sections 8–12 give growth bounds, the arithmetic PNT and stronger asymptotics, the exact global maximum at 113, and the smooth Riemann count.
- Sections 13–15 prove the exact logarithmic-integral cutoff, compare the numerical source claims, and give conditional short-interval results.
- Section 16 identifies proofs in Lean and the remaining steps in the first-order proof calculus.

The exact checks identify six consecutive failures of the displayed three-term lower bound at 88783 through 88788. The stated 0.9487 upper bound for the kth prime also fails at k = 39017. The report gives certified intervals for both corrections.

## Reproduce the report and arithmetic

With a standard TeX Live installation, Python 3.9+ and a C++17 compiler, run from this directory. Use the ordinary Python interpreter with assertions enabled.

~~~sh
latexmk -pdf -interaction=nonstopmode -halt-on-error prime-counting.tex
c++ -std=c++17 -O3 -Wall -Wextra -pedantic checks/prime_table.cpp -o /tmp/prime-count-ipra-table
/tmp/prime-count-ipra-table > verification/prime_table.txt
python3 checks/approximation_table.py
python3 checks/finite_bounds.py
python3 checks/nth_bounds.py
python3 checks/certify_li.py
python3 checks/golomb_check.py
~~~

The C++ program defaults to exponent 14. An optional smaller exponent runs a prefix of the table. The independent quotient-sieve check covers exponents 1 through 10. The approximation-table script reads the full 14-row receipt. The Python verifiers use integer or rational interval arithmetic for all asserted comparisons. The sieve and reciprocal identities in the paper explain the correctness of the two counting algorithms. Transcripts are in **verification/**.

## Lean

Five independent modules compile with Lean 4.19.0 and Std. Run them in any order. They use no additional packages.

~~~sh
lean lean/Counting.lean
lean lean/Sieve.lean
lean lean/Inversion.lean
lean lean/ChebyshevKernel.lean
lean lean/Growth.lean
~~~

The verification transcript includes the key theorem axiom reports. The executable definitions and proofs are in the host language. The PR bounds and induction invariants to translate them into the first-order system are in the paper.

**lean/ProveItPNT.lean** is a separate client of the object calculus. Its imported arithmetic PNT lives in ProveIt at revision **a9c0f1949be61679ed2e219b97dc42ecb7ae91a9**. In a checkout of that revision use its root Lake environment and pinned toolchain **Lean 4.32.0**. The following commands give the replay path, with the last path replaced by this archive's absolute path.

~~~sh
lake build IPRADerivations.AnalyticNumberTheory.FinalPNT
lake env lean /path/to/prime-counting-ipra/lean/ProveItPNT.lean
~~~

The optional client and its external dependency closure were source-inspected. The five standalone modules and the numerical checks were run for this report. The quantitative logarithmic-integral and theta estimates used for the finer asymptotics come from a separate human proof packet identified in Section 10. The gap implications in Section 15 state their numerical hypotheses explicitly.
