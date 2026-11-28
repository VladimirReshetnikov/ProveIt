# Exponentially smaller fields detecting nonabelian Riemann hypotheses

Research extension for the ProveIt GRH project, 27 November 2026.

**Result.** If E/k is Galois and its group contains A_n, n>=5, let r=floor((n-2)/3) and delta=1 when n-3r=4, else 0. There is an explicit abelian H=C_3^r x C_2^delta with K=E^H and

    ord(zeta_K) <= ord(zeta_E) <= 3^delta 5^r ord(zeta_K)

at every complex point other than 1. The degrees in the S_n case are n!/(2^delta 3^r), versus the previous n!/2. Consequently the two Riemann hypotheses are equivalent, unconditionally. An explicit nonnegative Frobenius statistic gives an equivalent one-sided prime criterion. An S4 two-field result and small-degree obstruction for this positivity method are also proved.

This solves the repository's question `nab:q:lowdegree` in the stated range, not nonabelian GRH itself. The multiplicity constant and subgroup size are not claimed globally optimal.

## Contents

- `detector.tex` — full mathematical proof, literature and repository references.
- `detector.pdf` — compiled paper.
- `verify.py` — standard-library Python verifier; exact induced-character computations and tower class-coefficient checks.
- `verification.json` — generated results, including degrees and multiplicity bounds through n=60.
- `SOURCE_AUDIT.md` — source locations, blob hashes, assumptions, limits.
- `build.sh` — rebuild PDF and rerun verifier.
- `SHA256SUMS` — integrity hashes of the delivered files.

## Reproduce

Use Python 3.8+ and a LaTeX installation with standard AMS, Latin Modern, geometry, booktabs, enumitem, microtype, xcolor and hyperref packages. From the extracted directory:

```sh
python3 verify.py
bash build.sh
```

The verifier evaluates every group element of A5, A4 and S4; then it checks 8,529 tower class coefficients in exact rational arithmetic for 5<=n<=60. Symbolic induction proves the unbounded result. No floating-point approximations or numerical zero search enter the proof. The code is not a Lean formalization or a check of the upstream GRH proof.
