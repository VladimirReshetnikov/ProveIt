# Bounded-excess positive filters for Dirichlet zero spectra

Research note, 27 November 2026. Intended as a standalone candidate contribution to ProveIt/Analysis/GeneralizedRiemannHypothesis, not committed to the repository.

## Result

For a symmetric multiset of nonzero frequencies with positive counting function
`N(T) = a*T*log(T) + b*T + O(log(T+2))`, `a > 0`, let `H(B,L)` be the smallest half-width of a probability measure cancelling all frequencies through `B`, with multiplicities, and bounded in Fourier magnitude by `exp(-L)` outside `[-B,B]`.

The paper proves **H(B,L) = L/B + pi*a*log(B) + O(1)**, uniformly in `L >= 0`. The error depends on the fixed multiset. This answers the first part of the question headed “Second-order term of the support” in `Article/sections/fil.tex`. The proof is unconditional for frequency multisets. For a conjugation-closed family of `d` primitive Dirichlet characters the coefficient is `d/2`. The exact second-order constant remains open in this work.

The construction has a uniform exponential-moment proxy, enabling a common averaging rule for all reduced residue classes, with support half-width `(phi(q)/2)*log(log X) + O_q(1)` and corrected ramp error `O_{q,m}(X^(-m-3/2))` for any fixed nonnegative integer `m`, under Dirichlet GRH. The correction includes finite imprimitive Euler factors and residues at zero and the first `m` negative integers.

## Files and reproduction

- `paper.tex`, `paper.pdf`: self-contained mathematical manuscript; classic analytic number theory is cited for the zero count and explicit-formula contour estimates.
- `SOURCE_AUDIT.md`: retrieved source snapshots, comparison, and scope.
- `FORMALIZATION_PLAN.md`: decomposition for future Lean work, not a checked formalization.
- `checks/verify.py`, `checks/results.json`: compressed synthetic bin-count regression and numerical interpolation tests.
- `checks/allocate.py`: finite exact-rational allocation routine and a small combinatorial example; no numerical zero computation.
- `checks/allocation_example.json`: reproducible example.
- `build.sh`: compile LaTeX twice and run the two checks; `requirements.txt`: Python dependency.
- `SHA256SUMS`: checksums of delivered files (not of itself).

Run `bash build.sh` in a scratch copy. It needs Python 3.11+, NumPy and a standard pdfLaTeX installation with Latin Modern and AMS packages. No external data, network access or Lean project is needed for the regression checks. Numerical tests do not establish the general theorem; its proof is in the manuscript.

## Important boundaries

The exact constant in the bounded-excess problem is not obtained. The explicit upper constants are intentionally conservative, and the construction is not optimized for small heights. Only the relevant portions of the 982-page merged article and the upstream interface were examined, not its entire proof corpus. No independent Lean verification of the new result was attempted. The brief literature comparison is not a priority certification. No claim is made to solve a separate prominent named conjecture or nonabelian GRH.
