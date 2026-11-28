# Source audit

## Repository revision and provenance

Repository: https://github.com/VladimirReshetnikov/ProveIt/tree/main/Analysis/GeneralizedRiemannHypothesis/

Inspected using the GitHub connector. The relevant filter section was retrieved from `main`, then its blob was confirmed against the branch revision returned by GitHub:

`a4021de208d592a04419593436847c8e9db9b456`

Base path at the pinned revision:
https://github.com/VladimirReshetnikov/ProveIt/tree/a4021de208d592a04419593436847c8e9db9b456/Analysis/GeneralizedRiemannHypothesis/

| Path below base | Confirmed Git blob SHA |
|---|---|
| README.md | 7aa9ee91a8e41fdfeb62d46656b3bfed5d228b09 |
| Article/README.md | 5f6ec7d07882de55ae4e28213f89cffbbff5ace1 |
| Article/sections/fil.tex | 8f4e47a5e3e1ae4e2381aa3305c938e3906b35c4 |
| vendor/grh-lean/grh/src/Statements.lean | 1cd1bce93344065936b2b392b23306254e0785ef |

The project names `72fead102f663d5c7a407964a13dc0cf9d977207` as its upstream Dirichlet-GRH revision in https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207 . The scope of its statements is the Riemann zeta function and Dirichlet characters. The project README reports that its imported theorem is taken as given; the merged research article is not itself a verification of that theorem. We adopt the same input scope and do not independently certify that result.

## Direct starting points

All following links point to the inspected blob at the pinned commit:

- Positive theta kernels (`fil:lem:kernels`): https://github.com/VladimirReshetnikov/ProveIt/blob/a4021de208d592a04419593436847c8e9db9b456/Analysis/GeneralizedRiemannHypothesis/Article/sections/fil.tex#L1286
- Full-divisor positive filters (`fil:thm:global`): https://github.com/VladimirReshetnikov/ProveIt/blob/a4021de208d592a04419593436847c8e9db9b456/Analysis/GeneralizedRiemannHypothesis/Article/sections/fil.tex#L1362
- Prior endpoint bound (`fil:cor:endpoint`): https://github.com/VladimirReshetnikov/ProveIt/blob/a4021de208d592a04419593436847c8e9db9b456/Analysis/GeneralizedRiemannHypothesis/Article/sections/fil.tex#L1446
- Explicit open sharpness question: https://github.com/VladimirReshetnikov/ProveIt/blob/a4021de208d592a04419593436847c8e9db9b456/Analysis/GeneralizedRiemannHypothesis/Article/sections/fil.tex#L1651

The former upper bound is `2 pi d / Q_*`; the new paper proves `pi d / Q_*`. The earlier result for the double-exponential exponent `2/d` is retained. The new paper also proves the polynomial rigidity and exact moment criterion, which are stronger than a change of constant. The general argument does not use the old upper bound as a premise.

## Other inspected material and selection of problem

The main-branch introduction and `src.tex` were read for the proof architecture; selected headings and open questions in `nab.tex`, `grp.tex`, `dir.tex`, `gra.tex`, `gpi.tex`, `li.tex`, and `fil.tex` were surveyed. One alternative was to extend the symmetric-group zero-multiplicity comparison beyond degree 12 using monomial characters. A uniform proof was not established and no result from that alternative is claimed. The full-spectrum filter question was selected because it admits a complete analytic comparison and rigorous exact examples. Selected recent Research READMEs on Gram/Euler/zero filters, hidden forms and filters, Cayley filters, and Dirichlet coupled zeros/prime variances were also inspected for overlap. This was a targeted review, not a line-by-line audit of all 194 reports and pending contributions. A targeted literature search found classical positive theta kernels and standard entire-function results; no exact match to the endpoint formulation was located. This does not establish publication priority.

## Mathematical dependencies and verification limits

The proof relies on the critical-line input to identify all zeros of the central-zero-removed completed product. Classical inputs are the functional equations, order-one growth of completed primitive Dirichlet functions, Stirling asymptotics, Hadamard factorization, Phragmen–Lindelof, Fourier inversion, and the theta transformation. The paper proves the key analytic comparison, the moment equivalence by positive saddle integration, and the additional positivity and perturbation arguments. The arithmetic checker is deliberately limited to exact rational bookkeeping, not proof certification. There is no Lean implementation or formal proof-check result, and no claim of a proof of a different Riemann hypothesis. No change was pushed to the repository.
