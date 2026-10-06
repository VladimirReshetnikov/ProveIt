Finite candidate-budget verification
====================================

Run with Python 3, NumPy, SciPy, and Matplotlib:
    python verify_finite_budgets.py

The script has two independent roles.

1. Exact verification on small finite probability spaces
   - Enumerate every binary word for N = 1,...,10, sort its exact rational
     probability, and compare every candidate-budget K against the
     Hamming-layer formula at p = 1/10, 1/3, and 1/2.
   - Enumerate nonidentical products with p_i = 1/(i+3), i = 0,...,7,
     and check all available budget values for all pairs of truncation
     lengths against the projection/modal-extension inequality.
   - Compare selected exact answers with the floating evaluator used
     for the plots. Counts and numerical error are recorded in JSON.
   - For N = 1,...,10, build the parity-dependent extremizers for the
     largest atom under pairwise independent fair bits. Enumerate all
     words and verify normalization, the maximal atom, every marginal,
     and all four outcomes for every pair. Verify the integer quadratic
     dual majorant at every possible Hamming weight and its exact
     binomial expectation. The sharp answer is 1/(N+1) for odd N and
     1/(N+2) for even N.

2. Reproducible numerical illustrations
   - sparse_budget_staircase.pdf: p = 1/N. Left: finite capture curves
     against log_N K and their Poisson staircase. Right: the multiplier
     window K approximately kappa N^r, for r = 1 and r = 2.
   - fixed_bias_normal_transition.pdf: p = 0.1, standardized budget
     s = (log K - N h(p) + (log N)/2)/sqrt(N v(p)). Finite capture
     curves tend to the normal cumulative distribution function.
   - Each figure is also exported as PNG for inspection.
   - Full plotted data and a compact sparse convergence table are CSV.

The exact finite checks are evidence against implementation/formula
errors. They do not verify the infinite probability proofs, simulate a
nonstandard model of arithmetic, or establish priority or novelty.

The optimal-atom ranking and fixed-bias normal source-coding expansion
are classical; see Kontoyiannis and Verdu, arXiv:1212.2668, and the journal
version in IEEE Transactions on Information Theory 60 (2014), 777-795,
DOI 10.1109/TIT.2013.2291007. The Poisson staircase follows directly from
the exact layer formula and the binomial-to-Poisson limit.

The pairwise atom bound is also classical: substitute p=1/2 in
Benjamini, Gurel-Gurevich, and Peled, On K-wise Independent Distributions
and Boolean Functions, arXiv:1201.3261, Proposition 25, equation (12).
They credit the general closed-form bounds of Boros and Prekopa (1989).
