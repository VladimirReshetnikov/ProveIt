# Measure section: provenance and status

Repository snapshot: `b2341af5370cd8a43f72ebb2341c0d7d7395b634` (read through the GitHub plugin).

## Directly inspected prior sources

- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/probability/expected_value_ipra_2026-11-16/paper/sections/10_effective_integration.tex`, blob `465752843def5108f008a5ed414db890cd2905cd`. Already contains effective L1 simple-law names, expectation extension, finite-law couplings, compact quadrature, absolute spatial tails, density comparisons, and a witnessed forward absolute-continuity treatment. The present report does not claim these as new.
- `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Analysis/GridIntegral.lean`, blob `6487786ac131df651294257474bf82190e15997d`. Provides genuine `Γ ⊢[PRAAx]` cell and accumulated grid inequalities. Its header expressly leaves multidimensional grids, contracts producing the cell error, and passage to regular names outside that module.
- `docs/proofs/foundations/ipra_abstract_analysis_2026-11-20/sections/hilbert.tex`, blob `1d3e1ec64d2926f9c3099d5076159e72541c770d` below `Logic/PrimitiveRecursiveArithmetic`: completion of polynomial pre-Hilbert spaces and a Green operator, rather than a general L1 measure algebra.
- `docs/proofs/foundations/ipra_continuous_framework_2026-11-20/sections/analysis_topology.tex`, blob `53e9c2b46de237470b15ebf96ae0902bde414fe4`: uniform quadrature, ODE realization, and holomorphic Cauchy transforms.
- `docs/proofs/foundations/ipra_continuous_framework_2026-11-20_2/paper/sections/03_function_spaces.tex`, blob `03d36ddfc11993f5a5885156e425635e50fa26c1`: no general measure/DCT/Fubini development found.
- `docs/proofs/foundations/ipra_continuous_mathematics_2026-11-20/sections/function_spaces.tex`, blob `17158b2c4af5a0bd1c065c54ac0c2adf42456687`: no general measure/DCT/Fubini development found.

The novelty claim is a concrete extension of the audited repository interfaces, not a priority claim in constructive analysis. Working on one coherently refinable event algebra supplies joint arithmetic on named functions. Pairwise couplings remain adequate for the expectation estimates already proved, but do not alone specify all simultaneous random-variable operations.

## New fully written human arguments

1. Integration, norm, lattice operations and bounded multiplication on a coherent rational simple-function completion; measure-algebra completion by the symmetric-difference pseudometric.
2. Countable union / additive series when an explicit primitive-recursive finite-tail bound is supplied.
3. Finite Vitali estimate and full name-level budget `4σ + 2τ + δM + 2Kη`.
4. Uniform clipping tails from the simple approximation of one L1 majorant; no separate amplitude-tail oracle is needed.
5. Represented dominated convergence with an explicit convergence-in-measure certificate (not from bare pointwise convergence).
6. Exact unbounded moving-spike example and an L1-multiplication counterexample.
7. Fubini by extending the exact finite row/column contraction.
8. Reduction of infinite-measure integrals to finite regions with explicit uniform spatial tails.

Every result is conditional on its displayed representation and primitive-recursive contract proofs. The section supplies the finite invariants and a Lean/object-language proof order; it does not claim that the complete derivations have been implemented.

## Primary outside sources checked online

- Iosif Petrakis and Max Zeuner, *Pre-measure spaces and pre-integration spaces in predicative Bishop–Cheng measure theory*, LMCS 20(4:2), 2024. https://lmcs.episciences.org/14409 ; DOI https://doi.org/10.46298/lmcs-20(4:2)2024 . Used only for historical context: predicative L1 completion exists in a more general constructive framework, not as an iPRA conservativity theorem.
- Jeremy Avigad, Edward T. Dean, Jason Rute, *Algorithmic randomness, reverse mathematics, and the dominated convergence theorem*, APAL 163 (2012), 1854–1864. https://arxiv.org/abs/1106.0775 . Its precise reverse-mathematical formulations are not silently equated with every possible encoding of DCT.
- The same authors, *A metastable dominated convergence theorem*, JLA 4:3 (2012), 1–19. https://doi.org/10.4115/jla.2012.4.3 ; https://arxiv.org/abs/1108.4400 (arXiv title: *Metastable convergence theorems*). General bounds use recursion along unsecured-sequence trees; invoking this theorem does not by itself establish primitive-recursive bounds.

## Reproducible finite checks

Run `python3 code/measure_reference.py --output evidence/measure_checks.json` from the package root. Exact Fraction arithmetic checks 33,750 two-cell Vitali cases, 81 rectangular Fubini cases, and ten moving-spike identities. These are implementation checks, not substitutes for the symbolic proofs and not formal iPRA derivations.
