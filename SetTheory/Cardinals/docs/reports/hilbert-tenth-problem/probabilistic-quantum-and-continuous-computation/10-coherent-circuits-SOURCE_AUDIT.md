# Source and claim audit

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit read through the GitHub connector:
`ccfb084adaa2f32e8d2738a25f82a00377fb3a8c`.

The recursive tree and the Hilbert-tenth-problem directory were inspected. The main mathematical direct reads were:

1. `Computability/HilbertTenthProblem/README.md`.
2. `Computability/HilbertTenthProblem/Lean/Diophantine/MRDP.lean`.

The inspected theorem file explicitly states finite-polynomial MRDP with natural witnesses, input zero included, and the converse. The current manuscript uses this result only for its fixed-arity representation of unbounded positive-probability halting. No dependency on the repository's optimized universal-operation counts is needed.

Some code-search results were indexed at older commit `4e128356d0ef75308be8ed405d89aea2ffdb8a57`. They were used for navigation, not represented as a complete audit of the pinned commit. Searches for quantum/tensor Diophantine work were selective and do not establish that no relevant prior material exists anywhere in the repository.

No Lean build or transitive axiom audit was run for this package. The repository README's reports about such audits are not presented as newly independently verified facts.

## Established ingredients

- MRDP: Matiyasevich's classical theorem and the inspected ProveIt interface.
- Quantum amplitudes as differences of path counts: Dawson et al., arXiv:quant-ph/0408129, Quantum Information and Computation 5(2) (2005), 102–112.
- Tensor contraction simulation and width: Markov–Shi, arXiv:quant-ph/0511069, SIAM Journal on Computing 38(3) (2008), 963–981.
- Exact Clifford+T arithmetic/synthesis context: Giles–Selinger, arXiv:1212.0506, Physical Review A 87 (2013), 032332.
- Hadamard–Toffoli universality context: Shi, arXiv:quant-ph/0205115.
- One-way cluster-state computation: Raussendorf–Briegel, Physical Review Letters 86 (2001), 5188–5191.
- SAT completeness: Cook, STOC 1971, 151–158.
- Computable real representations and the exact-equality distinction: Weihrauch, Computable Analysis (2000).
- Classical almost-sure termination hierarchy: Kaminski–Katoen, arXiv:1506.01930, MFCS 2015.

The bibliography contains persistent identifiers and pinned repository URLs. Primary paper landing pages and relevant PDF passages were checked. Technical diagrams in consulted PDFs were inspected as page images. No source PDF is redistributed in this package.

## Constructions proved in the manuscript

The manuscript supplies complete proofs for the canonical signed-wire compiler, contraction profile and height bounds, four-coordinate cyclotomic lift, unique quadratic order comparator, exact circuit and graph-state branch certificates, and the displayed reductions. The important features of the assembled compiler are explicit natural witnesses, uniqueness for fixed finite data, preservation of interference, resource counts, and representation-aware scope.

The complexity consequence is **conditional**: a uniformly polynomial-size and polynomial-bit exact-zero certificate compiler would imply NP = coNP. No separation of those complexity classes is proved.

The one-gate approximation-name reduction is self-contained. All gates in its uniform family are valid rotations and individually have rational entries, but their inputs are fast Cauchy names, not uniformly supplied exact rational fractions. The result is about effective descriptions, not physical hypercomputation.

The unbounded almost-sure result embeds a known classical classification into the stated quantum-controller model. It is not claimed as a newly discovered classical theorem. Likewise, the existence of tensor simulation and quantum path-sum expressions is not claimed as new.

## Novelty limitation

The research contribution is the explicit synthesis and its full accounting. Searches of the repository and primary literature were not an exhaustive historical-priority review. The package does not claim a confirmed breakthrough on a longstanding named conjecture, nor a solution of finite-fold or single-fold MRDP. It is intended as a rigorous, testable research contribution and a basis for further formalization.

## Computational evidence

The standard-library prototype uses exact integer/rational arithmetic. It checks gate-state simulation against doubled networks, graph branch sums against an independent circuit realization and native factor networks, sign decisions against rational square-root enclosures, and norm multiplication against an independent coordinate formula. An independent exported-file checker shares no generator code.

These are finite implementation checks. General soundness, completeness, uniqueness, height, and non-enumerability claims rest on the mathematical proofs, not on the finite test counts.
