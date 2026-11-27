# Source audit (26 November 2026)

GitHub connector reads, readable edition of https://github.com/lsernau/grh-lean (default branch; individual blob SHA identifiers):

| Path | Blob SHA | Use |
|---|---|---|
| README.md | fdca72cbfa3557506543b662317267897e0058a0 | Scope, status and build instructions |
| grh/README.md | 68cd862687bac1dadf3f14dc7266365e5c8b1ec4 | Theorems and reported checks |
| grh/GUIDE.md | c2acf9584b58efcb39ac1d668d25c107c3e76a0b | Theta-lift architecture and ramp statistic |
| grh/src/Statements.lean | 1cd1bce93344065936b2b392b23306254e0785ef | Mathlib proposition types |
| grh/src/Main.lean | 1adf4187a938510363cdb0dde0a6d628ff39c600 | The five endpoint theorems |
| grh/src/New/Reduction/MainInequality.lean | 97f83ab52b2feb420e952a2722b4cef454b9e579 | Header, theorem and start of proof (lines 1–110) |
| grh/src/New/Reduction/OneSidedBound.lean | 99e5240de112527b739068b692e5007720d310c1 | Ramp and one-sided bound (lines 1–110) |
| grh/scripts/PrintAxioms.lean | ec5adcfd7baeff36130db9a763720ba1a6567c57 | Axiom-check script |

No repository files were modified. The upstream build/checks are reported, not independently rerun. This note relies only on the stated GRH conclusion and classical analytic number theory, not a new use of the internal theta-lift lemmas.

Web sources inspected:
- https://en.wikipedia.org/wiki/Riemann_hypothesis — formulation, proof announcement and consequences/criteria.
- https://en.wikipedia.org/wiki/Explicit_formulae_for_L-functions — standard normalization for zeta.
- https://jtnb.centre-mersenne.org/item/10.5802/jtnb.920.pdf — H. Cohen, explicit formula, Theorem 7.1 (search extract).
- https://web.williams.edu/Mathematics/sjmiller/public_html/math/papers/DirichletZeros_DFandSJM_240arxiv.pdf — Dirichlet zero-statistics paper, formula (3.2) (search extract), checks gamma normalization and induced conductor treatment. Only the extracted formula was consulted, not a full paper audit.
- https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf — chapter 11, Lemma 11.4 (search extract), local zero count.
- https://doi.org/10.1112/jlms.12785 — Masatoshi Suzuki, screw functions and positive kernels for RH.

Related-work search was limited; no publication priority is asserted. The theorem and its sharpness proof are fully specified in paper.tex; numerical examples are independent illustrations rather than proofs.
