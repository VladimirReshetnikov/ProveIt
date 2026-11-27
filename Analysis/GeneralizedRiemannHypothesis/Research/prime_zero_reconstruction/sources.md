# Sources and review record

Accessed 26 November 2026. The GitHub connector returned repository metadata, root tree, file content, and the main commit SHA `72fead102f663d5c7a407964a13dc0cf9d977207` (25 November 2026). The following file blobs were directly inspected:

| Path | Blob SHA | Relevance |
|---|---|---|
| README.md | fdca72cbfa3557506543b662317267897e0058a0 | Scope, editions, status |
| grh/README.md | 68cd862687bac1dadf3f14dc7266365e5c8b1ec4 | Five exports, checks and build requirements |
| grh-compact/README.md | 85d43d83a7fa3b496968ce9216f4a7d75e44e84a | Compact edition and checks |
| grh/GUIDE.md | c2acf9584b58efcb39ac1d668d25c107c3e76a0b | Overview, definitions, lattice comparison and scales |
| grh/src/Statements.lean | 1cd1bce93344065936b2b392b23306254e0785ef | Precise zero-location definitions |
| grh/src/Main.lean | 1adf4187a938510363cdb0dde0a6d628ff39c600 | Exported theorems |
| grh/scripts/PrintAxioms.lean | ec5adcfd7baeff36130db9a763720ba1a6567c57 | Axiom-report commands |
| grh/src/New/Reduction/MainInequality.lean | 97f83ab52b2feb420e952a2722b4cef454b9e579 | Inspected first 100 lines, including statement and explanatory header |
| grh/src/New/Reduction/OneSidedBound.lean | 99e5240de112527b739068b692e5007720d310c1 | Inspected first 220 lines, including one-sided bound and scale lemmas |

Repository: https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207

The analysis uses the right-half-plane and critical-strip exports, with the classical functional equation. It does not transfer unproved analogies from the arithmetic geometry of the full Lean proof. The upstream readme reports kernel checks and external checks. Independent check records are available at https://www.math.uwaterloo.ca/~mrubinst/alpoge_claude_grh/. We did not rerun these checks.

The requested Wikipedia survey (https://en.wikipedia.org/wiki/Riemann_hypothesis) was read for its description of the announced proof, the explicit formula, prime-distribution consequences and analytic criteria (including Nyman--Beurling).

## Related literature search

Queries included Dirichlet L-function zeros reconstructed from prime-counting autocorrelation, prime race autocorrelation, and almost periodicity of prime error terms. Related results include:

- Akbary, Ng, Shahabi, *Limiting distributions of the classical error terms of prime number theory*, Q. J. Math. 65 (2014), 743–780: https://arxiv.org/abs/1306.1657 ; https://academic.oup.com/qjmath/article-abstract/65/3/743/1565364. This provides the relevant almost-periodic and limiting-distribution background.
- Rubinstein and Sarnak, *Chebyshev's bias*, Experimental Mathematics 3 (1994), 173–197, classical prime-race framework.
- Montgomery and Vaughan, *Multiplicative Number Theory I: Classical Theory*, Cambridge (2007), standard analytic properties and explicit-formula background.
- Davenport, *Multiplicative Number Theory*, 3rd ed. (2000), standard Dirichlet L-function theory.

No exact match for the countable character-labelled reconstruction from one autocorrelation was located in this limited search. It is a proposed novel synthesis, not a proven priority claim. Its main limitation is severe precision requirements and the need for exact infinite averages; no uniform finite-data complexity bound is claimed. The full complex autocorrelation is needed, not merely its real part.
