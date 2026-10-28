# Anthropic ETH source update at the user-supplied PR head

Reviewed immutable head: `anthropics/formal-math@1a6eee293b9e00cb432eef6018a21f523623a9af`.
Source directory: `eth/`. This note is a source and statement audit, not an independently executed Lean build.

## Required correction to the earlier ProveIt review

The prior ProveIt copy `Computability/SubexponentialSAT/Research/claude-2o-n-3sat/eth.pdf` is an earlier 49-page manuscript that says a public location for the Lean development is still to be added. At the exact PR head the public development is present, with `MainResults.lean`, `Solution.lean`, its imported modules, the pinned toolchain, the comparison challenge, and checking scripts. The earlier description “formalization not publicly supplied” is now stale and must not be repeated.

The PDFs are not byte-identical:

| Copy | Bytes | SHA-256 |
| --- | ---: | --- |
| Earlier ProveIt `eth.pdf` | 868673 | `f0af035b6c87d04d3fcf07dae040df98029f4990c6493e3e9ab64c4ac714c0eb` |
| Public PR-head `eth/paper.pdf` | 900337 | `7af518b09342c967ea371c74b8989806684c5d02aabe5763ca08554aff5025a0` |

Both have 49 pages. A whitespace-token comparison of extracted text found substantial publication/provenance and formalization-scope updates, including the public link and revised module count; the displayed Main Theorem retains the same complexity order. This is a statement-level comparison, not a proof that every mathematical passage is unchanged. A layout-sensitive text diff is retained separately in `comb_review/anthropic/paper_text.diff` as temporary research evidence.

## What the public Lean statement actually says

`MainResults.lean` imports only Mathlib and defines the propositions, with no proof declarations. `Solution.lean` imports it and provides actual theorem terms:

- `MainResults.mainTheorem : MainResults.MainTheorem` is supplied by `CountedRoute.mainTheoremHolds`.
- `MainResults.ethIsFalse : MainResults.ETHIsFalse` is derived from that main theorem through `NamesInOrder.generalFormFollowsAsPropositions` and `Wrap.countingBoundImpliesFailureOfETH`.

The counting statement quantifies **one** deterministic Mathlib `Turing.FinTM2` multi-stack machine and **one** natural constant C before choosing k or the formula. Every stack alphabet is explicitly required to be finite. For k >= 1, n >= 4, at least two clauses, every declared variable occurring, and no repeated clause, it outputs the number of satisfying assignments in n+1 bits within

`floor(2^(C * min(k*m/sqrt(log2(m)), k^2*n*log2(log2(n))/sqrt(log2(n)))))`

machine steps. The constant does not depend on k. The statement uses lists of literals and clauses; a clause may be empty, repeat a literal, or be tautological, and permutations count as different clauses. Duplicate *clause lists* are disallowed. The occurrence and deduplication promises are relevant to absorbing input-reading work. Small or malformed inputs are outside this exact proposition and can be handled separately in a conventional implementation.

`ETHIsFalse` is the negation of positivity of the infimum of deterministic exponential-time coefficients for 3-SAT. Its definition covers arbitrary numbers of nonrepeated 3-clauses and all n. The stronger single-machine counting statement is available in addition to the every-positive-delta interpretation.

The source itself explains the remaining interpretation boundary: the formal theorem counts steps of the specified Mathlib machine and fixed binary encoding. Rewriting arbitrary external formulas into that encoding and simulating this stack machine on a word RAM are standard mathematical steps discussed outside the Lean statement. The bound contains an existential, unextracted constant C. It gives neither a normalized-wire coefficient comparable to 30.891 nor a polynomial-space claim.

## Checking status and deliberate challenge stubs

The toolchain is Lean 4.33.1; the README states matching Mathlib 4.33.1 and Appendix E identifies Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. The README supplies `lake exe cache get`, `lake build`, and `lake env lean scripts/PrintAxioms.lean`, and describes a Comparator/nanoda check.

The expected axiom set printed for both final theorems is `propext`, `Classical.choice`, `Quot.sound`. This is a claim/instruction of the public source; it was **not independently reproduced here**. Neither `lake` nor `lean` was on this environment's PATH during this audit. The source tree has 1050 development Lean modules plus the two checking scripts (1052 `.lean` files total).

`Challenge.lean` deliberately contains two `sorry` placeholders for the statements to be compared. Its header says nothing imports it, and the actual `Solution.lean` imports real proof modules instead. A source-text search found the only `sorry` occurrences in this challenge file (one documentation mention and two placeholders); no top-level `axiom` declaration matched the simple scan. A scan is not a substitute for kernel checking or dependency analysis. The presence of those intentional challenge stubs is not by itself evidence that the final theorems depend on `sorryAx`.

Appendix E and `proof/PaperIndex.lean` disclose differences from the printed proof: internal counted operations may be polynomial-time computations on a state with a stated size bound; transitions to Turing machines can raise time to a fixed power; intermediate budget strings and a computed exponent in [e_l,2e_l] are used. The endpoint still states actual Turing-machine steps. These differences preserve the asymptotic big-O rate but prevent extracting a matching explicit wire-normalized coefficient from the comments alone.

## Useful research interfaces

The public proof offers an independent architecture, not a replacement justification for the Cauchy-mode refinements.

1. **A parameterized crossing decomposition.** Definition 7 and Theorem A accept polynomially many integral pieces of the crossing `[x=v][y=u]`, with the sum of row and column factorization-bit lengths at most `4*rho*lambda + O(log lambda)`, explicit size bounds and an evaluation cost exponential in lambda. They yield a logarithmic denominator exponent `alpha = log2(1/rho)`. Theorem B supplies `rho=1/sqrt(2)`, hence alpha=1/2. The associated interfaces are `PiecesStatement.lean`, `AppRunningTimeStatement.lean`, `PiecesCountedStatement.lean`, and the `PiecesCounted` / `ExplicitCost` modules.
2. **An explicit route to an order improvement.** A construction satisfying all Definition 7 requirements with a fixed `rho < 1/sqrt(2)` would improve the power of log in this architecture. A formal declaration of a rank bound alone would not suffice: integrality, polynomially many pieces, uniform construction, entry magnitudes, and paid evaluation all matter.
3. **A tempting route already recorded in the source.** Appendix H observes that a compatible graded operator algebra with `log(dim V_E) ~ E^alpha` would give `rho=2^(alpha-1)`. Replacing the partition-growth exponent 1/2 by a smaller exponent is therefore already an explicit research suggestion in the public manuscript. It must not be presented as our new idea. Merely retaining square-indexed bosonic generators does not preserve the locality identities used in Lemma 9; that missing identity is the main obstacle to such an attempted construction.
4. **No automatic transfer of the new wire constants.** These pieces operate over exact integral crossing tensors and a clique regrouping framework. The ProveIt improvements use a finite-precision unramified 2-adic ring, mode-pair lists, and immutable creation-time tensor descriptions. Combining them requires a new interface theorem paying for the altered ring, oracle, degree, and encoding costs. The currently available sources do not establish it.

## Immutable source links

- https://github.com/anthropics/formal-math/blob/1a6eee293b9e00cb432eef6018a21f523623a9af/eth/README.md
- https://github.com/anthropics/formal-math/blob/1a6eee293b9e00cb432eef6018a21f523623a9af/eth/MainResults.lean
- https://github.com/anthropics/formal-math/blob/1a6eee293b9e00cb432eef6018a21f523623a9af/eth/Solution.lean
- https://github.com/anthropics/formal-math/blob/1a6eee293b9e00cb432eef6018a21f523623a9af/eth/Challenge.lean
- https://github.com/anthropics/formal-math/blob/1a6eee293b9e00cb432eef6018a21f523623a9af/eth/proof/PaperIndex.lean
- https://github.com/anthropics/formal-math/blob/1a6eee293b9e00cb432eef6018a21f523623a9af/eth/paper.pdf

Audit completed by source inspection and exact file hashes; no upstream supplied executable code or proof build was run.
