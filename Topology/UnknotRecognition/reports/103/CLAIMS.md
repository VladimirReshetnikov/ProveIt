# Claim ledger

This ledger accompanies the full proofs in `article/Relative_Top_Handles.pdf`. “Proved” means a mathematical argument in the article, with the stated hypotheses. It does not mean a formal proof-assistant development. Novelty is assessed against the inspected ProveIt source, ten incoming packages, and the cited primary literature; it is not an exhaustive priority claim.

## Proved mathematical results

| Result | Hypotheses and conclusion | Boundary |
|---|---|---|
| Exact source cap inventory | For a valid source triangulation and admissible normal vector, a zero-weight interior edge contributes the two source ends; each positive-weight extreme gap contributes one source end and one cut-boundary end. Repeated endpoint occurrences are retained. | Source rank and orientation charts are essential. Arbitrary supplied endpoint lists do not authenticate geometry. |
| Relative source top elimination | Every source three-handle can be cancelled; the resulting core is homeomorphic relative to the complete native parallelity interface. The same parallelity pieces can be reattached. | The protected set is the native interface, including its collars. Arbitrary inherited boundary patterns need a separate avoidance or transport theorem. |
| Universal source tree | One boundary-rooted source tree specializes to valid top traces for every admissible coordinate vector, including zero and one-sided components. | The theorem does not establish downstream optimality for general raw cancellation. |
| Linear structural scheduler | The queue uses linear work in the explicit bounded core. The extra trace has `O(t log(t+2))` bits, independent of coordinate magnitude. | Source validation, coordinate reading, and incidence reconstruction have separate polynomial bit costs. The full proof does not have constant size under scaling. |
| Abstract joint-forest criterion | Short capped rows give a graphic matroid. A complete joint strategy exists exactly when the two graphic rank inequalities hold. For forced long rows, use contraction after first requiring those rows to be a cap forest. | This is a specialization of classical matroid partition. Forcing all long rows into the top tree is a restricted strategy. |
| Exact abstract deficiency | The maximum rank deficit equals the least residual graphic nullity among eligible top trees, and the least number of additional arbitrary row deletions needed by that graph model. | Arbitrary row deletion is not thereby a legal geometric operation. A deficit is not a non-handlebody certificate. |
| Homological rigidity | After a fixed primal forest, uncapped parity matrices satisfy `A^T B=0`. In the actual short-row class, every top tree leaves cycle nullity `m-q-rank(A)=beta_2(K; F_2)`. With long and loop rows forced, the same conclusion holds whenever the entire mandatory set is a cap forest. | Do not apply parity to naively capped odd entries such as 3. The primal forest, geometric chain condition, and mandatory-row convention are part of the theorem. |
| Exact exceptional-row quotient | If the selected short-row graph is a forest, omission of the grounded component and contraction of free short components preserves all exceptional projections of stopping sets. The maximal source lift is the union with the minimal short subtrees spanning exceptional incidence sites and, in the grounded component, the ground vertex. | This is for fixed primal and top forests. A short cycle alone obstructs complete peeling, but that branch does not claim the full canonical stopping set from the cycle alone. |
| Finite column-pattern kernel | With `k` exceptional rows, equal nonzero capped column signatures can be merged, leaving at most `3^k-1` types and preserving all stopping row subsets. | Original forest and representative maps must remain available to lift source certificates. No bound on the number of kernels reachable by changing forests is proved. |

The unmarked existence of three-handle elimination is classical and is specifically credited to Jackson, Lemma 3.2. Unit-column completeness and stopping-core persistence are prior incoming work. The present contributions are their source-relative use, uniform specialization and native certification; the geometric restriction on forest optimization; and the exact exceptional-row quotient and lift.

## Implemented and checked

The production integration is the additive top adapter and its independent replay. The current native source validator accepts a connected orientable compact source with exactly one torus boundary. The broader nonempty-boundary mathematical theorem is not an assertion that all existing consumers accept more general states.

- The version-6 whole-cut wrapper verifies both original source proofs before applying the new top trace, then reuses an existing terminal verifier on the reduced core.
- Original zero/one IDs, full port data, and surviving two-handle attaching cycles are retained. Remaining two-handles receive dense consumer IDs only after their original IDs have been checked.
- Sources without three-handles retain the old paths and certificate versions.
- The original source summary remains a summary of the original source, including its original handle counts. Equal index-2/index-3 deletion preserves its Euler characteristic.
- The source-template API is optional. The default adapter uses the linear queue.
- Abstract forest exchange and the exceptional kernel are research APIs. Neither changes default recognition dispatch.
- The release patch was applied to a separate pristine snapshot. All 17 resulting source files match its manifest. All 67 focused tests pass with zero skips in that clean environment. The full repository test suite was not rerun.

## Empirical findings

The retained corpus contains 106 exact source/vector pairs, with SHA-256 `97b4ceed6f068885760d80dea214538634998dd405b77e76926c1f93db03da5c`. Whole-cut completion rises from 85 to 92, with independent replay of every complete result and all earlier successes preserved. Ten three-handle exclusions disappear. Seven become complete; the other three remain inconclusive. Fresh Regina checks of the ten small former exclusions agree with the retained explicit data.

The controlled six-size scheduler benchmark uses genuine subdivided solid tori. At 769 tetrahedra and 256 interior vertices, the recorded median scheduler ratio is 28.8, and the directly timed common-incidence-plus-schedule ratio is about 1.94. The smallest cases regress. The old diagnostic performs exactly `(7q^2+q)/2` row visits on this family; the queue has linear incidence work. Repeated sorting in the old implementation is not included in that row-count formula.

The abstract forest strategy completes 40 of 106 native cores, whereas ordinary raw core cancellation completes 100. It supplies no new native successes. The chain audit authenticates 114 source cores; all have zero second Betti number. Forty-two have an acyclic mandatory set, and each such set is already a whole top tree, so multiple ordering trials do not give empirical evidence about distinct eligible trees. The article proves the general invariance algebraically and supplies a separate geometric family with varying tree choices and nonzero defect.

The kernel audit includes 21,304 small ternary matrices, 4,096 binary 4-by-3 matrices, 3,375 legal exceptional partitions of binary 3-by-3 matrices, and 2,000 seeded larger examples. All stopping projections and largest lifts are checked exhaustively on the designated small cases, beyond checking only complete peelability. The 120 retained replay packets include the six abstract and 114 native cases. For the 106 corpus cores, 773 source rows become 164 exceptional rows in aggregate; 809 occurring source columns become 189 nonzero distinct quotient column types. These are structural reductions, not a measured wall-clock improvement over ordinary peeling.

## Not established

1. A complete deterministic quasipolynomial unknot-recognition algorithm, or an end-to-end speedup for arbitrary knot diagrams.
2. A complete compressed search for the next useful admissible hierarchy surface.
3. Polynomial-size transport and checking of every inherited boundary pattern through the local moves.
4. A bound on the number, encoded size, or rebuild cost of all hierarchy states.
5. A bounded-parameter algorithm for selecting primal/top forests with arbitrary exceptional rows.
6. A complete geometric repair procedure for the lifted stopping cores.
7. A knot verdict from a handlebody histogram for an arbitrary supplied normal cut.
8. A topological negative verdict from an inconclusive matrix strategy, positive rank deficiency, or nonempty stopping set.

Lackenby's July 2026 preprint explicitly leaves its overall running time unestimated. This article uses the announced quasipolynomial target as a research objective and distinguishes certificate verification from discovery throughout.
