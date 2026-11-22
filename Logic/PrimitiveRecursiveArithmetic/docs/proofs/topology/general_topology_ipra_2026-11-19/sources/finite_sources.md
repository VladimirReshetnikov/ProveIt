# Sources for the finite-topology chapter

Accessed 2026-11-19. The chapter's proofs are supplied independently; the pages below identify the requested terminology and classical statements. No prose from these pages is reproduced at length.

| Page | URL | Web reference | Used for |
|---|---|---|---|
| General Topology | https://mathworld.wolfram.com/topics/GeneralTopology.html | parent retrieval | Scope of the task |
| Topology | https://mathworld.wolfram.com/Topology.html | turn286895898view0 | Topology axioms, finite-topology correspondence motivation |
| Exterior | https://mathworld.wolfram.com/Exterior.html | turn286895898view1 | Term; the chapter supplies the precise standard definition Int(X minus A) |
| Homeomorphism | https://mathworld.wolfram.com/Homeomorphism.html | turn286895898view2 | Bijection with continuous inverse; equivalence relation |
| Urysohn's Lemma | https://mathworld.wolfram.com/UrysohnsLemma.html | turn286895898view3 | Normality without an implicit T1 requirement and continuous separation |
| Urysohn's Metrization Theorem | https://mathworld.wolfram.com/UrysohnsMetrizationTheorem.html | turn286895898view4 | Regular second-countable T1, separable metric, Hilbert-cube alternatives |
| Compact-Open Topology | https://mathworld.wolfram.com/Compact-OpenTopology.html | turn762360018view0 | Subbasic sets, evaluation, exponential law |
| Sigma-Discrete Family | https://mathworld.wolfram.com/Sigma-DiscreteFamily.html | turn762360018view2 | Finite certified analogue through graph coloring |
| Sigma-Locally Finite Family | https://mathworld.wolfram.com/Sigma-LocallyFiniteFamily.html | turn762360018view3 | Finite family local-finiteness bound |

The following page was inspected to avoid a coding mistake; the finite-algebra chapter owns its treatment:

- Sigma-Algebra: https://mathworld.wolfram.com/Sigma-Algebra.html (turn762360018view1). A countable union of a primitive-recursive sequence of Boolean subsets of a finite carrier need not have a uniformly primitive-recursively computable Boolean code. Finite carrier size alone does not resolve this issue.

## Reproducibility

- `lean/FiniteTopology.lean` checked with Lean 4.32.0 (`8c9756b28d64dab099da31a4c09229a9e6a2ef35`), using `Init` only.
- Axiom reports for five central lemmas are empty; see `validation/finite_lean.log`.
- `code/finite_topology.py --max-n 4` exhaustively checks preorder spaces through four points, map/quotient results through three points, and compact-open exponentials through two-point source/target carriers.
- All universal mathematical claims are supported by the chapter's proofs, not inferred from the finite test results.
