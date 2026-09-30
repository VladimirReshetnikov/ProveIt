# Research status and claim boundaries

## What has been done

The article provides ordinary mathematical proofs of its general
representation, compact-realization, extremal-word, finite-height,
synchronization, approximation, and finite-obstruction results. Its
NP-completeness result imports the established modified-SCS hardness theorem
of Lagoutte and Tavenas and proves the transfer, including exact common-prefix
padding to power-of-two budgets.

The finite verifier was executed with `--max-n 5 --brute-n 4`. All recorded
checks passed. The PDF was compiled with pdfLaTeX, all pages were rendered with
Poppler, contact sheets of every page were inspected, and the main exact-tower
formula page was inspected at full size. The final compile has no LaTeX
warnings or overfull/underfull box diagnostics.

## What has not been done

No independent referee has checked the proofs. No Lean or other proof-assistant
formalization is included or claimed. Finite computation does not prove the
infinite-space statements. The verifier's six-point option was not run.

No named longstanding published open problem is announced as solved. This is
a research extension of the repository's binary open-query direction, with
specific generalizations and exact formulas. Historical priority and the term
“breakthrough” are not asserted. The broader literature on finite partitions,
difference hierarchies, typed graph fusion, and supersequences may contain
related or equivalent formulations. The article explicitly credits those
connections and distinguishes its proofs from novelty certification.

The exact tower formula concerns the supremum over all q-colorings of the
specified spaces. The compact sharp synchronization examples instead concern
particular colorings. These two statements must not be conflated.

## Repository scope

The source comparison is pinned to commit
`5c695cfdf70a8b6c91bd5b2c1e99e3baecd5a864` of
`VladimirReshetnikov/ProveIt`.

The report README and the opening portion of its article were inspected,
together with repository search results. This is not a complete audit of all
files or proofs in the repository. A repository search for `supersequence`
returned no matches in the connected search; that result is not evidence of
historical priority or an exhaustive absence guarantee.

No remote repository changes were made.
