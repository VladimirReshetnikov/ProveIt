# Source and proof audit

Audit date: 2026-10-02.

## Scope of the report

The article distinguishes three orders. W is the lexicographic order of all
complete ordinal enumerations of the usual real line. P restricts their domain
to the initial ordinal c. A is the actual Kanovei–Shelah ultrafilter-enumeration
index. Order embeddings throughout need not be continuous or convex.

The mathematical proofs are conventional ZFC arguments. No theorem in this
package has been verified in Lean, and no historical priority is claimed.
The focused searches below are not an exhaustive literature or repository audit.

## Primary published sources inspected

1. Vladimir Kanovei and Saharon Shelah, *A definable nonstandard model of the
   reals*, Journal of Symbolic Logic 69(1) (2004), 159–164.
   DOI: https://doi.org/10.2178/jsl/1080938834
   Published PDF: https://shelah.logic.at/files/95388/825.pdf
   ArXiv record: https://arxiv.org/abs/math/0311165
   The definition on printed page 160, section 2, was inspected in a rendered
   page as well as parsed text. The index consists of maps c -> P(N) whose
   ranges are ultrafilters, allowing repetition. It does not impose injectivity
   or restrict the formal definition to nonprincipal ultrafilters. The finite
   index sorting and the further omega_1 iteration occur in sections 2–4.
   The report does not attribute its new-to-this-report order calculations
   to that paper.

2. Salma Kuhlmann, *Isomorphisms of lexicographic powers of the reals*,
   Proceedings of the American Mathematical Society 123(9) (1995), 2657–2662.
   Preprint: https://d-nb.info/1102198234/34
   Author publication list:
   https://www.math.uni-konstanz.de/~kuhlmann/publikationen.htm
   Corollary 2.4 was checked on a rendered preprint page (PDF page 5), because
   the parsed mathematical text is garbled. It states that an embedding of
   R^alpha into R^lambda, for ordinal exponents, forces alpha <= lambda.
   The article identifies this as classical and supplies its own short proof.
   The support convention in the preprint permits all functions for an ordinal
   exponent, so it is the power used in the article.

3. Alfio Giarlotta, *On the representability number of lexicographic products
   in a Dedekind-complete chain*, Applied Mathematical Sciences 7(127) (2013),
   6347–6353.
   DOI: https://doi.org/10.12988/ams.2013.39524
   PDF:
   https://www.m-hikari.com/ams/ams-2013/ams-125-128-2013/giarlottaAMS125-128-2013.pdf
   The first page was inspected for the definition and terminology of the
   least ordinal exponent admitting a real-power representation. No
   full-enumeration theorem is imported from this source.

## ProveIt repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt
Pinned revision: 6ea60e3677bd847a00baf023c3c532c83884530e

The connected GitHub search and fetch tools were used. Focused search terms
included `lexicographic`, `Kanovei`, `well-orderings`, and
`lexicographic well-ordering`.

Read in full:

- `SetTheory/Cardinals/README.md`
  https://github.com/VladimirReshetnikov/ProveIt/blob/6ea60e3677bd847a00baf023c3c532c83884530e/SetTheory/Cardinals/README.md
  It separates unformalized research reports from the Cardinals Lean library,
  reports unrefereed status, and makes the latter library's admitted published
  statements explicit. The present report does not inherit any Lean status.

- `SetTheory/Cardinals/docs/reports/ordinals-and-order-types/wqo-powersets-and-statures/cofinal-strata-of-finitary-powersets/data/lexicographic_tails_result.json`
  The file records `omega*2 + 2` for the maximal type of a particular
  lexicographic sum and explicitly limits its scope to that sum. It is not a
  theorem about the full enumeration order, and is not used in the proofs.

Search results also showed Hahn-series order modules and adjacent ordinal
reports. Those snippets were used for navigation only, not to assert that the
entire developments had been reviewed. No directly matching proof of the
specific full-enumeration results was located in this focused search. This
is not a claim that no such result occurs anywhere in the repository.

## Proof-dependency audit

- Ordinal spectrum: prefix freeness, regular successor-cardinal stabilization,
  injectivity of enumerations, and binary pair-switch coding.
- Representation rank: real-to-binary coding, the real-power strictness theorem
  (also proved in the article), and fixed-length padding of prefix-free codes.
- Power absorption: explicitly constructed disjoint increasing copies of R,
  ordinal concatenation, and the ordinal-spectrum obstruction.
- Finite blocks: exact first-difference adjacency criterion and the fact that
  a subset of R ordered well in both directions is finite.
- Point characters: possible first-divergence positions, countability of usual
  monotone real sequences, and explicit triple-block constructions.
- Full-order gaps: completion of every injective prefix and the small
  cofinalities of every residual-enumeration cylinder.
- Fixed-length gaps: the same prefix tracking up to c, with special care for
  non-surjective branches of length exactly c.
- Actual ultrafilter index: surjectivity onto a cardinal-c ultrafilter,
  arbitrarily late perturbations within a fixed ultrafilter, and explicit
  missing branches. No hyperreal saturation claim is inferred from index
  topology.

## Verification limits

`finite_checks.py` tests finite permutation adjacency, pair-switch coding,
initial-segment cut coding, concatenation of interleaved ordered copies, and
nonconvex ultrafilter fibers on a finite universe. It uses the standard Python
library and a recorded fixed seed. Results are in `finite_checks_results.json`.

Passing these checks does not verify any assertion about infinite ordinals,
cardinals, choice, topology, or cuts. No external source PDF, proprietary
material, or font file is redistributed in this package.
