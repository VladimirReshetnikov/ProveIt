# Research status and source audit

Report date: 2 October 2026.

## What this package claims

The article gives ordinary mathematical proofs of the following statements, with the hypotheses explicitly stated in the text:

1. **Full class lexicography (Theorem 3.4).** Two well-orders on the same labelled carrier have an elementarily definable largest common labelled initial segment. Comparing their first labels after that segment gives a strict linear order, even if the segment is a proper class. The argument is in GBC and does not invoke ETR or comparison of abstract class order types.
2. **Choice equivalence (Theorem 4.1).** Over GB with set-level AC, global choice, an Ord-bijection onto No, a set-like class well-order of No, and an arbitrary class well-order of No are equivalent. The nontrivial reverse direction uses ordinal codes for transitive closures and the least code in the given surreal well-order. The hypothesis of set AC is retained.
3. **Diagonal obstruction (Theorem 5.1).** No uniform family indexed by any class of sets exhausts all global surreal well-orders. A set-like well-order outside any proposed family is constructed by reversing one designated pair in each indexed relation.
4. **Set-like geometry (Section 6).** Uniform set-indexed cuts can be filled; there are no set-indexed cofinal or coinitial families; every class linear order embeds uniformly, even in each nonempty interval. Set-prefix cylinders are isomorphic to the entire set-like predicate in the stated uniform sense.
5. **Binary-class coding (Theorem 7.2).** The set-like predicate and the predicate of binary classes on Ord are mutually embeddable by uniform transformations. They are not claimed isomorphic.
6. **Full-order adjacency (Theorem 8.3).** Two distinct well-orders are adjacent exactly when the complement of their maximal common prefix is finite and their residual finite permutations are consecutive. This provides finite factorial-sized convex blocks and isolated points in the full surreal order.
7. **General set spectra (Theorem 9.6).** For any infinite linearly ordered carrier of cardinality μ, the full and minimal enumeration spaces have cardinality 2^μ and ordinal spectra exactly below μ⁺. The full space admits Bγ exactly for γ < μ⁺ and has binary coding rank μ⁺.
8. **Singular transition (Theorem 10.3).** The minimal enumeration order of Sκ has exact binary rank κ·κ at singular strong-limit κ, and μ = 2^{<κ} otherwise. The proof uses a cone decomposition and a first-varying-row-preserving scheduler. No inaccessible cardinal is assumed here.
9. **Full-class interpretation (Theorem 11.1).** In the external full-class model (Vκ, P(Vκ)) at a strongly inaccessible κ, the internal set-like and unrestricted global orders become Wκ(Sκ) and W(Sκ), respectively. Their external coding ranks differ. This is a relative model calculation with an inaccessible hypothesis, not an unconditional existence proof of such a model.

These statements are supplied with proofs but have not been independently refereed or kernel-checked. The precise formulations, and especially the singular-cardinal result, are offered for mathematical review. Historical originality is not certified.

## What is not claimed

There is no new Lean or Rocq verification of the transfinite results. The Python checks are not substitutes for the proofs. The bounded theorem is not a construction of a full class model at a singular cardinal. The full collection of class well-orders is not treated as a set or ordinary class at the same foundational level. No universal semantic decoder for arbitrary formula codes is assumed. The nine research questions are proposed continuations, not a verified census of currently open problems.

## Repository audit

Pinned repository:

`VladimirReshetnikov/ProveIt`

Pinned commit:

`63bb8b1d99359e7188abf0a33fb152e121858150`

The connected GitHub search and fetch tools were used. The following were directly read in full:

- `SetTheory/Cardinals/docs/reports/ordinals-and-order-types/lexicographic-well-orderings-of-reals/README.md`
- `Algebra/SurrealNumbers/Surreal/Foundations/SignSequenceSimplicity.lean`

The containing real-well-order report directory was also inspected through its GitHub contents listing. Searches included `lexicographic well` and a focused search for a small-cut realization identifier. Not every search succeeded, and no whole-repository audit is asserted.

The real-order README describes a 54-page merged research report and explicitly states that it is unrefereed and not formalized. Its full merged article was not independently reviewed here. Therefore the needed set-sized coding and spectrum arguments are reproved in the present article rather than accepted from unread predecessor proofs.

The Lean source includes, among other declarations:

```
isPrefix_of_minimum_birthday
existsUnique_prefix_of_ordConnected
existsUnique_minimum_birthday_of_ordConnected
ordConnected_separators
existsUnique_simplest_separator
```

The last theorem assumes the existence of a separator. The source's distinction between uniqueness and cut-filling existence is preserved in the proposed formalization architecture. The repository was not rebuilt, and declarations outside this inspected file are not asserted to have been audited.

Pinned source URLs are included in the article bibliography. No repository files were modified.

## Literature audit

The main literature checks were targeted at the foundational and historical distinctions needed by this task:

- **Kanovei–Shelah, arXiv:math/0311165.** The definition of the lexicographic ultrafilter index was inspected in the paper, including a screenshot of PDF page 2. The article distinguishes their maps, whose ranges are ultrafilters, from exhaustive bijections and from all class well-orders.
- **Hamkins–Woodin, arXiv:1806.11180v1.** Sections 2–3 and Theorem 6 were inspected. They provide the distinction between class-valued recursion and ordinary set-valued stages, the formulations of class well-foundedness, and the sufficient ETR hypothesis for abstract class-order comparability. Their historical open questions are not presented as certified current open questions.
- **Ehrlich, Bulletin of Symbolic Logic 18 (2012), 1–45.** Author-uploaded text and publisher metadata were consulted for surreal universality and the absolute-continuum framework. DOI: 10.2178/bsl/1327328438.
- **Hamkins, “Universal order type,” MathOverflow, 6 March 2011.** The author's forth-construction explanation was inspected. URL: https://mathoverflow.net/questions/57597/universal-order-type
- **Hamkins, “Is the universality of the surreal number line a weak global choice principle?”, MathOverflow, 7 January 2016.** Used only to distinguish that historical question from the well-order-existence equivalence proved here. URL: https://mathoverflow.net/questions/227849/
- Gonshor's 1986 book is cited as a standard background reference; this package does not claim a page-by-page new audit of the book.

The source search was not sufficient to establish that every exact formulation in this article is absent from earlier literature.

## Computational checks

Recorded output: `data/finite_checks.json`.

| Check family | Comparison cases |
|---|---:|
| Sign-code order preservation and prefix-freeness | 65,025 |
| Pair-orientation lexicographic coding | 87,381 |
| Common-prefix formula and adjacency, finite pairs | 15,017 |
| Additional larger finite adjacent pairs | 5,758 |
| Row-scheduler product-to-permutation coding | 7,724 |
| **Total** | **180,905** |

All checks passed. The program also records a three-point example where relation-table lexicography differs from enumeration lexicography. Only exact finite data and standard-library Python are used.

The tests do not assess singular cardinals, class Replacement, cofinalities, model existence, or any other infinitary claim. Those depend on the written proofs.

## Document validation

The source was compiled with pdfLaTeX in three passes. The final compilation has no undefined references, undefined citations, or overfull boxes. The resulting PDF has 24 pages, including the unnumbered title page. It was rendered to images; all pages were reviewed in contact sheets, with full-size inspection of selected proof and reference pages. No image assets or external bibliography database are needed to rebuild it.

Checksums in `SHA256SUMS.txt` identify the delivered source, PDF, code, data, build script, and documentation. Rebuilding with another TeX installation may change PDF bytes without changing the mathematical content.
