# Source audit and scope of priority claims

Audit date: 29 September 2026.

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspected commit: `9b24a3a8d545af9624f6ac455f5b548be62818b6`.

Relevant directory:
`SetTheory/Cardinals/docs/reports/enumerative-combinatorics/preorder-root-polytopes/`.

The README and the relevant sections of `article.tex` were read through the
GitHub connector. The report combines Part I, dated 20 September 2026, and
Part II, added 28 September 2026. Its explicit status is AI-assisted,
unrefereed, and not formalized in Lean. It proves the height-at-most-two poset
case, while leaving general gamma-positivity and nontrivial equivalence-class
blowups beyond its proved scope. Its demand/support counting lemma is an
inherited input, not a new claim of the present article.

The existing report also credits previously posted nonreal-root
counterexamples to Shivam Patel. The present work neither republishes those
as a discovery nor relies on their priority for its proof. The canonical
root-polytope realization asserted in Part I is not used in the main proof.

## Primary mathematical sources

### Athanasiadis–Chapoton: the target

C. A. Athanasiadis and F. Chapoton, *Polytopes and posets associated to
preorders*, arXiv:2605.26916 (2026).

https://arxiv.org/html/2605.26916v1

Section 5, Conjecture 5.2 explicitly asks for nonnegative gamma coefficients
for every finite preorder, not just posets or arbors. This is the statement
proved in the article. The same source's flag-realization question is not
settled here. The inspected version identifier is the URL above; no later
uninspected revision is represented as having been checked.

### Kálmán–Postnikov: hypertrees and root polytopes

T. Kálmán and A. Postnikov, *Root polytopes, Tutte polynomials, and a duality
theorem for bipartite graphs*, Proc. London Math. Soc. (3) 114 (2017), 561–588.

https://arxiv.org/abs/1602.04449
https://doi.org/10.1112/plms.12015

The article imports the normalized volume = number of hypertree vectors
consequence. These are vectors counted once, not spanning trees counted with
multiplicity. The volume normalization is stated in the article.

### Ohsugi–Tsuchiya and Davis–Kohl: matchable vertex supports

H. Ohsugi and A. Tsuchiya, *Reflexive polytopes arising from bipartite graphs
with gamma-positivity associated to interior polynomials*, Selecta Math.
(N.S.) 26 (2020), article 59.

https://arxiv.org/html/1810.12258v4
https://doi.org/10.1007/s00029-020-00588-0

Propositions 3.3–3.4 identify the relevant augmented root-polytope numerator
with the perfectly matchable set polynomial. The augmentation has one new
universal vertex on each shore and the edge joining them.

R. Davis and F. Kohl, *Perfectly matchable set polynomials and h*-polynomials
for stable set polytopes of complements of graphs*, arXiv:2207.14759 (2022).

https://arxiv.org/pdf/2207.14759

Theorem 3.10 was checked in the PDF text and a rendered screenshot of printed
page 10. It gives precisely the augmentation used in the proof. Neither the
matching-support polynomial nor its augmented-root identity is claimed as
new. The prescribed-support refinement in the article is obtained from the
known total-count identity by Boolean inversion.

### Dai et al.: prior general support-enumerator results

Z. Dai, Q. Hou, Z. Liu, W. Thawinrak, and H. Wang, *Counting lattice points in
Minkowski sums of cross polytopes*, arXiv:2608.16037 (2026).

https://arxiv.org/pdf/2608.16037

The inspected PDF identifies version v2, 27 August 2026. Its Theorems 1.2–1.3
supply prior root/support-enumerator and duality results. Problem 5.3 asks
which bipartite graphs have the conjectured support-polynomial properties.
The present article addresses palindromicity and gamma-positivity for the
balanced perfect-matching class, not the whole problem and not its
real-rootedness component. The relevant theorem page was visually checked.

### Menon: an earlier gamma-positive family

K. Menon, *Gamma-positivity for octopuses: a bijective proof*,
arXiv:2608.13247 (2026).

https://arxiv.org/html/2608.13247v1

This is a prior special-family result, including lopsided octopuses. It is
credited rather than represented as a general-preorder theorem.

## Novelty assessment

The contribution relative to the inspected repository is the unrestricted
preorder support-fibre reduction and the resulting general gamma formula,
plus the stated matching-theoretic classification and derived formulas.
The endpoint-defect criterion is proved directly, but its relationship to
older matching/Gorenstein characterizations warrants additional historical
review. No separate absolute priority claim is made for every consequence.

Targeted public searches used combinations of “preorders”, “gamma-positivity”,
“Athanasiadis”, “Chapoton”, “Conjecture 5.2”, “perfectly matchable set
polynomial”, and “transitive”. Some search responses were poor or unrelated;
those results were not used as mathematical evidence. No earlier general
proof was located in the inspected sources. That is a limited search result,
not a proof of absence of a preprint, unpublished argument, or parallel work.

The article distinguishes a proved mathematical implication from claims
about novelty, refereeing, and formal verification. The latter are not
inferred from successful finite tests.
