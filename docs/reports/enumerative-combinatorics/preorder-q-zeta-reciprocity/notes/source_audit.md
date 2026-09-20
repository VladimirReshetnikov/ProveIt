# Source and scope audit (merged)

Audit date: **20 September 2026**.

This file merges the three source ledgers of the drafts that were combined into
this package (`preorder-q-zeta-support-reciprocity`, `preorder-q-zeta-supportwise`
and `preorder-q-reciprocity-weighted`). Where the three recorded the same fact
differently, both formulations are kept; where they disagreed in degree of
caution, the most cautious statement is kept.

## Target and nonduplication

The target is the full q-identity in Christos A. Athanasiadis and Frédéric
Chapoton, *Polytopes and posets associated to preorders*,
https://arxiv.org/abs/2605.26916v1 ; also
https://arxiv.org/pdf/2605.26916v1 and https://arxiv.org/html/2605.26916v1 .

The checked PDF labels it **Conjecture 4.9, equation (21), printed page 14**.
The right-hand exponent is the number of elements **covered by** a maximal
point. The source's definition uses weak chains of length m-1 at [m]_q. The
source's printed page 15 reports computational verification through size 6 and
the five-element value -(2q+1)(q^2+4q+1)/q^5. The defining inequalities of that
five-element example are in Section 3.1. Theorem 2.1 is the source's own
statement of Postnikov's formula; Lemma 4.1 is its draconian/filter
identification, which this package credits explicitly where it reuses it.
The PDF formulas were checked visually, not only from parsed text.

### The version-date anomaly

All three merged drafts recorded the same anomaly, each slightly differently,
and the union is retained:

- the arXiv submission record displayed only v1, submitted 26 May 2026;
- the PDF's author date is 27 May 2026;
- the retrieved HTML bears an internal date in August 2026, recorded by one
  draft as 24 August 2026.

The target is therefore pinned by arXiv identifier, section, equation number
and displayed formula, rather than by any of those dates. The relevant q-zeta
statement agrees between all the representations consulted.

### Nonduplication

The user's manifest explicitly says that its earlier preorder-reciprocity
package proved the ordinary q=1 case, **not** the full q-refinement. The
present work does not import that package's proof. The exact relevant entry is
preserved verbatim, with its SHA-256 digest and its source line numbers
960–969, in `manifest_provenance.txt`; that file is the precise record of the
boundary.

**Only the manifest, and not the full text of the earlier packages, was
available for this comparison.** Nonduplication is assessed against what the
manifest's descriptions explicitly claim. The earlier report archives were not
read or assumed correct, and no claim is made to have audited them.

Three overlaps with the earlier package
`enumerative-combinatorics/preorder-polytope-reciprocity` are acknowledged in
Section 1.5 of the article and flagged again where they occur: (i) the
independent-capacity reciprocity that the second proof reproves so as to be
independent of an unrefereed draft; (ii) the enumerator formula for
`L_{tau*}`, which is that package's rising-factorial enumerator at s = 0 with
independent capacities, derived the same way, both crediting AC Lemma 4.1;
(iii) the ordinary q=1 case, which this package continues to present as
already covered there and not as a fresh result.

The manifest's separate entry "A Reflexive Root-Polytope Model for Preorder
h-Polynomials" concerns a different conjecture and is not repeated here.

### Search limitations

Searches included the arXiv identifier with "4.9" and "proof", the authors'
names with "Conjecture 4.9", the source title with "q-zeta", "reciprocity" and
"proof", and "preorders q-zeta reciprocity"; the source manuscript, Chapoton's
q-zeta paper and the nearby cross-polytope paper were inspected. The checked
source still states the target as a conjecture, and these searches did not
identify a separate resolution. Some search results were irrelevant or
aggregated. This is a focused literature check, not exhaustive coverage of
unindexed papers, unpublished work, or all recent drafts, and the same result
could exist under other terminology. No proof of historical priority is
claimed.

## Imported primary mathematics

**Frédéric Chapoton, On a q-analogue of the Zeta polynomial of posets.**
https://arxiv.org/abs/2402.11979v2 , revised 29 January 2025; also
https://arxiv.org/html/2402.11979v2 . Appendix C develops a q-incidence
algebra. The article's incidence-matrix calculation is a fully written
specialization of that viewpoint, and it also supplies, in the least-element
setting, the polynomial existence that construction requires. It is not
claimed that interpreting q-zeta values through incidence powers is new. No
general weighted reciprocity theorem is assumed from this paper: the article
constructs the needed negative evaluations twice and independently, once by
the incidence continuation and once by the Gaussian endpoint formula.

**Alexander Postnikov, Permutohedra, associahedra, and beyond.**
https://arxiv.org/abs/math/0507163 ; also
https://arxiv.org/html/math/0507163v1 . Published in IMRN 2009, no. 6,
1026–1106; DOI 10.1093/imrn/rnn153. The theorem numbering used is that of the
arXiv PDF: Definition 9.2; Theorem 11.3 (printed page 28); Lemma 11.7;
Corollary 11.8. The PDF pages containing the lattice-count theorem and the
duality corollary were checked visually. The untrimmed formula shifts the
distinguished universal weight by +1, and that shift is retained even when the
actual Minkowski coefficient is zero. The source contains a later passage
explicitly called an "alternative semiproof"; that passage is **not** what is
imported — the stated theorem and its main proof are the dependency.

Theorem 11.3 is used by both proofs. Lemma 11.7 / Corollary 11.8 are used
**only** by Engine 1 of the first proof; Engine 2 derives the instance it needs
from Theorem 11.3 alone, applied twice, and the support-restricted graph is
checked for isolated vertices before connected bipartite duality is invoked.
This import trade is recorded in the article rather than silently resolved.

**Ehrhart–Macdonald reciprocity.** The standard formula
`E_Q(-1) = (-1)^dim(Q) #int(Q)` is used only for full-dimensional integral
polytopes with all capacities positive integers, univariately along
`s -> s*c`. Three references are retained, because the three merged drafts each
used a different one and they serve different purposes:

- I. G. Macdonald, *Polynomials associated with finite cell-complexes*,
  JLMS (2) 4 (1971), 181–192 — the historical source. **The publisher page was
  not accessible through the browsing tool; the bibliographic entry was
  cross-checked indirectly in research-paper references. No assertion is made
  that the original Macdonald paper was read in full.**
- M. Beck and S. Robins, *Computing the Continuous Discretely*, second
  edition, Springer 2015, Chapter 4 — the textbook statement.
- M. Beck and M. Develin, *On Stanley's reciprocity theorem for rational
  cones*, https://arxiv.org/abs/math/0409562v3 , revised 4 August 2005 — a
  primary-source proof of cone reciprocity, of which only the
  lattice-polytope case is used, with full dimensionality checked explicitly.

**P. Hall, On representatives of subsets**, JLMS 10 (1935), 26–30,
https://doi.org/10.1112/jlms/s1-10.37.26 . The finite form needed, with the
exact matching convention and the multiplicity reduction, is proved in
Appendix A of the article. It is used only by the first proof; the second uses
no matching theorem.

## Nearby 2026 work inspected for overlap

Ziyi Dai, Qilin Hou, Zhiyuan Liu, Warut Thawinrak and Hongyu Wang,
*Counting Lattice Points in Minkowski Sums of Cross Polytopes*,
https://arxiv.org/abs/2608.16037v2 , 27 August 2026; also
https://arxiv.org/html/2608.16037v2 . Its support-enumerator/root-polytope
interpretation and preorder-duality consequence were checked. They concern the
support enumerator over a full draconian set — that is, over *all* lattice
points — not the maximal-layer q-zeta formula proved here; the V versus V*
example in the article separates the two. It is not a mathematical dependency.
A text search for "zeta" in the retrieved HTML returned no matches; that is a
search observation, not a general certificate of absence of related
mathematics.

## Claimed contribution versus supporting material

The proposed new conclusions are: the full conjecture; its strengthening to the
squarefree exact-support identity and to the support-restricted interior-count
identity; the evaluations at every negative q-integer with their positivity and
sharp extreme degrees; and the arbitrary normalized-height variant. The proofs
combine the explicitly stated classical tools and nothing else.

The examples, boundary counterexamples and exact test output were computed in
these investigations. They are not presented as inherited data. The
five-element factorization is explicitly compared with the source paper. No
proof assistant, external reviewer, or computer-algebra service was used.

That three separate drafts reached the same two statements by three different
routes is evidence of internal consistency, not of correctness. A shared
misreading of the source's conventions would not have been detected by that
agreement, which is why the conventions are restated in Section 1 of the
article and audited item by item in Section 15 and in `proof_audit.md`.
