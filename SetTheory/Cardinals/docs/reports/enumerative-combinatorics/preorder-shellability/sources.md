# Primary-source and current-status audit

Checked during preparation on 20 September 2026. Sources are linked, not
redistributed; this ZIP contains no copied research-paper PDFs or font files.

## Selected question and exact object

Christos A. Athanasiadis and Frédéric Chapoton, *Polytopes and posets associated
to preorders*, arXiv:2605.26916v1 (2026).

- https://arxiv.org/abs/2605.26916v1
- https://arxiv.org/html/2605.26916v1
- https://arxiv.org/pdf/2605.26916v1

The defining inequalities are (2) in the introduction and Section 3.1. The
coordinatewise lattice-point poset is specified in Section 3.3. Question 4.6,
on printed p. 13 of the PDF, asks about shellability and Cohen–Macaulayness for
general preorders. The paragraph immediately preceding it establishes these
properties when the preorder has a maximum vertex. This is the selected target.
Theorem 1.5 and the proof of Proposition 4.5 are used only for the optional
Ehrhart–Zeta identification of the chain-complex h-polynomial.

The article and this audit consistently use the displayed version identifier
v1; no inference from that identifier to an uninspected later version is made.
The source treats equivalence classes as preorder “vertices”; all original
elements remain separate coordinates in the integer vectors.

## Classical and closely related literature

Jürgen Herzog and Takayuki Hibi, *Discrete polymatroids*, Journal of Algebraic
Combinatorics 16 (2002), 239–268.
https://doi.org/10.1023/A:1021852421716

Classical context and terminology. Neither the specified-insertion convention
nor a shelling theorem is left as an unchecked citation: the needed exchange
lemma is proved in the article from submodular tight sets.

Majid Alizadeh, Afshin Goodarzi, and Siamak Yassemi, *M-Shellability of Discrete
Polymatroids*, arXiv:1012.1075v1 (2010).
https://arxiv.org/abs/1012.1075v1

Theorem 2.1 establishes M-shellability. The definition is an interval partition
of a monomial order ideal, not the ordinary simplicial shelling conclusion used
here. The article gives a small example showing why the terminology cannot
simply be substituted. The primary PDF's definition and theorem were inspected.

Antonino Ficarra, *Shellability of Componentwise Discrete Polymatroids*,
arXiv:2312.13006v2 (27 December 2023).
https://arxiv.org/html/2312.13006v2
https://doi.org/10.37236/12818

Section 4 discusses simplicial multicomplexes; earlier sections treat linear
quotients and componentwise polymatroidal ideals. Relevant prior context, not an
import used to skip the proof that the chain complex itself is shellable.

Michelle L. Wachs, *Poset topology: tools and applications*,
arXiv:math/0602226v2 (2006).
https://arxiv.org/abs/math/0602226v2
https://arxiv.org/pdf/math/0602226v2

Section 4.1 gives the homological definition of the Cohen–Macaulay property and
explains the implication from pure shellability. Lecture 5 supplies context for
order complexes and poset maps/products. The needed shelling-to-link homology
and order-homotopy arguments are also supplied in the article.

## Later related preorder paper

Ziyi Dai, Qilin Hou, Zhiyuan Liu, Warut Thawinrak, and Hongyu Wang,
*Counting Lattice Points in Minkowski Sums of Cross Polytopes*,
arXiv:2608.16037v2 (27 August 2026).
https://arxiv.org/abs/2608.16037v2
https://arxiv.org/html/2608.16037v2

Section 4.3 concerns support-enumerator duality for preorders. Its retrieved
text did not state a solution to the ordinary shellability question. Its
support polynomial is not the chain-complex h-polynomial computed here.
This work is credited, not claimed as part of this package's contribution.

## Search boundary

Searches included the source's exact title together with “shellable” or “4.6”,
preorder shellability and polymatroids, and “discrete polymatroids” with “order
complex”. We inspected the actual target paper and the relevant related
multicomplex and preorder papers rather than treating search snippets as
proofs. Some searches returned unrelated material and some PDF retrievals
failed; those do not establish absence of prior work. Accessible primary HTML
and PDF text were used for the relevant definitions.

No resolution of Question 4.6 was located. This does not prove that none exists,
and in particular is not a priority claim for the general shelling construction.
The mathematical result is presented as a complete proposed proof for review.

## Attached manifest

The manifest is a user-supplied selection source, not external evidence that its
listed proofs are correct. Exact relevant entries and the supplied file's hash
are recorded in `manifest_selection.md`. No unseen package contents are inferred.
