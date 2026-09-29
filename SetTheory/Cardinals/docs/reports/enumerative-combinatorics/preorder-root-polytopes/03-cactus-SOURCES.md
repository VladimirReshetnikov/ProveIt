# Sources and provenance

Audit date: September 29, 2026.

## Repository source

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit: `9754e83603e223811b7515eb892f22c847144593`

Commit date returned by GitHub: `2026-09-29T14:35:15Z`.

Source path:
`SetTheory/Cardinals/docs/reports/enumerative-combinatorics/preorder-root-polytopes/article.tex`

Source Git blob: `8739a224fa8956adab5d8df9f2d5012a6a220959`

Pinned source:
https://github.com/VladimirReshetnikov/ProveIt/blob/9754e83603e223811b7515eb892f22c847144593/SetTheory/Cardinals/docs/reports/enumerative-combinatorics/preorder-root-polytopes/article.tex

Its Part II is the September 28, 2026 height-two report. Section 19 proves the
cactus construction. Section 24 asks the question headed “Beyond the sixth-root
cactus matrices.” These sections were read through the GitHub connector; the
full source article is not redistributed in this package.

## Primary literature consulted

1. Hidefumi Ohsugi and Akiyoshi Tsuchiya, *Symmetric edge polytopes and matching
   generating polynomials*, Combinatorial Theory 1 (2021), #9.
   DOI: 10.5070/C61055371.
   https://arxiv.org/html/2008.08621v2
   Theorem 7.2 and its proof provide the prior cactus real-rootedness context.

2. Robert Davis and Florian Kohl, *Perfectly Matchable Set Polynomials and
   h*-polynomials for Stable Set Polytopes of Complements of Graphs*.
   https://arxiv.org/abs/2207.14759
   Used for the established invariant's definition and literature context,
   not as an input to the new classification proof.

3. Petter Brändén, *Polynomials with the half-plane property and matroid theory*,
   Advances in Mathematics 216 (2007), no. 1, 302–320.
   DOI: 10.1016/j.aim.2007.05.011.
   https://arxiv.org/html/math/0605678v4
   Theorem 5.6 is the exact external input to the K_{2,3} stability proof.

4. P. J. Almeida, D. Napp, and R. Pinto, *Superregular matrices and applications
   to convolutional codes*, Linear Algebra and its Applications 499 (2016),
   1–25.
   https://arxiv.org/abs/1601.02960
   Used for pattern-sensitive superregular terminology. The publisher's full
   page was not accessible during the final check; no inaccessible theorem
   from it is used.

5. Matthew Baker, Changxin Ding, and Xu Zhuang, *The Jacobian of a
   Sixth-Root-of-Unity Matroid*.
   https://arxiv.org/html/2308.11760v2
   Definitions 2.1–2.5 give classical sixth-root and complex-unimodular context.
   Their weaker condition permits structurally nonzero minors to vanish;
   the article's support-exact condition does not.

6. Sam Burton, Cynthia Vinzant, and Yewon Youm, *A real stable extension of
   the Vamos matroid polynomial*.
   https://arxiv.org/abs/1411.2038
   Used to credit the preexisting general stability-versus-determinant
   separation phenomenon, not as a proof dependency.

7. Masataka Nakamura, *A note on binary fundamental transversal matroids*,
   Graphs and Combinatorics 5 (1989), 371–372.
   DOI: 10.1007/BF01788693.
   https://link.springer.com/article/10.1007/BF01788693
   The publisher's abstract and bibliographic record were inspected. This is
   a related earlier characterization, not an imported equivalent theorem.
   Its full text was not available in the inspected publisher preview.

## Audit limitations

Searches also targeted ternary/fundamental transversal matroids, sixth-root
matrices, matching-support stability, and superregular cactus patterns.
Some broad searches returned irrelevant material; no such results are used
as mathematical evidence. The audit does not establish the absence of an
older equivalent theorem. The delivered proofs and the answer to the pinned
repository question stand independently of an absolute novelty claim.
