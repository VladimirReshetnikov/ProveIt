# Claim and dependency ledger

## Proposed contributions, with full proofs in the article

| Result | Location | Main dependencies |
| --- | --- | --- |
| Universal preorder ultra-log-concavity, coefficient bounds, simultaneous equality case | Section 4 | Established lattice-point/matching-support bridge and classical matroid Lorentzian theory |
| Transitivity if and only if paired copies are clones | Section 5 | Elementary matching paths and basis permutations |
| Symmetric transversal presentation and upset rank formula | Section 6 | Hall's theorem and the matching deficiency formula; elementary proofs supplied |
| Intrinsic clone classes, unlabeled reconstruction, full automorphism group | Section 7 | Sections 5--6; basis-exchange tests |
| Order duality and induced restrictions as matroid operations | Section 8 | Exact basis descriptions |
| Weighted orbit/gamma identity and weighted preorder ultra-log-concavity | Section 9 | Overlap cancellation, the lift, classical Lorentzian theory |
| Explicit height-two minor universality | Section 10 | Elementary matching contraction/deletion analysis |
| Height-two minor closure equals finite gammoids | Section 10 | The preceding construction plus Ingleton--Piff's classical theorem |
| Signed-support stability if and only if the associated basis polynomial is stable | Section 11 | Partial reciprocal substitution in the upper half-plane |
| Exact block locality of signed-support stability | Section 12 | Explicit one-vertex-sum identity, upper-half-plane argument, induced deletion |
| Stable families with complete-bipartite and even-cycle blocks | Section 13 | Uniform-matroid stability, an even-cycle Hermitian certificate, Section 12 |

The weighted and probabilistic statements include direct consequences of
classical results; they are not presented as unrelated new general theorems
of probability or Lorentzian theory. The proposed contributions are stated
relative to the inspected sources, without asserting absolute priority.

## Classical inputs, not new results of this manuscript

1. The matching-support/transversal-matroid lift and unweighted bimatroid
   ultra-log-concavity: F. Roehrle and M. Ulirsch, *Logarithmic concavity of
   bimatroids*, arXiv:2402.15317v2, especially Theorem A, Proposition 2.2,
   Example 2.4.
2. Matroid basis polynomials are Lorentzian, with preservation under
   nonnegative linear substitutions: P. Braenden and J. Huh, *Lorentzian
   polynomials*, Annals of Mathematics 192 (2020), 821--891;
   arXiv:1902.03719v8, especially Theorems 2.10 and 3.10.
3. The preorder support/root-polytope bridge: Z. Dai, Q. Hou, Z. Liu,
   W. Thawinrak, H. Wang, *Counting Lattice Points in Minkowski Sums of
   Cross Polytopes*, arXiv:2608.16037v2; the augmented matching-support
   identity is recorded in R. Davis and F. Kohl, arXiv:2207.14759v1,
   Theorem 3.10, crediting Ohsugi--Tsuchiya.
4. Finite gammoids are minors of transversal matroids:
   A. W. Ingleton and M. J. Piff, *Gammoids and transversal matroids*,
   Journal of Combinatorial Theory, Series B 15 (1973), 51--68,
   DOI 10.1016/0095-8956(73)90031-2.
5. The multiaffine Rayleigh characterization of real stability:
   P. Braenden, *Polynomials with the half-plane property and matroid theory*,
   Advances in Mathematics 216 (2007), 302--320; arXiv:math/0605678.

The article contains typeset author names and the full bibliography.

## Repository dependencies and non-claims

The inspected report is the combined *A Reflexive Root-Polytope Model for
Preorder h-Polynomials*, Parts I--IV, at commit
`e1afd75e35a4de734d5aa47aec5cdb917b82ed3e`.

- Report `README.md` blob:
  `846d9f19fadac9cd933b74370cdb8fafa2211c5d`.
- Report `article.tex` blob:
  `d52a2633b58e74aa653e967eb56adc1aa41bc8ae`.

The all-preorder gamma formula, transitivity/palindromicity criterion,
height-two matching-support formula, cactus faithful-matrix classification,
and theta-family counterexamples predate this manuscript in the inspected
repository. The theta example is credited there to Shivam Patel for the
first counterexample. None is claimed as a first result here.

This manuscript does not certify the complete repository or depend on an
assertion that every repository theorem has been formally verified. Its
structural matroid arguments are proved independently, and its enumerative
inputs are stated explicitly with published-source dependencies.

## Verification boundary

The script checks finite instances and exact certificates only. It does not
prove all-size reconstruction, universal inequalities, or graph stability in
general. No proof assistant was run. No claim of exhaustive literature coverage,
complete stable-graph classification, or resolution of all ten research questions
is made.
