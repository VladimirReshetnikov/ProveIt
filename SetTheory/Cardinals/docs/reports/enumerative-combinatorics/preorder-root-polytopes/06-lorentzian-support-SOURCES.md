# Sources, theorem dependencies, and limits

Prepared September 29, 2026. References are to primary research sources or the
explicit repository report. This is a targeted source audit, not a certification
that every implication below is new in the worldwide literature.

## The published question

Ziyi Dai, Qilin Hou, Zhiyuan Liu, Warut Thawinrak, Hongyu Wang,
*Counting Lattice Points in Minkowski Sums of Cross Polytopes*,
arXiv:2608.16037v2 (2026).
https://arxiv.org/html/2608.16037v2

Problem 5.3 asks which bipartite support enumerators have the properties
conjectured for preorders: unimodality, palindromicity, and real-rootedness.
The article answers the unimodality component for ALL bipartite graphs,
with a stronger binomial-normalized inequality. It does not answer the entire
multi-property classification question. Theorem 4.2 supplies the augmented
root-polytope interpretation, which is not an assertion about every
unaugmented root polytope.

Christos A. Athanasiadis, Frédéric Chapoton,
*Polytopes and posets associated to preorders*, arXiv:2605.26916 (2026).
https://arxiv.org/abs/2605.26916

Section 5 is the source of the underlying preorder conjectures. Prior
repository reports already treat gamma-positivity and real-rootedness
counterexamples; those results are not discoveries of this package.

## Imported counting identity

Hidefumi Ohsugi, Akiyoshi Tsuchiya,
*Reflexive polytopes arising from bipartite graphs with gamma-positivity
associated to interior polynomials*, Selecta Mathematica (N.S.) 26 (2020), 59.
https://arxiv.org/abs/1810.12258

Proposition 3.4 and its proof supply the fixed-support positive-coordinate
lattice-point count used in Lemma 2.1. The proof was read in the PDF, including
the page carrying the fixed-support argument. Its extra zeroth coordinate is
eliminated in the article's formulation. Empty supports and isolated donor
vertices are explicitly allowed.

Su Ho Oh, *Generalized permutohedra, h-vectors of cotransversal matroids and
pure O-sequences*, Electronic Journal of Combinatorics 20(3) (2013), P14.
https://arxiv.org/abs/1005.5586

The specific positive-coordinate counting input is attributed to Oh's
Lemma 22 and Proposition 26 in the Ohsugi–Tsuchiya proof. Oh's work includes
bijections; the present paper does NOT claim that no lattice-point/matroid
bijection previously existed. An effective, restriction-compatible map for
the current sampling and formalization goals is left as a separate target.

## Classical matroid representation

Egon Balas, William R. Pulleyblank,
*The perfectly matchable subgraph polytope of a bipartite graph*,
Networks 13 (1983), 495–516.
https://doi.org/10.1002/net.3230130405

Kenta Mori, *Toric Rings of Perfectly Matchable Subgraph Polytopes*,
Graphs and Combinatorics (2023), Section 2.1.
https://doi.org/10.1007/s00373-023-02719-8

Mori explicitly attributes the bipartite transversal-matroid connection to
Balas–Pulleyblank. The original 1983 paper was not audited in full. The article
therefore gives the private-copy basis correspondence directly and does not
claim it as a new construction. Bases are sets: multiple matching witnesses
for the same support pair do not give multiple bases.

Robert Davis, Florian Kohl,
*Perfectly Matchable Set Polynomials and h*-polynomials for Stable Set
Polytopes of Complements of Graphs*, arXiv:2207.14759.
https://arxiv.org/abs/2207.14759

Used for the established graph-polynomial terminology and the distinction
between perfectly matchable vertex sets and edge matchings.

## Imported analytic and algorithmic theorems

Petter Brändén, June Huh, *Lorentzian polynomials*, arXiv:1902.03719v8.
https://arxiv.org/html/1902.03719v8

Used: Theorem 3.10 (matroid basis polynomials), Theorem 2.10 (nonnegative
linear substitution), Theorem 2.30 (homogeneous complete log-concavity), and
Example 2.26 (bivariate ultra-log-concavity). Proposition 2.33 records the
standard homogeneous root-concavity equivalence, which the article reproves
to track the covariance constant. Lorentzian does not mean real stable.

Nima Anari, Kuikui Liu, Shayan Oveis Gharan, Cynthia Vinzant,
*Log-Concave Polynomials II: High-Dimensional Walks and an FPRAS for Counting
Bases of a Matroid*, arXiv:1811.01816.
https://arxiv.org/abs/1811.01816

Theorem 1.1 gives the weighted basis down-up walk mixing estimate; the
paper also gives the general approximate-counting implication. These are
imported results, not a new Markov-chain theorem. The present article supplies
an explicit matching oracle, the relevant weight/encoding bounds, and a
log-concave tilting reduction for individual coefficient recovery.

## Repository sources

https://github.com/VladimirReshetnikov/ProveIt/tree/e9a57d735db2177a8cca6aaecd95a3d53a0ba678

Target:
`SetTheory/Cardinals/docs/reports/enumerative-combinatorics/preorder-root-polytopes/`

The four-part report's research questions include coefficient shape beyond
gamma-positivity, exact counting complexity, effective demand/support
bijections, and support-size limit laws. This article settles gamma
ultra-log-concavity only for height-two posets, while proving the ordinary
support-polynomial inequality for all finite preorders. It does not treat
an unrefereed repository result as machine-verified merely because related
projects use Lean.

The Theta_3 polynomial (1,9,24,16,1) and the prior small real-rootedness
counterexample are credited to the existing report, which credits Shivam
Patel for the earlier example. No new discovery of that counterexample is
asserted here.

## Dependence and non-claims

The central ordinary-coefficient theorem uses a published counting bridge
plus classical matroid/Lorentzian inputs. Its preorder specialization has a
direct ideal-to-neighborhood proof and does not depend on the repository's
unrefereed simplicial realization or universal gamma theorem. The height-two
gamma corollary uses the finite common-support cancellation identity, whose
proof is included.

The covariance and tilting arguments are written proofs. Exact finite
computations audit normalizations and implementations; they are not substitutes
for those proofs. The reference sampler is implemented, but the entire FPRAS
reduction is not packaged as a production software system.

Not proved: arbitrary-preorder gamma log-concavity, flag realizability,
unrestricted real-rootedness or stability, exact polynomial-time counting,
binary-capacity polynomial complexity, or uniform sampling of actual demand
vectors. No worldwide novelty or proof-assistant certification is claimed.
