# Literature search for the odd-order uniformity comparison

Search and source inspection carried out on 7 October 2026, UTC. This is a
targeted search, not a complete bibliography or a certification of priority.
Only author, journal, institutional, or arXiv sources are used below as evidence.

## Questions searched

1. Has the sharp inequality `||f||U2^4 <= ||f||infinity^4/3` for centered real
   functions on finite abelian groups of odd order already appeared?
2. Has the order-N refinement
   `1/3 - 4/(3N^2) + 1/N^3` appeared for the same bounded problem?
3. Has the group-uniform limit of
   `sup ||f||U2^4/||f||Ud^4` as d tends to infinity been identified?
4. Is the argument a direct instance of a known fixed-order near-extremizer or
   compact-group rearrangement result?

## Exact query log

Queries were run through both available web-search engines. Repeated variants
are recorded because exact-phrase queries often returned irrelevant material.

    "Gowers norms" "1/3" "real"
    "Gowers norms" "infinity" "limit"
    "Fourier" "mean zero" "one third" "bounded"
    Gowers uniformity norm high order limit L infinity real mean zero
    "Gowers" "one-third"
    "autocorrelation" "R(2" "1/3"
    "Fourier coefficients" "fourth powers" "bounded"
    "Gowers norms" "as the order"
    "Gowers" "real-valued" "odd" "norm"
    "autocorrelation" "triangle inequality" "binary" "squared"
    "autocorrelation" "balanced" "maximum" "energy" sequences
    "Gowers norms" "supremum" "order" "limit"
    "Fourier" "bounded real" "1/3"
    "Riesz" "mean zero" "convolution"
    maximal Gowers U2 norm mean zero real function odd cyclic group
    Fourier fourth moment maximum balanced binary sequence cyclic
    autocorrelation bounded real stationary process one third inequality
    Riesz Sobolev inequality compact abelian group disconnected Pollard
    "Gowers" "norm" "tends to" "infinity norm"
    "Gowers" "norm" "converges" "supremum"
    "Gowers" "1/3" "centered"
    "Gowers" "1/3" "mean zero"
    "Gowers" "real" "centered" [recency 3650 days]
    "autocorrelation" "1/3" "odd" [recency 3650 days]
    "Gowers" "high-order" "comparison" [recency 3650 days]

No returned primary source was found to state the new uniform comparison
theorem or the exact finite-N bounded inequality. Many exact queries had poor
precision; this absence of a hit is weak evidence and must not be presented as
proof that the statements have never appeared elsewhere.

## Primary sources actually opened and inspected

### Eisner--Tao: fixed-order near-extremizers

Tanja Eisner and Terence Tao, *Large values of the Gowers--Host--Kra seminorms*,
arXiv:1012.3509v2 (2011).

* Abstract and source: <https://arxiv.org/abs/1012.3509>
* Full text: <https://arxiv.org/html/1012.3509v2>
* Inspected: introduction, definitions (1)--(7), Theorem 1.1, and organization of
  the remaining theorems. In-text searches for `real-valued` and `odd` gave no
  matches in the fetched full text.

This paper gives the standard recursive definition, U2 Fourier identity, norm
property, and upper bound by Linfinity. Its Theorem 1.1 characterizes equality
and near-equality at a fixed Gowers order by polynomial phases, with an error
term depending on the fixed order. It does not, in the inspected statements,
give the present uniform-as-order-grows supremum ratio for centered real functions
on odd groups. Those are different quantifiers and a different extremal problem.

### Host--Kra: dual norms and dual functions

Bernard Host and Bryna Kra, *A point of view on Gowers uniformity norms*.

* Author-hosted PDF: <https://sites.math.northwestern.edu/~kra/papers/gowersnorms.pdf>
* Inspected: abstract and introductory description, compact-group scope, and the
  dual-function decomposition framework.

The paper studies dual norms/functions and related algebra and decomposition
properties. Its compact-group framework is relevant context. No matching
odd-order high-degree comparison constant was found in the inspected material.
This report does not claim to have checked every theorem in the paper for an
indirect implication.

### Christ--Iliopoulou: connected compact-group rearrangement

Michael Christ and Marina Iliopoulou, *Inequalities of Riesz--Sobolev type for
compact connected Abelian groups*, arXiv:1808.08368v2 (2019).

* Abstract and source: <https://arxiv.org/abs/1808.08368>
* Full text: <https://arxiv.org/html/1808.08368v2>
* Inspected: introduction; Theorems 1.1, 1.2, and 1.5; explicit scope discussion
  for groups not necessarily connected; attribution preceding Definition 1.1.

Their Theorem 1.1 compares indicator-function convolution integrals on a compact
connected abelian group with centered-interval rearrangements on the circle.
Theorem 1.5 also addresses functions taking values in [0,1]. The paper credits
earlier work on the circle and states that the general connected-group
inequality is equivalent to a formulation of Tao. Thus circle interval
extremizers and rearrangement methods should be treated as classical context.

Finite odd groups are disconnected, and the paper explicitly says that the
not-necessarily-connected setting is more complicated. The present elementary
doubling proof works on finite odd groups directly and does not assume
connectedness. No claim of novelty for the circle square-wave model is warranted.

## Recommended status language

The present manuscript proves the stated inequalities and resolves the
limiting-constant question posed in the inspected ProveIt reports. It provides
complete proofs and a uniform quantitative upper bound. The targeted literature
search did not locate an identical theorem, but does not establish independent
publication priority. No claim is made that a recognized longstanding open
problem in the wider literature has been settled.
