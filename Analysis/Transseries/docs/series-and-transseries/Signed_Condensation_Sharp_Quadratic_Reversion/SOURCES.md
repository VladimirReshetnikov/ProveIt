# Sources and provenance

Inspected September 29, 2026. GitHub was read through the connected GitHub
interface; primary literature metadata was checked on arXiv. No repository
write operations were performed.

## Fixed repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Commit: `aab173a7ccdd48add72191d68ce6b0c12ffd72fe`

### Principal research source

`Analysis/Transseries/docs/series-and-transseries/Finite_Core_Universality_Exponential_Feedback/article.tex`

Blob: `c2b6faf623003111e9d9e6bbb162a67429f3ce42`

https://github.com/VladimirReshetnikov/ProveIt/blob/aab173a7ccdd48add72191d68ce6b0c12ffd72fe/Analysis/Transseries/docs/series-and-transseries/Finite_Core_Universality_Exponential_Feedback/article.tex

Title: *Finite-Core Universality and Sharp Large Order for Countable
Exponential-Feedback Transseries*.

Audited portions: model and main statements (source lines 100--385),
macroscopic concentration and forward mass-transfer proof (490--785),
recorded inverse diagnostics and open problems (1530--1740). The conjecture
itself was rechecked at source lines 1660--1678. Its environment is lines
1661--1668. Relevant source labels are `prop:inverse-response`,
`conj:quadratic-inverse`, `eq:inverse-conjecture`, and `thm:explicit`.

The exact response identity is established there, while the text explicitly
identifies exhaustion by the one-tail response as the missing step. The
new report supplies that step with a cutoff large enough to give an
arbitrarily small polynomial absolute error.

### Repository inventories

- `Analysis/Transseries/README.md`.
- `Analysis/Transseries/docs/series-and-transseries/README.md`, especially
  descriptions of the finite-core, microscopic-condensation,
  sharp-weighted-type, and negative-direction-summability packages.

https://github.com/VladimirReshetnikov/ProveIt/blob/aab173a7ccdd48add72191d68ce6b0c12ffd72fe/Analysis/Transseries/docs/series-and-transseries/README.md

The inventory's statements about other research packages are not treated as
independent verification of all their theorems. No result from those other
packages is needed for the new inverse proof.

## Primary literature

1. Ira M. Gessel, *Lagrange Inversion*, Journal of Combinatorial Theory,
   Series A 144 (2016), 212--249.
   https://arxiv.org/abs/1609.05988
   DOI: 10.1016/j.jcta.2016.06.018.
   Role: established inversion machinery; the specialization used is proved
   in the manuscript.
2. Sabine Jansen, Tobias Kuna, Dimitrios Tsagkarogiannis, *Lagrange inversion
   and combinatorial species with uncountable color palette*, Annales Henri
   Poincare (2021).
   https://arxiv.org/abs/2008.10862
   DOI: 10.1007/s00023-020-01013-0.
   Role: context for infinite-colour inversion, not an imported technical lemma.
3. Michael Borinsky, *Generating asymptotics for factorially divergent
   sequences*, Electronic Journal of Combinatorics 25(4) (2018), P4.1.
   https://arxiv.org/abs/1603.01236
   DOI: 10.37236/5999.
   Role: comparison with a fixed-factorial asymptotic calculus, and a proposed
   research direction for moving-saddle coefficient algebras.
4. G. A. Edgar, *Transseries for beginners*, Real Analysis Exchange 35 (2010),
   253--310.
   https://arxiv.org/abs/0801.4877
   Role: general formal-transseries context.

## Novelty and attribution boundary

Classical Lagrange inversion, coefficient majorants, Stirling's formula,
and discrete saddle methods are not claimed as new. The explicit research
advance is the signed quadratic inverse equivalent and the extension and
consequences proved in this manuscript. The main pure-model expression was
already conjectured by the repository source; it is not presented as a
newly discovered conjectural formula.
