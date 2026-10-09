# Source and provenance audit

Research/retrieval date: 9 October 2026.

## Repository reference

Repository: https://github.com/VladimirReshetnikov/ProveIt

Reference revision: `cd984a34c0e06e467f3403576afbe6deeb1b5d11`.
The GitHub connector returned that commit with timestamp
`2026-10-09T22:10:53Z`. All access was read-only.

Inspected material included the top-level UnknotRecognition README, its report
catalogue through reports 64–69, the selected synthesis text
`Topology/UnknotRecognition/synthesis/completion_theorems.tex`, the incoming
folder inventory and its intake README, and relevant native-code searches.
The catalogue and intake reads were made from `main` immediately before
recording the reference pin; those listing reads are not represented here as
separate full historical-tree audits.

The direct native target read was explicitly pinned:

```
Topology/UnknotRecognition/fast/fastunknot/normal_boundary_geometry.py
Git blob: f43dc70b7e1553b3a56830aebbe76e39cb82e6fb
```

Its `boundary_weight_system` contract uses two independently validated torus
cycles and simple boundary-circle orbits. The parity test is correct for
that torus contract. This package identifies no defect in it. The proposed
extension concerns higher-genus closed boundary surfaces in a hierarchy.

The inspected synthesis and report catalogue distinguish component topology,
boundary essentiality, source provenance, and actual runtime integration.
That distinction is preserved here. No individual incoming archive was fully
unpacked and audited in this session. Reading the folder inventory/catalogue
is not an audit of every incoming manuscript.

The GitHub connector supplied the necessary texts. A container checkout was
not available because the attempted network path did not resolve; no local
upstream checkout or upstream test suite was used. No maintained repository
file, branch, commit, or pull request was created or modified.

## Primary literature consulted

### Livingston

Charles Livingston, *Maps of surface groups to finite groups with no simple
loops in the kernel*, arXiv:math/0002162; Journal of Knot Theory and Its
Ramifications 9 (2000), 1029–1036.
https://arxiv.org/abs/math/0002162

The abstract and bibliographic record were inspected. They state the genus-two
order 32 and the g^(2g+1) upper bound. Full-PDF access was not successful in
this session. Attribution is also supported by Pikaart's discussion. The
article does not claim to have audited Livingston's complete original proof;
it supplies a self-contained coordinate argument instead.

### Pikaart

Martin Pikaart, *Large characteristic subgroups of surface groups not
containing any simple loops*, arXiv:math/0005093v2.
https://arxiv.org/abs/math/0005093

The abstract, PDF text, and relevant rendered PDF pages were inspected,
including the odd/even distinction and the intersection-form central
quotient. Proposition 1.1 gives the characteristic indices
`g^(2g+1)` for odd g and `(2g)^(2g)*g` for even g. The present package does not
claim invention of the quotient or of the even-genus enlargement.

### Malestein–Putman

Justin Malestein and Andrew Putman, *Pseudo-Anosov dilatations and the Johnson
filtration*, arXiv:1307.6226v3; Groups, Geometry, and Dynamics 10 (2016),
771–793; DOI 10.4171/GGD/365.
https://arxiv.org/html/1307.6226v3

The relevant text, especially Lemmas 4.5–4.6, was inspected. Lemma 4.5 is the
classical topological lifting input. The report proves its converse and
uses the resulting exact criterion to derive the finite-bank theorem.

### Chambers–Lazarus–de Mesmay–Parsa

*Algorithms for Contractibility of Compressed Curves on 3-Manifold Boundaries*,
arXiv:2012.02352; Discrete & Computational Geometry 70 (2023), 323–354.
https://arxiv.org/abs/2012.02352

The abstract was inspected for its explicit uniform polynomial algorithms
for compressed surface loops and normal subgroup membership. This is why
this report does not claim the first polynomial algorithm for compressed
surface-word contractibility. Its own primitive has a narrower promise,
smaller explicit state, and complementary-genus information.

### Lackenby

Marc Lackenby, *Incompressible surfaces, hierarchies and unknot recognition*,
arXiv:2607.23350v1 (2026).
https://arxiv.org/html/2607.23350v1

The introductory boundary-pattern material and the Section 9 distinction
between stage control and sufficiently specified running-time estimates were
inspected. The report does not turn this local observer into a bound for the
entire hierarchy, and does not equate ordinary curve contractibility with
the violating-disc predicate for boundary patterns.

## Novelty and validation limits

The coisotropic interaction criterion and optimal fixed-cover-bank theorem
are proved in this package. No exhaustive literature-priority claim is made.
The group arithmetic is classical in substance. Code, finite tests, and
benchmarks were generated and run locally, rather than copied from the
maintained runtime. The final implementation has 47 passing unit tests.
There is no Lean or other proof-assistant verification in this delivery.

The final review removed an unnecessary eager table of all dense marked
generator vectors, which would have introduced a quadratic setup cost for
very short programs. A dedicated test now enforces lazy default generators;
all delivered timing records were regenerated after that change.

Only references and original explanatory material are shipped. No source
paper, external repository snapshot, or font file is bundled.
