# Claim and verification status

## Proposed structural results proved in the article

- Height-two matching-support identity and its gamma-positivity consequence.
- Closed perfectly-matchable-set polynomial for Theta_m and complete all-m
  real-root distribution, extending the earlier m=3 counterexample.
- Direct height-two orthant proof of the canonical root-polytope identity.
- Explicit cactus sixth-root matrix, all-square-minor identity, stable signed
  complementary-support polynomial, positive-weight determinant, and deletion
  interlacing. Absolute novelty of matrix techniques is not asserted.
- General induced-crown obstruction to arbitrary lattice triangulations and
  indispensable degree-r toric relations, with a real-rooted crown family.

These are written mathematical proofs, not proof-assistant certificates or
statements of independent peer acceptance.

## Credited prior results and examples

- Kálmán–Postnikov: normalized root-polytope volume counts hypertree vectors.
- Ohsugi–Tsuchiya / Davis–Kohl: the augmented bipartite edge-polytope Ehrhart
  numerator is the perfectly matchable set polynomial.
- Ohsugi–Tsuchiya: univariate real-rootedness for bipartite cactus graphs.
- Davis–Kohl and Ohsugi–Tsuchiya: the even-cycle matching-support formula.
- Stembridge / Ohsugi–Tsuchiya: the older degree-eight nonreal-rooted polynomial
  used in the 17-element construction.
- Shivam Patel's MathDB posting: the eight-element preorder counterexample
  corresponding to Theta_3. It predates this article according to the displayed
  relative posting date. The exact calendar posting date was not established.

The last item was found after the 17-element example was developed. The
article's title, abstract, introduction, provenance ledger, and conclusions
were revised accordingly. A first-disproof or minimum-size claim would be
incorrect and is not made.

## Not claimed

- General gamma-positivity for all preorders or for nontrivial block blowups.
- A disproof of existential flag realization (AC Conjecture 5.1(d)).
- Minimality of the eight-element example independently of the authors'
  reported small-size computation.
- Real-rootedness for every graph of treewidth two (the article proves failure).
- A characterization of all graphs admitting the cactus-style matrix.
- A canonical bijection in the matching–polymatroid cardinality lemma.
- Novelty of the old graph counterexample or univariate cactus theorem.
- Absolute publication priority for the new proposed structural statements.
- Lean verification, automated proof of all theorems, or community acceptance.

## Independent computational checks

Every supplied program was run successfully. The strongest finite comparisons
are the direct eight-element enumeration (1,281 points), the direct independent
17-element enumeration (8,408,566 points), and comparisons over all 512 labeled
3-by-3 bipartite graphs. The programs' exact outputs are supplied in `data/`.

The all-m theta theorem is proved by support classification, an exact positive
interval identity, and Descartes' rule plus sign evaluations. The finite Sturm
checks through m=20 are independent audits, not the proof of the all-m result.
