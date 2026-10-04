# Proof audit and hypothesis ledger

## 1. Principal proof

**Ambient setting:** ZFC; set-sized carriers; Hausdorff additive topological
groups. The ring is nonzero and unital, and 1 is its least positive element.

1. In a nondiscrete Hausdorff topological group, each singleton is nowhere
   dense. If P and -P were meager, G = P union {0} union (-P) would be
   meager in itself. Baire therefore makes P nonmeager.
2. The Baire property supplies a nonempty open U where P is comeager.
   Choose u in U intersection P. Reflection makes 2u-P comeager on 2u-U.
   Their domains have the nonempty open intersection U intersection (2u-U),
   containing u. Hence (0,2u) is nonmeager with the Baire property.
3. Pettis, proved in the manuscript, gives an open W containing 0 inside
   (0,2u)-(0,2u), so W is order-bounded. The discrete case uses W={0}.
4. Write W subset (-a,a) and b=2a+1. Distinct r,s satisfy |r-s| >= 1,
   hence |b(r-s)| >= b > 2a. But W-W subset (-2a,2a). Thus br+W and bs+W
   are disjoint.
5. The translates are open because translation is a homeomorphism. The
   map r -> br is NOT assumed continuous or measurable.
6. There are |R| such sets. The elementary inequalities c(R)<=d(R)<=|R|
   give equality. Under ccc, R is countable; the countable Baire-group
   singleton argument makes its topology discrete.

## 2. Separate Haar-measure route

Completed Haar measurability is required for the ambient cone, not for
its restrictions to arbitrary null subgroups. In a nondiscrete locally
compact group, Haar measure of a singleton is zero. Intersecting the
positive/negative partition with a compact positive-measure set, and using
inner regularity, produces compact B subset P of positive finite measure.

A sigma-compact open subgroup containing B is obtained by adjoining B and
-B to a compact identity neighborhood and generating a subgroup. Tonelli
is applied in that sigma-finite subgroup. The integral of
mu(B intersection (a-B)) equals mu(B)^2. Some compact intersection thus has
positive measure and lies in (0,a). The compact Steinhaus proof gives an
order-bounded neighborhood. The same algebraic packing finishes the proof.

No structural decomposition of a locally compact abelian group is used.

## 3. Additional assertions

| Result | Essential hypotheses / proof boundary |
| --- | --- |
| Principal convex quotient has cardinality \|R\| | A nonstandard discretely ordered ring; H_a is an additive subgroup, not an ideal. Multiplication by (a+1)c escapes H_a for all nonzero differences. |
| Unit-image spectrum is bounded | Uncountable ordered Baire ccc group, BP cone, least positive element. Embeddings are arbitrary algebraic ordered additive embeddings. |
| No positive-semiring expansion | Cone of the specified group, prescribed addition and unit, cancellativity inherited from the group. Difference multiplication is proved well-defined. |
| Borel non-Polishability | The new topology must generate the specified Borel structure, keeping the cone Borel. |
| Meager Borel subgroup | Ambient group is Polish; carrier and positive cone are Borel in the ambient group. A nonmeager subgroup would be open and hence Polish. |
| Omnific application | A set-sized unital subring with inherited discrete order. No proper class is called a Polish space. |
| Completion has no discrete order | The formal series ring contains the nontrivial unit 1-t. Every unit of a discretely ordered ring is +/-1. |

## 4. Sharpness

All three principal examples have the SAME abstract ring Z+t R[t].

- Coefficient subspace topology: separable, metrizable, continuous ring
  operations, Delta^0_2 cone; meager in itself, so not Baire.
- Real t-coordinate times a discrete complementary group: locally compact,
  Hausdorff Baire, Delta^0_2 cone, density and cellularity continuum; not ccc.
- Topology transported through a rational-vector-space basis isomorphism
  to Z times Q^N with discrete rational coordinates: Polish additive group;
  the inherited order cone necessarily fails the Baire property.

The ordinary real field drops the least-positive-element hypothesis.
The lexicographic additive group R plus Z demonstrates that regular
continuous addition alone is possible without a compatible ring expansion.

## 5. Non-claims

- No automatic Polish group completion of an arbitrary positive monoid.
- No resolution of Glazer's ATR_0 question.
- No independently established historical priority.
- No proof of unrelated repository claims.
- No Lean/Rocq kernel check of this manuscript.
- No inference from finite random tests to infinite topological theorems.

## 6. Mechanical checks performed

The supplied Python script passed 36,989 exact checks using a fixed seed.
The PDF was built with pdflatex, with all references resolved and no
overfull-box warnings. All 23 pages were rendered for layout review;
the central category/packing proof and measure proof were also inspected
at a readable page scale. These checks address implementation and layout,
not independent certification of the mathematical theorems.
