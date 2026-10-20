# An entire class of three-input propositional replacements is too weak

## New theorem

Write

L(A,B,C,U) = ((C -> U) -> A) -> ((A -> C) -> (B -> C)).

In the native K calculus, replace unrestricted L by any effectively presented family of instances in which the fourth input U always has outermost constructor implication, universal quantification, or equality. The internal arguments of U may be completely arbitrary native codes; U may be chosen by arbitrary arithmetic functions of all available parameters, and any number of such restrictions may be emitted simultaneously. One may additionally retain all five earlier restrictions U=F, truth, A, B, C, and all instances of identity, ex-falso and the K combinator A -> (B -> A).

Keep every other native logical row, the full support-bearing seed-K bundle, modus ponens, and generalization. **ZFC proves consistency of this entire modified calculus.** Thus, assuming ZFC is consistent, its consistency cannot be provably equivalent in ZFC to Con(ZFC).

This theorem strengthens the earlier five-restriction obstruction from the pinned K219 packet. It excludes, in particular, U=C->F, C->A, A->C, Q_a C, E(a,b), arbitrary larger implication-headed terms, and arbitrary mixtures of these proposals. It does not exclude membership-headed fourth inputs.

## Finite matrix argument

Use values 0,1,2,3, with only 3 designated, falsum 0, and implication table

| -> | 0 | 1 | 2 | 3 |
|---|---:|---:|---:|---:|
| 0 | 3 | 3 | 3 | 3 |
| 1 | 3 | 3 | 1 | 3 |
| 2 | 3 | 3 | 3 | 3 |
| 3 | 0 | 0 | 0 | 3 |

There are exactly two failures of L among all 4^4 tuples:

(A,B,C,U)=(0,3,1,2) and (1,3,1,2).

Therefore L is designated for every A,B,C whenever U is in {0,1,3}. Every implication output lies in {0,1,3}. Every quantified formula and every equality atom in the HC realization has value in {0,3}. Truth code 0 has value 3. The claim holds without induction on the internal complexity of U: its outermost operation alone excludes value 2.

The independent script checks all 256 unrestricted tuples, all 192 uniformly allowed tuples, and the exact ranges of the three constructors. This is an exhaustive finite calculation, not sampling over numerical formula codes.

## Why this is a consistency-strength obstruction, including K

The infinite realization is the full HC model established in the predecessor packet's `research/theory/restricted_rho8_strong_countermodel.md`; the following describes the points needed for the new extension.

Work inside ZFC. The domain HC is the set of hereditarily countable sets. Choose an antichain encoding e:HC -> 2^omega and a map n:HC -> omega with uncountable fibers. For distinct p,u, choose a coordinate k with e(p)(k)=0 and e(u)(k)=1. Define membership values by

r(z,p)=3 if z is an actual member of p;
r(z,p)=0 if z=p;
r(z,p)=1+e(p)(n(z)) otherwise.

Equality has value 3 exactly for equal objects, and 0 otherwise. Quantification has value 3 exactly when every instance has value 3, and 0 otherwise. Native F=R(0,0) is therefore always 0. These interpretations satisfy all retained equality, quantifier, substitution, and vacuity rows, and preserve designatedness under both rules.

The native subset formula is designated exactly when the two objects are equal. For distinct p,u, select z in the uncountable fiber n^-1(k) outside the countable set p union u union {p,u}; then r(z,p)=1 and r(z,u)=2, giving a nondesignated implication.

Consequently the full native K principle, with its support condition retained, needs only countable closure under chosen witnesses. For any designated matrix relation Phi(y,p), choose a witness function g on the inputs having witnesses. Starting from a witness of the seed request, repeatedly adjoin g(u) for members u having successors. The resulting countable closure C belongs to HC; each of its members has support and every member's request has a witness inside C. If there is no seed witness, choose the empty set. Coincident public labels are handled by an empty or singleton container, as in the predecessor's complete proof.

The new restrictions on L do not change the interpretation of any other row or the K proof. Every new L instance is designated by the outer-head calculation. ZFC can construct HC, the coloring functions, the recursive finite-code evaluator and assignment set, and prove soundness by induction on a finite derivation. Hence it proves that F is not derived.

## Exact boundary

A membership-headed U can have value 2, so it is outside this theorem. For example U=R(a,b) fails in the ordinary HC realization: take the numerical row parameters a=1, b=0, c=R(2,3)=73. Then decoded A is falsum and B is truth. Assign the objects at labels 2,3 to give C value 1, and independently assign labels 1,0 to give U value 2. The prohibited tuple (0,3,1,2) occurs.

This only eliminates this particular HC model for that variant. It is **not a proof that the membership-headed variant is equiconsistent with ZFC**. A noncircular derivation or refutation translation remains necessary.
