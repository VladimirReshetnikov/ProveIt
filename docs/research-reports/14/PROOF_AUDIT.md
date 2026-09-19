# Proof and provenance audit

## A. Maximal fibers (Theorem 4.4)

External inputs: local Kunen inconsistency; high-critical-point ultraexacting
witnesses at sufficiently correct ranks.

Proof dependencies:

1. The critical sequence of an elementary self-map of V_lambda is cofinal in
   lambda; no ordinal in [crit(j), lambda) is fixed.
2. A fixed set of cardinality below lambda has cardinality below crit(j) and is
   permuted by j. An ordinal-valued such set is pointwise fixed.
3. A nonempty fixed family of cofinal omega-subsets has cardinality at least
   lambda (projection-width argument).
4. For a small fixed collection of such families, take all the small members.
   Their cardinality spectrum is a small fixed set of ordinals, hence lies
   below crit(j). Regularity of crit(j) makes their union small, contradicting
   step 3. This handles infinite permutation orbits.
5. Internal availability of j restricted to V_lambda puts the critical sequence
   and its shifted variants into the domain. Their finite-difference classes
   are fixed and pairwise distinct.
6. Fix a canonical least definable counterexample, not its arbitrary ordinal
   parameters. If its set of good classes has size nu < lambda, then nu is
   fixed and below crit(j); step 5 yields too many good classes.

Scope cautions: the main theorem concerns representative transversals, not
selectors of finite sets of quotient classes. Sharpness is proved for fiber
size only, not for the size of the collection. Ultraexactingness is essential
to the displayed internal-sequence argument.

## B. Bounded separation (Theorem 5.1)

External input: an exacting lambda is regular in HOD_(V_lambda).

Collect the least disagreement ranks of pairs of distinct members. This is a
small ordinal-definable set of ordinals, so it belongs to HOD_(V_lambda). If
unbounded, its canonical enumeration contradicts that model's regularity of
lambda. A bound gives injective restriction signatures in V_lambda. These
signatures define the individual members. The actual small bijection to the
signature set has rank below lambda and therefore belongs to the inner model.

Scope cautions: the family is a subset of V_(lambda+1), and ambient size is
strictly below lambda. No global well-order of V_lambda in HOD_(V_lambda) is
assumed.

## C. Equiconsistency (Theorem 6.1)

External inputs: Aguilera–Bagaria–Goldberg–Lücke's ultraexacting/I0
comparison and forcing that preserves ultraexactingness while coding V_lambda
into HOD.

The new principles are theorems from ultraexactingness, so they survive as
consequences in the model supplied by the coding theorem. The reverse
consistency implication forgets the extra principles. This calibrates a new
profile at a known strength; it does not improve the known bare comparison.
No passage from syntactic consistency to existence of a transitive model is
silently assumed.

## D. Successor obstruction (Theorems 7.2 and 8.4)

External inputs: fine-ultrafilter characterization of strong compactness;
for the HCD application, cover-exacting stationary hulls and Goldberg's HCD
ground theorem.

The general stationary-set mechanism is classical. Let theta be the inner
model's lambda-successor and S its set of points of cofinality lambda.
If theta is not collapsed, S becomes a nonreflecting subset of ambient
E_omega^theta. Strong compactness below lambda forces S to be nonstationary.
A theta-cc forcing would preserve theta and S, giving the contradiction.

The cover-exacting application obtains inner regularity from the
high-completeness cofinality barrier. That inherited barrier is rederived in
the report using principal traces on elementary hulls.

Scope cautions: the successor and antichain lower bounds are computed in the
ground. An ambient lambda-plus lower bound needs successor correctness.
Strong compactness is needed in the outer universe. This is not an argument
that every forcing singularization is impossible.

## E. Localization (Theorem 8.6)

External input in addition to D: the HCD ground forcing-size bound below
(2^(2^delta))^+.

The lower HCD core is a ground of V by forcing of size below lambda, because
lambda is strong limit. At the common successor this forcing preserves all
old stationary sets. Since S is nonstationary in V, it was already
nonstationary in the lower core. A club disjoint from S witnesses a concrete
difference between the two cores.

Scope cautions: successor correctness is explicit. No small presentation of
the universe over the upper core is assumed. No presentation of the lower
core over the upper core is needed.

## Verification limits

All new arguments are mathematical derivations supplied for review. They have
not been independently refereed or formalized in Lean or another proof
assistant. No finite experiment can verify the large-cardinal assertions, and
no computational test is presented as doing so. Primary sources and their
version numbering are recorded in the report; a worldwide novelty claim is
not made.
