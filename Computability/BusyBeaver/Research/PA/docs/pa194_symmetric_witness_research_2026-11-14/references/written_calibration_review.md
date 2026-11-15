# Review of the AX11H written iPRA calibration

Snapshot reviewed: `3c3bf00e3132d31d328a7bcfe79761ef238eced3` of
`VladimirReshetnikov/ProveIt`.

## Result and scope

The packet `PA/docs/pa194_ax11h_research_2026-11-14_2` explicitly claims a
complete **written mathematical iPRA calibration**, separately from its
unfinished proof-assistant implementation. It is inaccurate to classify
this packet as supplying only a conditional theorem because the top-level
PA README says the Lean machine endpoint is open.

I read all three completion fragments `foundation_paeq_completion.tex`,
`term_leaf_completion.tex`, and `forward_calibration_completion.tex` (2,384
source lines), together with the concluding equivalence and source-soundness
fragments. I checked the particularly sensitive equality-vacuity boundary
against the actual logical and arithmetic-certificate source, and checked
the form of the fixed primitive-totality and ordinal seed derivations.
I found no defect in those reviewed mathematical steps. This is a bounded
independent review, not a new complete proof-kernel verification, execution
of the enormous PA proof compiler, or independent audit of every transitive
lemma in its implementation. The archive's stronger theorem remains an
attributed written result when used by a new machine construction.

## The real improvement in the completion fragments

The important change is not an assertion that every intuitive proof
translation is primitive recursive. Each recursive proof request carries
a numerical rank and a finite environment packet. Its child requests are
computed **before** any child proof outputs are returned, and same-family
ranks strictly decrease. There are at most two same-family children.
Generate a complete binary request tree to depth one more than the root
rank, using inactive placeholders, and evaluate it backwards. Both loops
are bounded primitive recursions. A forward Boolean invariant checks valid
child queries and coverage; a reverse Boolean invariant checks the proof
and conclusion stored at every already evaluated valid query. These are
legitimate quantifier-free induction invariants in the PR language.

Calls to a previously completed stratum may increase the requested syntax
code. This causes no cycle. In particular a bound-variable realization
request can ask for uniqueness of its replacement term, whose code may
exceed that of the variable, only because uniqueness has already been
completed separately. This point is correctly handled in the text.

The Foundation adapter is also concrete: it identifies the ten logical
proof constructors, supplies an explicit opening/closing chain, respects
the exact canonical parameter count of induction axioms, and handles the
historical/current `addEqOfLt` change by an explicit existential projection.
It checks the metatheory as well: the current finite arithmetic base proves
the historical bounded positive-difference axiom, and the historical prenex
Sigma-one induction formulas are included in the current hierarchy.

## Equality-vacuity boundary: an actual source check

A recursive text scan of the actual `PA196/Logic` and
`PA196/Arithmetic/Certificates` trees found precisely two consumers of
primitive `equalityVacuity` beyond its definition and `#print` statements:

* `Reverse.lean`, in the last premise of `reverseChi`;
* `Neighborhood.lean`, in `primitiveToNeighborhood`.

The pattern is identical in the arithmetic certificate mirror.
This confirms the dependency boundary asserted by the written completion.
The `negativeSpecialization` proof in the actual `Reverse.lean` uses the
equality witness, direct membership rewrites, and membership-only vacuity;
it does not use primitive equality vacuity.

For the first replacement, let

    C = E(a,b) -> (chi(b) -> chi(a)), phi = not C, c = code(phi).

The point is to choose the separator property as the negation of the entire
desired conclusion. Under phi, the point condition `phi -> M(c,a)` gives
`M(c,a)`, direct rewriting gives `M(c,b)`, and negative specialization of
the separation matrix contradicts `chi(b)`. Therefore
`phi -> (S -> not P)`. Generalization at c, universal distribution, and
the literal diagonal head `phi -> U(c,phi)` yield `phi -> Q`, contradicted
by the gate's `not Q`. Double-negation elimination supplies C.

This is a modified derivation. The old `reverseFromProperty` constructor
cannot simply be reused verbatim: it expects both property-to-negation
and negation-to-property premises, and the latter would be false for the
new choice. The written proof correctly rebuilds the needed core under
phi rather than invoking that old constructor unchanged.

For the neighborhood replacement, choose `z0 = code(E(a,b))`. The diagonal
head supplies equality vacuity at this one binder, which gives
`E(a,b) -> R(a,b,z0)`. For another binder `z != a,b,z0`, both directions of
membership rewriting give

    E(z,z0) -> (P(z0) -> P(z))

for each of the two membership-only neighborhood matrices P. The equality
witness at z0 and membership-only vacuity give
`U(z0,P(z0)) -> P(z)`; the antecedent is vacuous at z, so generalization
gives `U(z0,P(z0)) -> U(z,P(z))`. This replaces the second and last
primitive equality-vacuity consumer. The collision cases are handled
separately as in the supplied direct derivations.

## Fixed leaves and arbitrary properties

`RelationalClosedCertificateSeeds.lean` defines actual `Derivation`
objects for inhabited zero and successor/addition/multiplication totality
at explicit standard reserves. `RelationalClosedCertificateOrdinalSeeds`
does the same for reflexivity, symmetry, congruence, transitivity,
intersection, and adjunction. They are finite proof recipes, not a
PA-calibration axiom. The completion reinterprets their logical boundary
through the two replacements above.

Those fixed recipes need not have their enormous numerical encodings
printed to serve as fixed constants in a mathematical PR construction.
However, their existence does not by itself supply an arbitrary-property
induction schema. The completion handles that separate task: arbitrary
source separation is supplied first; the ordinal-induction template has
six fixed leaves and that one separation leaf; arithmetic formula
realization and the explicit canonical-matrix and universal-closure loops
then supply each ordinary PA induction instance. The declared dependency
order is acyclic and avoids the previously unbounded all-environments
induction.

## What a new table may safely inherit

A new construction can prove its exact blank-start halting equivalence to
the pinned AX11H or QAX11H table by its own positive-duration simulation
and command interpretation. Composing that result with the **attributed
written AX11H theorem** gives the requested iPRA consistency equivalence
at the level of ordinary mathematical proof. The report should give that
inheritance explicitly and preserve the different status of (1) fresh
finite transition/certificate checks, (2) fresh relative mathematical
proofs, (3) the inherited written absolute calibration, and (4) the still
unfinished end-to-end Lean endpoint.

The weaker primary packet's PA-only calibration should not be silently
used as an iPRA calibration. Conversely the top-level Lean status must not
be used to erase the later written iPRA argument.

## Reduction route rejected for a mathematical reason

The equality-free radix-three shortcut is already ruled out in
`pa1944l_research_2026-11-14/theory/bounded_compiler_and_radix3.tex`.
The displayed primitive-recursive Boolean valuation validates the retained
gate, diagonal, logical heads, and inference rules while falsifying code
one. It gives an iPRA consistency proof of that weakened calculus. Dropping
only the equality-witness head admits the same obstruction with every
equality atom assigned zero. Neither deletion is a valid state-saving
route to the PA refutation problem.
