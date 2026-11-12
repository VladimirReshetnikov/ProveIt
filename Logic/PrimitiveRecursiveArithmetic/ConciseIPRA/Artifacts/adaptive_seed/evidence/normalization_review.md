# Red-team review: hypothesis-only elimination majors

## Proposed reduction and scope

The proposed checker deletes recursive checking of an elimination major.
Each equality/closure/paired elimination may use its major only when that
formula is already a retained hypothesis. Computation equations can still
be supplied, and contextual literal-equation induction is added directly
at equation goals. The question is whether closed-theorem completeness
follows from ordinary natural-deduction normalization.

It does not follow from that normalization theorem. There is an immediate
counterexample if the current public Eq/Q/D language is preserved. If Q is
made strictly internal and excluded from public formulas, that specific
counterexample disappears, but an atomic-cut elimination theorem remains
necessary. I have not proved a general incompleteness theorem for every
possible revised Eq/D presentation with explicit atomic induction.

## An exact counterexample for the current Eq/Q/D interface

The current flat-computation report explicitly takes

    A ::= s=t | Q_y A | D_{x,y} A

as its actual native formula language, because its public checker accepts
raw Q goals. It gives Q_y A the reading A(0) -> forall y A(y), and derives
its equivalence with D having an unused first coordinate.

The original calculus proves the closed formula

    Q_y (0=0).

A derivation is:

1. Derive 0=0 by the computation/equality rules.
2. DI-case, ignoring its hypothesis, gives D_{x,y}(0=0).
3. DE opens this theorem to the hypothesis Q_y(0=0).
4. Hyp closes the desired Q conclusion; DE discharges the local hypothesis.

The D theorem at step 3 is a derived major, not a retained hypothesis.

In the proposed hypothesis-major-only calculus, Q_y(0=0) has no finite
closed derivation, provided the only additional introduction is induction
at literal-equation goals and computation supply adds equations.

Proof by induction on a hypothetical derivation: throughout a Q-root goal
branch beginning with empty context, computation supply and equation
induction hypotheses add only equations. Hyp therefore cannot close the
Q goal. DI introduces D, not Q. Equation induction concludes an equation,
not Q. Equality transport preserves the outer logical constructor, since
its substitution is numerical, so its minor is again a Q-root goal.
QE requires a Q hypothesis, and DE requires a D hypothesis; neither is
available. Thus every possible final rule either is inapplicable or
requires a shorter branch with the same impossible invariant.

This is a genuine nonderivability argument, not merely a failure of one
normalization algorithm. A new Q-introduction rule, a computation-like
supply for derived logical theorems, or exclusion of Q from the object
language changes the proposal and must be charged and proved separately.

## Why DI-progress creates a further normalization obligation

Consider the principal pair

    Gamma, E(t,z) |- E(t,Sz)
    ----------------------- DI-progress
    Gamma |- D_{x,y} E(x,y)

followed by DE, whose continuation uses Q_y E(b,y), with b fresh.
For ordinary existential introduction followed by existential elimination,
one substitutes the witness t and its proof into the continuation.
Here the supplied proof is not just a logically introduced closure: it
contains equation induction.

A use of QE in that continuation takes E(t,0) to E(t,n). With explicit
atomic induction at the goal, this particular conclusion can indeed be
proved. But E(t,n) can then be the major premise of equality transport
into an arbitrary native formula F. Deleting recursive majors forbids
exactly that use unless the induction result is put into the context.

In ordinary natural-deduction proof terms the obstruction is

    transport(ind_E(base, step, n), minor)

where n is a parameter. It is neutral under the usual logical beta
reductions: induction unfolds at 0 or a displayed successor, not at an
arbitrary parameter. The major is an equation, so reducing formula
complexity cannot remove it. Logical normalization can remove maxima for
implication, conjunction and existential introduction, while leaving this
induction-generated atomic cut.

For a familiar instance, take addition recursive in its second argument
and E(n) := 0+n=n. Induction proves forall n E(n). Applying its instance as
an equality major proves F(0+n) -> F(n) for any fixed formula F. The displayed
proof contains precisely the neutral induction/transport combination.
This example demonstrates why ordinary logical normalization is insufficient;
it does not assert that no other proof of that particular formula exists.

A naive commuting conversion replaces the induction motive by

    F(s(n)) -> F(t(n)).

This can be compound or quantified and is not an allowed induction matrix.
Even when the target is an equation f(s(n))=f(t(n)), the original step proof
may need s(n)=t(n), which cannot in general be recovered from the new
induction hypothesis when f is noninjective. A valid compiler might use
strengthened atomic invariants, finite equation tuples and arithmetic coding,
but every such operation and all its prerequisites must be proved in the
restricted target system. It cannot be assumed from ordinary cut elimination.

## Consequences for inherited bi-interpretability proofs

Several inherited native developments explicitly use arbitrary derived
majors and finite substitution of derivations (ordinary assumption cut).
Examples include:

- deriving contextual numerical cases by DI-case, then DE and QE;
- deriving equation induction by DI-progress, then DE and QE;
- restricted Boolean implication elimination in the successor-seeded
  arithmetic bootstrap;
- contextual Boolean case analysis, which uses a derived compound closure;
- the Q/D round-trip when Q is treated as an object connective;
- preservation of formula interderivability underneath D.

Deleting recursive majors does not automatically preserve those derivations.
In particular, ordinary assumption-cut admissibility by replacing a Hyp leaf
with a proof no longer applies: a leaf used in an elimination-major position
is no longer permitted to be replaced by an arbitrary derivation.

## Other mathematical audit points

I did not find a new countermodel to the original full native calculus during
this scoped review. The original ordinary interpretations of Q and D make
its displayed rules sound, assuming the stated equation induction and
numerical coverage. The existing reports explicitly recognize several
important issues:

- numerical computation alone cannot yield separation from an independent
  ordinary falsity, because a singleton model satisfies positive equations;
- equality characteristics must reflect actual equality internally, not just
  standard-numeral evaluation;
- scalar iteration must reconstruct predecessor and pairing before claiming
  compilation of all primitive recursion;
- passive parameters cannot change inside a literal-equation induction;
- both interpretation composites need internal proofs, not just mutual
  theorem translations or equiconsistency;
- arbitrary formula transport and compound numerical case analysis are used
  before the full logical interface is reconstructed and need native proofs.

The successor-seeded bootstrap addresses the potential early-use-of-logic
circle by giving a restricted Boolean implication and contextual Boolean-case
derivation. That derivation itself relies on derived-major elimination and
cut, so it cannot be imported unchanged into the proposed restricted checker.

## Recommendation

Retain recursive checking of derived majors unless the replacement has one
of the following independently proved mechanisms:

1. a verified local lemma/supply rule that makes every needed derived major
   available, with correct context and eigenparameter discipline; or
2. a complete normalization/compilation theorem into hypothesis-major proofs,
   explicitly treating atomic induction cuts and the chosen public status of Q.

The current evidence does not justify claiming that ordinary normalization
alone supplies mechanism 2.
