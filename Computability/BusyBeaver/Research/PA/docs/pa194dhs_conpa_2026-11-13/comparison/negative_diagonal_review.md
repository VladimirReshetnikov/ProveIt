# Independent review of the negative-only diagonal supplement

Pinned repository: `3cc7fbf75ba111a0da696ef2f6001dd528891bd5`.
Reviewed `source_work/pa194dhs/supplement/negative_diagonal.tex` and
`negative_diagonal_note.txt` against the inherited PA calibration and
the actual upstream PA196 logical proof operations. No mathematical gap
was found at the explicitly stated inherited calibration boundary.
The accepted PA194DHS machine is unchanged by this supplement.

## The fixed-binder lemma

Fix a numerical binder z and write box A = U(z,A). From a closed proof
of A -> box A, contraposition, closed generalization and h6 yield

    box(not(box A)) -> box(not A).

The h1 instance not(box(not(box A))) -> A, contraposed and followed by
double-negation elimination, gives

    not A -> box(not(box A)).

Composition proves not A -> box(not A). This is exactly the dependency
structure of `Logic/Vacuity.lean::negationVacuity`, using the numerical
constructors without any syntactic identification of double negations.

Apply it with A=not B to a proof of not B -> box(not B). Compose with
double-negation introduction on the left and the quantified
double-negation-elimination implication on the right. The result is
B -> U(z,B), with exactly the same z. The quantified last implication
is `liftImp z (doubleNegationElimination B)`, obtained by generalizing a
closed theorem and h6. No generalization under an unpaid assumption
occurs.

The bodies of `doubleNegationIntroduction` in `Logic/Reverse.lean`,
`doubleNegationElimination` and `explosion` in `Logic/Deduction.lean`,
and `negationVacuity` and `liftImp` in `Logic/Vacuity.lean` use no
equality-vacuity or diagonal-axiom constructor. Their propositional
operations come from the retained dominated implication basis.

Consequently Gamma(not B) proves B -> U(not B,B). This is not a claim
to recover Gamma(B) at binder B. Strict growth of the negation code and
the inherited label bound make not B a fresh label for B.

## The two calibration interfaces

For reverse membership rewriting, the inherited replacement chooses
C=E(a,b)->(chi(b)->chi(a)), phi=not C, and c=code(phi). Its only diagonal
requirement is literally Gamma(not C), an allowed restricted instance.
Thus its negative-property specialization, pointed separation and
collision cases remain unchanged.

For neighborhood equality, choose z0=code(not E(a,b)). The fixed-binder
lemma supplies E(a,b)->U(z0,E(a,b)); z0>E(a,b)>a,b. The exact upstream
neighborhood formula is

    R(a,b,z) = U(z,M(a,z)<->M(b,z))
               and U(z,M(z,a)<->M(z,b)).

The supplement now gives this exact definition. Lifting the recovered
two-way membership rewrites gives E(a,b)->R(a,b,z0). To transport to an
arbitrary allowed z, handle z=z0 by identity. Otherwise z differs from
a,b,z0, and z0 differs from a,b,z. The relevant membership matrices
therefore have all required membership-vacuity proofs at the opposite
binder. The existing witness and recovered rewrite proofs specialize
from z0 to z; h2 carries vacuity through the outer quantifier; closed
generalization and h6 finish the transport. No equality-vacuity axiom,
unproved alpha-conversion, or original-binder Gamma instance is used.
Existential monotonicity and neighborhood symmetry then provide the
unchanged witness interface.

## Dependency surface and limits

A source search of `PA196/Logic` and `PA196/Arithmetic/Certificates`
finds the uses of `equalityVacuity`, other than its own definition and
extraction, in `Reverse.lean` and `Neighborhood.lean` and their
arithmetic-certificate copies. Downstream relational `Interface.lean`
and `Alpha.lean` consume the recovered reverse-rewriting, neighborhood
and witness interfaces. These are precisely the interfaces changed by
the inherited diagonal calibration and the present supplement.

The restricted calculus is a subcalculus of the original sound
separate-head calculus. The forward refutation compiler can use the
replacement interface templates; the reverse arithmetic interpretation
therefore also restricts. The resulting refutation calibration is
supported by the ordinary syntactic proof argument, at the same explicit
logical-calibration boundary as the main report.

The supplement appropriately does not claim a newly elaborated Lean or
Rocq endpoint, a translation of every old diagonal axiom at its original
binder, or a smaller accepted Turing machine. The nine negative-schema
and 72 positive-offset compilation screens report optimistic fixed-layout
costs, not universally verified machines or global lower bounds. For the
positive-offset screen, only offset one receives a logical justification
in this supplement.
