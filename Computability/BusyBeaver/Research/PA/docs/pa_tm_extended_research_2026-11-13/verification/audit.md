# Independent logical audit

Sources pinned on 13 November 2026:

- `jamesyc/BusyBeaver@407cdc356f6b586635e71ac92be394255f4bfea4`.
- `VladimirReshetnikov/ProveIt@f1f076e31995f10460838d1846456f4bb9c8ae80`.

## Exact upstream endpoint

`PA196/Independence.lean`, `pa_proves_nonhalting_consistency`, proves
PA |- Nonhalt(PA196) -> Con(PA). The same file supplies external
two-sided unprovability. `PA196/Logic/Soundness.lean` explicitly says its
soundness proof is external and is not a PA proof of consistency. The
source nonhalting invariant invokes this external soundness theorem.

Consequently a full PA-internal biconditional is not an upstream Lean
endpoint. A new table equivalent to PA196 cannot acquire that stronger
formal status merely from a state simulation.

The existing incoming package `pa_tm_research_2026-11-13` already records
this distinction and gives a written reverse proof compiler in
`report/pa_reverse_translation.tex`. I independently checked the main
argument: interpretation by binary membership, proof-producing bounded
comprehension using full PA induction, the coincident-label gate case,
code-zero implication collision, and annotated proof extraction are sound
as a mathematical construction. Its final list of missing encoding and
literal-trace bindings is material. Repeating this argument does not
constitute a new formalization or remove those obligations.

## New T-only countervaluation

A tempting reduction replaces head 1

    (exists x_d forall x_d H) -> H

by the shorter ordinary universal-instantiation head

    forall x_d H -> H.

There is a direct all-instance countervaluation to recovering the old
head, or explosion, from this replacement and all other exact PA196
rules. Interpret code zero as true, implication as Boolean implication,
every quantifier U(d,H) as the truth value of H, and both atomic
constructors M(a,b) and E(a,b) as truth iff their numerical labels a,b
are equal. In particular code one M(0,0) is true, whereas code nine
M(0,1) is false.

Every proposed T instance and every quantifier-commutation instance is
an identity. Head 6 is the propositional tautology
A -> ((A -> H) -> H). The two membership-rewriting heads follow from
equality of their numerical labels. Existential head 5 is true, since
the existential's outer relative negation has consequent code one.
Every guarded gate is true for the same reason. The restricted
propositional head is a Boolean tautology. Modus ponens preserves truth,
and generalization preserves it because U is interpreted as the identity.
The exceptional code I(0,0)=0 respects the interpretation too.

Nevertheless the old head at (d,H)=(0,9) is false: its antecedent is
true and its consequent false. Likewise 1 -> 9 is false. Thus neither
the old head nor explosion is derivable in the modified calculus. This
is a countervaluation of the numeric calculus, not a first-order model,
and it does not itself prove that the modified calculus lacks every
possible PA-refutation interpretation. It does refute the proposed
straight replacement justified by recovering the old rules.

`t_replacement_countermodel.py` implements supplementary finite checks.
The preceding schema argument, rather than the finite enumeration,
establishes the all-instance claim.

## Exact point where quantifier commutation is used

The new reverse membership arguments in `PA196/Logic/Reverse.lean` and
all three equality interfaces in `PA196/Logic/Neighborhood.lean` avoid
head 2. Their vacuity arguments concern formulas built from atoms by
implication and relative negation. In `Vacuity.lean`, head 2 is used by
`universalVacuity`, which transports freshness through a universal
binder. `Logic/Relational/Encoding.lean` subsequently uses that lemma
for arbitrary relational formulas. `Logic/Relational/Interface.lean`
uses it for neighborhood equality and bound-variable renaming.

This sharply localizes a possible deletion: it needs a fresh argument
for vacuity of quantified formulas (or a new interpretation that avoids
that interface). Atomic equality and reverse membership do not need
to be reproved. No such replacement argument was obtained here, so no
head deletion is asserted.

## Relevance of ConciseIPRA

The pinned README gives the native scalar core with terms x,0,S,I;
formula constructors equality,Q,D; and progress restricted to literal
equations. It formalizes equivalence with intuitionistic primitive
recursive arithmetic. It does not furnish a PA-equiconsistent calculus.
Its measurements are Python checker tokens, AST nodes, normalized bytes,
and gzip bytes, which do not imply a two-symbol machine-state bound.

Useful design lessons include deriving full equality transport from a
restricted primitive rule, letting syntax determine certificate fields,
and unifying operations whose separate formulation obscures shared
computation. The PA196 equality-vacuity reduction already follows a
related principle: only the interfaces actually needed by the
interpretation are retained. Replacing the enumerated theory by iPRA
would change the target unless an additional PA-consistency equivalence
were proved. No such replacement is made in this audit.
