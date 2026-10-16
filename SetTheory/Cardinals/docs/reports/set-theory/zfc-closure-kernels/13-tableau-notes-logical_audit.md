# Two obstructions in the equality-free 252-state logical kernel

## Scope

These results concern the logical fragment emitted by the repository's
`theory_backend_experiment.py` at ProveIt commit
`17d0f2eaa650901cda59764dfcc4661c199e49c8`.
They do not assert a model of the complete C/G bundle theory, nor do they
prove that the 252-state machine halts or does not halt. They show that two
specific hoped-for logical bridges are false as stated.

Write `F = Rel(0,0)`, `not A = (A -> F)`, and
`exists_i A = not(forall_i not A)`. The retained logical calculus has truth
code 0, modus ponens, generalization, the Lukasiewicz implicational schema

    ((C -> U) -> A) -> ((A -> C) -> (B -> C)),

quantifier distribution `forall_i(B -> C) -> (forall_i B -> forall_i C)`,
commutation `forall_i forall_j C -> forall_j forall_i C`,
the dual row `B -> forall_i exists_i B`, and atomic vacuity
`Rel(i,j) -> forall_k Rel(i,j)` when its side conditions hold.
Giving vacuity with no side conditions only strengthens the negative result.

## Theorem 1: the retained logical fragment is not complete for ordinary
equality-free first-order logic

Let the Boolean algebra be `{false,true}`. Interpret every `forall_i` as
the identity operation. Assign `Rel(0,1)` the value true and every other
`Rel(i,j)` the value false. Interpret implication classically and code 0
as true. In particular `F` is false.

Every instance of the retained schemas has value true. The Lukasiewicz
schema is a classical implicational tautology. Distribution and commutation
reduce to implications from a Boolean value to itself. Atomic vacuity
reduces to `p -> p`. Since F is false and each quantifier is identity,
`exists_i p` has value p, so the dual row is `p -> p`. The old row
`exists_i forall_i p -> p` is also true in this model. Modus ponens and
generalization preserve truth, so induction on derivations shows that every
theorem of either logical fragment has value true.

However the formula

    (forall_0 Rel(0,1)) -> Rel(2,1)

has value false. It is valid in ordinary first-order logic: instantiate the
antecedent's quantified variable with the assignment to variable 2. The
closed formula

    (forall_0 forall_1 Rel(0,1)) ->
    (forall_2 forall_1 Rel(2,1))

is also false in the Boolean interpretation, although its antecedent and
consequent are merely different bound-variable presentations of the same
ordinary first-order sentence. Thus even closed alpha-conversion is not
provided by the retained rows.

The base-3 numerical codes of these two witnesses are respectively
`25221` and `2306316221757`.

The interpretation is deliberately not an ordinary model of a single
membership relation. Atomic propositions indexed by different variable
pairs are independent. The absence of a rule tying these atomic occurrences
together is exactly what the countermodel detects. Restoring the old
quantifier row alone does not repair this failure.

### Consequence for the research candidate

An equality-free *theory* equiconsistency proof in ordinary first-order
logic cannot be connected to the candidate simply by deleting equality
axioms from the original completeness proof. One must either:

1. derive the missing substitution/alpha-conversion principles using the
   complete nonlogical bundle theory and prove that stronger bridge;
2. add a complete equality-free proof system, for example explicit
   capture-avoiding universal-instantiation and binder-renaming operations;
3. retain a validated logical equality subsystem while minimizing the
   nonlogical theory.

No Boolean model of the complete C/G theory is supplied here. Consequently
this theorem does not prove that C/G cannot repair the defect. It does prove
that the proposed purely logical completeness argument is unavailable.

## Theorem 2: the old and dual rows are not interderivable in the relative-F
logical calculus

Again interpret each quantifier as the identity Boolean operation, but now
assign F the value true and assign some other atom p the value false.
For every Boolean value b,

    exists_i b = ((b -> F) -> F) = F or b.

Thus every dual row is `b -> (F or b)`, a tautology. Every other retained
logical schema and every inference rule still preserves true. The old row,
however, becomes `(F or b) -> b`, equivalently `F -> b`; at b=p it is false.
It follows by induction on derivations that the old row is not derivable
from the new logical fragment. The same countermodel shows that the full
ex-falso scheme `F -> A` is not derivable there.

This does not rule out preservation of *target-F refutability*. Such a result
would be a weaker theorem than equality of the theorem sets. A suitable
Friedman-style or continuation-style translation may eliminate uses of
ex-falso from proofs whose final conclusion is F. It would have to be
defined and proved for this precise binder syntax. Here F is the literal
atom `Rel(0,0)`, so quantifier 0 can capture it; pretending F is a fresh
nullary constant without an explicit normalization bridge is insufficient.

The repository's finite Boolean test with F fixed false correctly checks
that special semantic case. It does not imply interderivability of the
relative-F schemas. The four-row truth table in `calculus_audit.json`
exhibits exactly the omitted case `F=true, p=false`.

## A positive result: a total base-3 decoder including the truth alias

Let `P(a,b) = (a+b)(a+b+1)/2+b`, and define

    Imp(a,b)=3P(a,b), Rel(i,j)=3P(i,j)+1, All(i,A)=3P(i,A)+2.

Add a metatheoretic syntax constructor Top and define `D(0)=Top`.
For positive n, write `n=3P(a,b)+t` and decode according to t. Both a and b
are strictly below n. Indeed `P(a,b)>=a,b`; if P is positive then
`3P>max(a,b)`, while P=0 implies a=b=0 and positivity of n supplies t>0.
This gives a total well-founded decoder by strong recursion on n.

Define the encoder E by `E(Top)=0` and the displayed constructors. Strong
induction gives `E(D(n))=n` for every natural n. Every variable label in D(n),
including binder labels, is strictly below n; the n=0 case is vacuous. The
inductive step uses the component bound just proved. Consequently the code
n is fresh as a variable label for its own decoded formula, including n=0.

The decoder is not a strict homomorphism at the single case
`Imp(0,0)=0`: `D(Imp(0,0))=Top`, whereas `D(0)->D(0)=Top->Top`.
The two formulas are classically equivalent. All other constructor
equations are literal. Equivalently, let N recursively replace
`Imp(Top,Top)` by Top, after normalizing the children. Structural induction
gives `D(E(A))=N(A)`, and N preserves semantics in every ordinary relational
structure and assignment. On finite formulas with no Top constructor,
all codes are positive, N is the identity, and E is injective.

This is a direct way to remove the cyclic-looking zero-code obstacle.
It has no machine cost, since Top is only a metatheoretic decoder convention.
It does not fix the missing logical rules identified above.

## Executable evidence

Run `python audit_calculus.py --output calculus_audit.json`.
The script checks all 16 Boolean assignments of the Lukasiewicz schema,
all four F/p assignments for the old/dual comparison, 5,824 numeric
schema/constructor examples in each of the two witness algebras, and
10,000 natural-number decoder/freshness/round-trip cases. These tests
reproduce exact witness values; the universal claims are justified by the
proofs above rather than by extrapolation from the finite cases.
