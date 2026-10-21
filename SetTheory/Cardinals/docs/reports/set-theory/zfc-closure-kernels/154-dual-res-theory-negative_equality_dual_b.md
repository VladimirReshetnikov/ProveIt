# A calibrated dual-B variant with negative equality

## Exact scope

Keep the original numerical constructors

```
I(a,b)=4P(a,b), R(a,b)=4P(a,b)+1,
Q(a,b)=4P(a,b)+2, J(a,b)=4P(a,b)+3,
F=R(0,0)=1, N A=I(A,F), Ex_a A=N Q_a N A.
```

Interpret primitive `J` as disequality, and use `E'(a,b)=N J(a,b)`
at every equality occurrence in rho1, rho3, rho5, and G. Replace rho6 by

```
B(a,A): A -> Q_a Ex_a A.
```

For this theorem **rho1 is the full translated row**
`Ex_a E'(a,b)=N Q_a N N J(a,b)`. All other rows, the private-code-gated
bundle, MP, and GEN remain unchanged. In particular, the proof does not
currently cover replacing rho1 by `N Q_a J(a,b)` or swapping the two odd
tags so that F becomes a disequality atom.

The following is a proof inside the native Hilbert calculus. Every use of
classical implication is licensed by the unchanged Lukasiewicz rho8; we
do not assume that F is a bottom for arbitrary numerical formulas.

## Pure implication preliminaries

The rho8 basis supplies the K, S, and Peirce schemes and the ordinary
implicational deduction theorem. Contraposition relative to any formula
F does not require explosion: from `A -> B` one derives
`N B -> N A` by composing the implications to F. Double negation
introduction `A -> N N A` is also purely implicational.

Call a formula A **F-closed** if the calculus proves `F -> A`. If A is
F-closed, then `N N A -> A` follows without any additional assumption.
Indeed, under `N N A` and `A -> F`, obtain F and then A; discharge the
second assumption and apply Peirce `((A -> F) -> A) -> A`. Thus double
negation is an equivalence for F-closed formulas, even though it need not
be one for raw J atoms.

GEN and rho2 give monotonicity of Q: every theorem `A -> B` gives the
theorem `Q_a A -> Q_a B`.

## The key new bootstrap: F is quantifier-stable

The formula `N F=(F -> F)` is a theorem, hence so is `Q_a N F`.
Consequently

```
Ex_a F = (Q_a N F -> F)  <->  F
```

is a theorem in both directions. The direction from F is K; the reverse
direction uses the already established theorem `Q_a N F` and MP under a
single hypothesis.

Instantiate dual B with F:

```
F -> Q_a Ex_a F.
```

Quantifier monotonicity applied to `Ex_a F -> F`, followed by composition,
now gives the previously missing stability theorem

```
F -> Q_a F                                      (all a).
```

This deduction does not use rho1, equality, membership, K, T, or any form
of explosion. It is valid for an arbitrary chosen formula F.

## Negative equality makes every named atom F-closed

K gives `F -> E'(u,v)` for every u,v because E' is an implication to F.
Since F is literally R(0,0), the changed rho5 gives

```
F -> R(a,0),
```

by using `E'(0,a)` in `E'(0,a) -> (R(0,0) -> R(a,0))`.
The changed rho3 then gives

```
F -> R(a,b),
```

by using `E'(0,b)` in `E'(0,b) -> (R(a,0) -> R(a,b))`.
Thus both named atomic forms, membership and defined equality, are
F-closed.

F-closed formulas are closed under implication when its consequent is
F-closed. They are closed under relative negation, whose consequent is
F. They are closed under Q: compose `F -> Q_a F` with the quantified
version of `F -> A`. Truth code zero is F-closed, since `0=I(0,0)` is a
theorem of the implicational calculus.

By structural induction, **every named formula translated using R,
E', I, N, and Q is F-closed**. This includes every intermediate formula
needed by the named logical calibration, and every equality-eliminated
matrix used by Complete222.

## Recovering the original rho6 on this fragment

Let A be F-closed. Both directions of `N N A <-> A` have been proved.
Apply dual B to `N A`:

```
N A -> Q_a Ex_a (N A)
    =  Q_a N Q_a N N A.
```

Two applications of Q-monotonicity, with contraposition between them,
replace `N N A` by A and give

```
N A -> Q_a N Q_a A.
```

Contraposition relative to F gives

```
N Q_a N Q_a A -> N N A.
```

Its antecedent is literally `Ex_a Q_a A`; compose with the F-closed
double-negation elimination to conclude

```
Ex_a Q_a A -> A.
```

This is the old rho6, for every formula in the complete named-language
translation. No inference used double-negation elimination on raw J.

## Recovering the calibration

For every translated named formula A, the preceding argument supplies
the exact original rho6 instance and the explosion implication `F -> A`.
The full translated rho1 is present as an axiom. Therefore the algebraic
proofs of G222 (reflexivity, helper, Euclidean equality) and the induction
of Interp222 can be replayed on these translated formulas. Their
propositional intermediate formulas stay in the F-closed fragment.

The membership-vacuity formula V is F-closed: its consequent is a
quantified membership atom. The seed formula is F-closed because its
outermost operation is N. Thus the ordinary relative-conjunction
projection of the native bundle is available for both components using
only F-closed double-negation elimination. This supplies every gated V
and every seed instance needed by the unchanged completeness proof.

As in the unchanged-rho6 disequality codec, the interpretation `th` in
L224E replaces all equalities by membership indiscernibility. Therefore
its translated output contains only the original R/I/N/Q constructors:

```
tau'(th(A)) = tau(th(A)).
```

The Complete222 matrix codes, private-label freshness arguments, and
K0-to-ZFC consistency interpretation remain literally unchanged.
An inconsistent ZFC consequently yields a finite proof of F in the new
calculus.

Conversely, in a ZFC model let J denote actual disequality. F is false,
E' is equality, and dual B is valid for ordinary variable quantification.
All retained logical and seed axioms are valid. Every numerical formula,
including raw J, has its ordinary recursive interpretation. No odd
formula is globally valid: membership and disequality each fail under
an assignment identifying their two endpoints. This proves the desired
consistency equivalence and licenses the four-leaf parity halt test.

The proof is elementary and can be formalized in ZFC. It is currently a
mathematical calibration, not a completed Rocq replay or a certified TM
table. It is intentionally weaker than an assertion that the new
calculus and the old one have the same theorems on all natural codes.

## Why compact rho1 is not covered

The old-rho6 proof simplifying rho1 used `N N J -> J`. Raw J need not be
F-closed, and dual B does not imply this statement. To see the exact
obstacle, take a reflexive two-world frame 0->1 with no return edge, and
set F false at 0 and true at 1. Relative Ex at world 0 ignores the
F-true world 1; at world 1 it is always true. This frame validates dual B
for every A. Set J true at 0 and false at 1. At world 0,
`N Q J` is true whereas `N Q N N J` is false. Thus the proposed row
equivalence cannot be borrowed from the unchanged-rho6 proof. This is a
countermodel to the local logical implication, not a claim that the
entire compact-rho1 native set theory is inconsistent or too weak.

## Why swapping the odd tags is not covered

If F is J(0,0), F still implies every defined equality, but it no longer
supplies the membership atom R(0,0). The derivation transporting F to
every membership atom therefore stops. A separate calibration would be
needed before combining dual B with that codec.
