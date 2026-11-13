# Uniform Church arithmetic: a finite-model obstruction

This note examines a specific candidate simplification, not every use of
combinators. It does **not** claim a new presentation of iPRA, a checker-size
improvement, or a new theorem of the literature. It uses the standard
normalization and set-model soundness theorems for the simply typed lambda
calculus; the arithmetic model and interpretation obstruction are proved here.

## Candidate being tested

Let the pure simply typed lambda calculus have one ground type `o`, arrow
types, application, and abstraction, with no constants. Put

`N = (o -> o) -> o -> o`,

and let `bar(n) = lambda f x. f^n(x)` be the Church numeral. For every closed
lambda term `M : N -> ... -> N -> N`, with `k` argument occurrences, introduce
a numerical function symbol `F_M` of arity `k`. The numerical signature is
allowed to contain **all** such symbols, so the obstruction is not caused by
choosing too few combinators.

Give this numerical theory intuitionistic first-order logic with actual
equality, all equations justified by beta-eta conversion after expanding the
function symbols, the usual Church zero and successor, the axioms

* `forall x. S(x) != 0`;
* `forall x. (x = 0 or exists y. x = S(y))`;

and induction for **every** first-order formula, including formulas with
parameters. Call this theory C. In particular, C contains any weaker proposal
with quantifier-free induction and the same beta-defined arithmetic symbols.

## Theorem 1: C has a three-element model

Interpret the ground type as the two-element set X = {0,1}, arrow types as
the full sets of functions, and lambda terms by their usual set denotation.
There are four maps X -> X: the identity, the transposition, and the two
constant maps. Consequently the denotation of a Church numeral depends
exactly on whether its exponent is

1. zero;
2. positive and odd;
3. positive and even.

These classes are distinct. Identity versus a positive power is distinguished
using a constant map and an initial point different from its value. The two
positive classes are distinguished using the transposition.

A map is displayed as `(f(0),f(1))`:

| f | f^0 | f^1 | f^2 | f^3 |
|---|-----|-----|-----|-----|
| (0,0) | (0,1) | (0,0) | (0,0) | (0,0) |
| (0,1) | (0,1) | (0,1) | (0,1) | (0,1) |
| (1,0) | (0,1) | (1,0) | (0,1) | (1,0) |
| (1,1) | (0,1) | (1,1) | (1,1) | (1,1) |

Let the numerical domain D be these three denotations, represented by the
numerals 0, 1, 2. Every symbol F_M restricts to an operation on D. Indeed,
substituting Church numerals for its arguments gives a closed lambda term of
type N; its beta-normal, eta-long form is `lambda f x. f^n(x)` for some n.
The assertion follows directly from the shape of a normal term of ground
type in the context `f:o->o, x:o`. If two numeral representatives have the
same denotation, applying the set denotation of M gives equal results, so
the restriction is independent of representatives.

All beta-eta equations hold because set denotation is sound for beta-eta
conversion. Equality in D is literal equality of denotations. The successor
table is

| a | S(a) |
|---|------|
| 0 | 1 |
| 1 | 2 |
| 2 | 1 |

No successor is zero, and every nonzero element has a predecessor, so both
displayed axioms hold. Finally, every element of D lies in the finite orbit
of zero. If any subset P of D contains zero and is closed under S, it contains
1 and then 2, hence all of D. Every formula, for each assignment of its
parameters, denotes such a subset. Therefore **full formula induction**
holds. A one-world Kripke model is enough, so this also verifies the
intuitionistic first-order version.

Here are all the subsets that the induction argument covers:

| P | 0 in P | S-closed | P = D |
|---|--------|----------|-------|
| empty | no | yes | no |
| {0} | yes | no | no |
| {1} | no | no | no |
| {2} | no | no | no |
| {0,1} | yes | no | no |
| {0,2} | yes | no | no |
| {1,2} | no | yes | no |
| {0,1,2} | yes | yes | yes |

Nevertheless S is not injective: S(0)=S(2)=1 but 0 != 2.

## Corollary: no finite-dimensional interpretation of iPRA in C

An interpretation with a fixed finite tuple domain inside a finite model has
a finite interpreted domain. Taking a definable subdomain, adding parameters,
using finitely many sorts, or quotienting by a definable equivalence relation
does not change this fact. Every model of iPRA has an injective successor with
zero outside its image, and hence is infinite. Thus C cannot interpret iPRA
by any such interpretation, in particular cannot be bi-interpretable with it.

This is stronger than the observation that predecessor is missing as a term:
adding numerical induction, even full induction, does not repair the uniform
Church-number arithmetic. It does not rule out a different numeral encoding,
polymorphism, an additional recursor, a non-pure arithmetic constant, an
untyped calculus, or an interpretation whose domain lies in a newly added
infinite syntax sort. Those are different candidates and their added
mechanisms must be counted.

## Theorem 2: no predecessor at any fixed simple Church type

Let tau be any simple type over o and put
`N_tau = (tau -> tau) -> tau -> tau`. There is no closed pure simply typed
lambda term `P : N_tau -> N_tau` such that, for every natural n,

`P bar(n) =_{beta eta} bar(max(n-1,0))`.

Proof. In the full set model with o={0,1}, the denotation of tau is a finite
set of some size q >= 2. Let L=lcm(1,...,q). For every endomap f of this set,

`f^(q-1) = f^(q-1+L)`.

Every orbit enters its cycle after at most q-1 steps, and each cycle length
divides L. Thus the Church numerals q-1 and q-1+L have equal denotations.
Their proposed predecessors q-2 and q-2+L do not: on a q-element chain use
`f(i)=min(i+1,q-1)` and initial point 0. The two iterates give q-2 and q-1.
A lambda term denotes a function, which sends equal arguments to equal
values. Contradiction.

The canonicity claim used in Theorem 1 is specifically for the ground-base
Church type N. Theorem 2 does not assert that every closed inhabitant of
N_tau is a Church numeral for arbitrary tau; its proof only compares the
denotations of the actual Church numerals.

At the base type q=2 this is the tiny argument `bar(1)=bar(3)` while
`bar(0)!=bar(2)` in the finite model.

## What the attached check establishes

`verify_church_obstruction.py` exhaustively enumerates the four ground maps,
checks the three numeral denotations, checks the successor table and every
one of the eight subsets for induction, and checks the generalized power
identity and separating chain for q=2,...,5. This is finite evidence for the
displayed model and examples. The universally quantified statements about
all lambda terms and all finite q are proved above, not by that finite check.

## Literature context

The familiar stronger characterization of same-type numerical functions by
extended polynomials is due to Helmut Schwichtenberg, “Definierbare Funktionen
im Lambda-Kalkul mit Typen,” Archiv fur mathematische Logik und
Grundlagenforschung 17, 113-114 (1976), DOI 10.1007/BF02276799.
Author's institutional repository:
https://epub.ub.uni-muenchen.de/4273/.
The theorem is also explicitly recalled as Theorem 1 in William Blum and
C.-H. Luke Ong, “The Safe Lambda Calculus” (TLCA 2007),
https://www.cs.ox.ac.uk/files/156/safelambda-tlca2007.pdf.
The finite-model proof above does not require that characterization.
