# Direct calibration of the 17-clause extensional control

This is a self-contained account of the lower set-theoretic argument for
FC15 plus Extensionality. It applies both to FC16* with its class-coded
Extensionality clause and to FC17* with a separate witness function. It reuses standard EPSC/PSC
bootstrap ideas already established in ProveIt; the new contribution is their
application to the finite class-coded payload, not the individual set
constructions. It avoids invoking the longer raw hereditary interpretation.

## 1. What class coding supplies

The E-reduct is extensional and satisfies all equality-free full-parameter
EPSC instances. Under Extensionality, an equality atom u=v can be replaced by
forall z(E(z,u) iff E(z,v)), using a fresh z. Induction on formulas gives all
ordinary equality-bearing EPSC instances as well. Hence in this section we
use literal equality and write membership as in ordinary set theory.

For a relation R(x,y) with any finite tuple of parameters, write

    SB_R := forall x exists b forall y(R(x,y) -> y subset b).

EPSC says that if SB_R, there is a C closed under R from every empty input and
every input in C, with every member of C equal to some R-output. The source
theory gives no other set axioms initially.

## 2. Empty sets, exact bounded classes, singletons and powersets

Use the false relation. Its subset boundedness is immediate and the support
clause says that its hull has no members. Thus an empty set e exists. It is
unique by Extensionality.

Suppose a predicate theta(y) has a global subset bound b. Apply EPSC to the
constant-in-input relation R(x,y):=theta(y). The seed e emits every theta
object, while support excludes all other objects. Thus the exact class
{y:theta(y)} is a set. This construction uses no earlier Separation.

Taking theta(y):=y=a gives the singleton {a}, since a subset a. Taking
theta(y):=y subset a gives the full powerset of a. In particular the power
resource has been recovered before transitive closure or Union.

## 3. Transitive containers from a single empty-seeded instance

Write Sing(x,y) for forall z(z in x iff z=y), and define the gated decoder

    Dec(x,y) := Sing(x,y)
                OR (NOT exists z Sing(x,z) AND y subset x).

If x is a singleton {z}, its only decoder output is z and z itself is a
subset bound for that fiber. Otherwise all outputs are subsets of x, bounded
by x. Consequently Dec is locally subset bounded without Pairing, Union, or
any selection of a family of bounds.

For an arbitrary parameter a apply EPSC to

    R_a(x,y) := (Empty(x) AND y=a)
                OR (NOT Empty(x) AND Dec(x,y)).

The two cases are disjoint; the local bound is a in the first case and a
decoder bound in the second. Any empty input emits a, so the hull C contains
a. We claim C is transitive. Let x in C and z in x. The latter assumption
makes x nonempty. If x is a singleton, its decoder emits z directly. If it
is not, the already available singleton {z} is a subset of x, so the decoder
first emits {z} into C; this nonempty singleton then emits z. Therefore z in C.

Thus every a belongs to a transitive set C. No support argument or existing
Union has been used in this container construction. It is safe when a itself
is empty: the container still contains a, and empty objects have no members
requiring further decoding.

## 4. Separation and Union

Given a, choose transitive C with a in C. If y in a, then y in C and hence
y subset C. Thus y in a AND phi(y) is a globally subset-bounded predicate for
every formula phi. Exact bounded-class formation supplies its exact set,
which is full Separation, with unrestricted parameters.

Likewise, if y in x in a, transitivity puts x and y in C, then y subset C.
The predicate exists x(x in a AND y in x) is globally subset bounded by C.
Exact class formation gives the ordinary Union of a.

## 5. Pairing without a circular common-bound assumption

For arbitrary a,b use

    R(x,y) := (Empty(x) AND y=a)
              OR ((NOT Empty(x) OR Empty(a)) AND y=b).

If x is nonempty, its fiber is {b}, bounded by b. If x is empty and a is
nonempty, its fiber is {a}, bounded by a. If both x and a are empty, its fiber
is {a,b}; every member of a is absent, so a subset b and b bounds the fiber.
There is no appeal to a pre-existing bound combining a and b.

In an EPSC hull, the empty seed emits a. If a is nonempty, its recurrent input
emits b; if a is empty the seed already emits b. Support says every member of
the hull equals a or b. Hence the hull is the exact pair {a,b}. Binary unions
are now available using Pairing and the previously proved Union.

## 6. Recover point-seeded PSC

Suppose SB_R and fix an arbitrary point seed a. Form

    T(x,y) := R(x,y) OR (Empty(x) AND y=a).

For each input x take its R-bound b. The already available binary union a union
b bounds every T-output, so SB_T. An EPSC hull C contains a, because an empty
input emits a, and it is R-closed. Use Separation to form

    C' := {y in C : exists x R(x,y)}.

Every R-output of a is in C' since a in C. Every R-output of an input x in C'
lies in C because C is R-closed, and lies in C' by its own support. Finally
every member of C' is an R-output by definition. Thus C' is a supported
positive R-hull from point a. This proves all point-seeded PSC instances from
EPSC after the preceding noncircular bootstrap.

The support cut is necessary: C itself may contain a even if a is not an
R-output, so it need not satisfy the desired point-PSC support condition.

## 7. Functional Replacement and Infinity

For a relation phi(x,y) at most single-valued on a set A, Separation forms

    r := {t in A : t notin t}.

Russell's argument proves r notin A. Let U=Union(A) and define

    R(x,y) := (x=r AND y in A) OR (x in A AND phi(x,y)).

At input r all outputs are members of A and hence subsets of U. At an input
in A there is at most one output and the root arm is false; a nonempty fiber
is subset bounded by its unique output. Other fibers are empty. Hence SB_R.
Point-PSC at r gives a hull containing all members of A, followed by all
their phi-outputs. Separation in that hull gives the exact partial image.
This proves functional Replacement, including the usual total case.

By Pairing and Union each x has the unique successor x union {x}. The
successor relation is locally subset bounded by that successor. Point-PSC
at the empty set produces a successor-closed positive hull C containing the
successor of empty. The set I=C union {empty} contains empty and is closed
under successor. This is the ordinary Infinity axiom.

We have recovered exactly Extensionality, Empty, Pairing, Union, Power,
Infinity, full Separation and functional Replacement: ZF without Foundation
or Choice. Nothing in the argument assumes either omitted axiom.

## 8. Consistency endpoint

The preceding constructions are uniform finite proof patterns. Combining
them with FC15's syntax-directed class-code interpretation gives the lower
consistency implication from the seventeen-clause control to ZF without
Foundation/Choice. The usual effective interpretation by well-founded sets,
followed by the constructible-universe interpretation, gives Con(ZFC).
The countable-model upper construction for FC15 also supplies an extensional
E-reduct and the binary Extensionality witness. Thus ZFC proves that the
seventeen-clause control is consistent iff ZFC is consistent.

An implementation of those standard Foundation/Choice reductions is already
available as derivation-level source in the attributed upstream development:
https://github.com/jeff87654/busy-beaver/tree/main/ZF/stdzf_r3/regcon/
https://github.com/jeff87654/busy-beaver/tree/main/ZF/stdzf_r3/zfc/

No literal Turing-machine endpoint or newly serialized proof translation is
asserted here. This direct control is useful when independent review of the
raw hereditary interpretation is not the desired dependency for a compiler
experiment.
