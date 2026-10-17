# Raw irreflexivity need not survive the bisimulation quotient

Ordinary mathematical audit, 16 October 2026. This note completes the parked
finite target-permutation argument in
`/tmp/zfc-quotient-cpgic-route-Tsqyxe/route.md`. It is not a Lean theorem or a
new model-existence theorem. No proof-assistant build was run for this note.

**Conditional result.** From any actual first-order model of full ZF, including
Foundation but without assuming Choice, one obtains on the same domain a model
of CP, every **native-equality first-order GIC instance**, raw irreflexivity and
Extensionality. Its internally represented bisimulation quotient has a
self-membership edge. In particular, the failure already occurs in a model
with literal singletons and outgoing-profile faithfulness; duplicated objects
are not involved.

Here “any model” does not assume an externally transitive or well-founded
model. All ranks and hierarchy levels used below are internal to the given ZF
model. Equivalently, the construction is a fixed first-order interpretation:
ZF proves the translated fixed axioms and each translated GIC instance. It
does not assert inside ZF that a set-sized model of ZF exists.

## Exact target and the relevant definitions

Write `E` for raw membership, and let `Sub_E(z,x)` abbreviate
`forall u (u E z -> u E x)`. The container axiom is

```
forall a exists v,
  a E v /\
  (forall x E v, forall u E x, u E v) /\
  (forall x E v, exists p E v, forall z (Sub_E(z,x) -> z E p)).
```

For each first-order matrix `phi(x,y,parameters)`, GIC says

```
forall a exists b,
  (forall y E b, exists x, phi(x,y,parameters)) /\
  (forall x E a,
     (exists y, phi(x,y,parameters)) ->
     exists y E b, phi(x,y,parameters)).
```

The support quantifier in the first conjunct is global; our construction will
satisfy the stronger support condition with `x E a`. The schema is indexed by
actual finite formulas and their parameter assignments. It is not collection
for every external relation on the model's domain.

These are `ProfileCollection.Containers` and `CollectionInstance`
(`Lean/BusyBeaver/ZFC/ProfileCollection.lean:20–32`).
`ProfileModel.ModelsGIC` currently restricts its matrices to equality-free
`Form` (`ProfileModel.lean:26`); the construction here satisfies the stronger
schema with native equality as well. The upstream nonextensional theory uses
that full native-equality schema and the same raw IR
(`lib/jeff-busy-beaver-zfc254/ZF/m254/coq/settheory/S_def.v:1–43`).

For the repository's quotient, `Same_E(x,y)` means equality of raw member
profiles. An object `r` represents a relation by its E-members that are
Kuratowski ordered-pair codes. `Bisim_E(r)` is the forth/back condition for
all represented edges, and

```
Eqv_E(x,y) := exists r, Bisim_E(r) /\ App_E(r,x,y)
Member_E(x,y) := exists u, u E y /\ Eqv_E(x,u).
```

See `ProfilePairs.lean:20–32`, `ProfileCollection.lean:109–124` and
`ProfileComposition.lean:287`. `QuotientModel.lean:147` defines actual quotient
membership from this `Member`, after proving congruence. Quotient IR therefore
requires `forall x, not Member_E(x,x)`, which is stronger than raw IR.

## A parameter-free definable change of receiving sets

Work first in ordinary ZF. Use old membership `in`, and put

```
A = empty,       B = {A},       C = {B}.
```

These are three distinct sets, of ranks 0,1,2. In particular, C is the double
singleton of the empty set, not the ordinal 2. Let `tau` exchange A and C and
fix every other object:

```
tau(A)=C,    tau(C)=A,    tau(x)=x when x differs from A,C.
```

It is an involutive bijection. Define the new membership relation by

```
x E y  iff  x in tau(y).                                      (1)
```

This changes the receiving set, not the element on the left of membership.
All new quantifiers range over the same domain and native equality stays
literal equality.

The definition is first-order without parameters. For example, let
`Empty(a)` be the usual empty-set formula, `Sing(b,a)` the native singleton
formula, and

```
DoubleEmpty(c) := exists a b, Empty(a) /\ Sing(b,a) /\ Sing(c,b).
Tau(x,y) :=
  (Empty(x) /\ DoubleEmpty(y)) \/
  (DoubleEmpty(x) /\ Empty(y)) \/
  (not Empty(x) /\ not DoubleEmpty(x) /\ x=y).
```

ZF proves that `Tau` is the graph of the stated involution. Equation (1) is
the fixed formula `exists t (Tau(y,t) /\ x in t)`. The convenient A/B/C/tau
notation can consequently be eliminated by a definitional extension. There
is no external enumeration, satisfaction predicate or selected global choice
function in this definition.

For each finite target formula phi, define phi^tau by replacing every E atom
with (1), keeping native equality, Bottom and connectives, and recursing through
quantifiers with fresh bound variables. This is a computable, capture-avoiding
finite formula translation. Induction on phi gives its satisfaction identity
in the old and new structures for every assignment. We have not implemented
this translation or a proof-code transformer in Lean.

## Raw IR and Extensionality

The complete raw member sets of the exceptional objects are

```
E-members(A) = {B},   E-members(B) = {A},   E-members(C) = empty. (2)
```

For x other than A,C, `x E x` is old `x in x`, excluded by old Foundation.
For x=A it would say `A in C`, hence A=B, and for x=C it would say `C in A`.
Both are false. Thus raw IR holds globally, even though A and B form a
membership two-cycle.
The new structure itself fails Foundation: its E-pair of A,B is nonempty,
and each of its two members has an E-member in that same pair.

If x,y have the same E-members, old Extensionality gives tau(x)=tau(y), so
x=y. Hence the new structure is extensional and `Same_E` is literal identity.
It has literal E-pairs and E-singletons:

```
pair_E(x,y) = tau({x,y}),       singleton_E(x) = tau({x}).       (3)
```

Indeed `z E pair_E(x,y)` iff z=x or z=y. Testing outgoing profiles against
`singleton_E(x)` also proves outgoing-profile faithfulness. This example does
not exploit failure of native equality, raw profile congruence or pairing.

## CP, including all raw subsets outside the container

It is essential to distinguish two operations:

* `tau(X)` permutes the **one object** X;
* `tau``X = {tau(z): z in X}` is its pointwise image as an old set.

In particular, these operations cannot be interchanged in a power bound.

Given a, choose the old limit ordinal

```
lambda = rank(a) + omega,       v = V_lambda.
```

It is at least omega. The sets A,B,C belong to v, a belongs to v, and tau
permutes v's members. The object v itself is neither A nor C, so tau(v)=v.
Consequently `x E v` iff `x in v`.

For transitivity, suppose x E v and u E x. Then x belongs to v, tau(x) also
belongs to v, and u belongs to tau(x). Old transitivity of V_lambda gives
u in v, equivalently u E v. Also a E v.

For each x E v define the old sets and the new power witness

```
U_x = P(tau(x)),       Q_x = tau``U_x,       p_x = tau(Q_x).     (4)
```

All these sets exist in old ZF. Every pointwise image Q_x lies in
`U_x union {A,C}`. Thus

```
rank(Q_x) <= max(rank(tau(x))+1, 3) < lambda.
```

The last inequality uses that lambda is a limit at least omega, and
`tau(x) in V_lambda`. Therefore Q_x belongs to v; its object image p_x also
belongs to v, so p_x E v.

For **every object z of the whole model**, not only z in v,

```
z E p_x
  iff z in Q_x
  iff tau(z) in P(tau(x))
  iff tau(z) is an old subset of tau(x)
  iff Sub_E(z,x).                                             (5)
```

Here tau is its own inverse. This gives an exact E-power object, stronger
than CP's bound. It explicitly accounts for raw subset copies initially
outside v; none is assumed to be already in the container. In a nontransitive
or externally ill-founded old model, P and V_lambda in this argument are the
old model's own sets and (5) quantifies over its entire domain, exactly as the
first-order CP axiom requires.

## Full GIC, formula by formula, without Choice

Fix an actual finite phi(x,y,parameters) and an input object a. In old ZF put
D=tau(a), and use the translated relation phi^tau. Old Collection gives an old
set Y such that

```
y in Y -> exists x in D, phi^tau(x,y),
x in D /\ exists y phi^tau(x,y) -> exists y in Y phi^tau(x,y).
```

For completeness, this use of Collection needs no Choice. For each x in D
with an output, take the least ordinal alpha(x) that is the rank of an output;
when no output exists use a separate default. Leastness is obtained inside
a set of ordinals below the rank of any one existing witness, and is unique.
Replacement collects alpha(x)+1 for the successful inputs, together with
0 for the unsuccessful ones. Let beta be their supremum. Then Separation in
V_beta forms

```
Y = {y in V_beta : exists x in D, phi^tau(x,y)}.
```

Every successful x has a least-rank witness in V_beta. This proves both
clauses above, including the empty-domain/no-success case. Every schema use
is on a specific old first-order formula obtained from phi; arbitrary
external predicates have not been admitted as Separation or Replacement
instances.

Take the new output object b=tau(Y). Its E-members are precisely the old
members of Y. The satisfaction identity for phi then gives both new GIC
clauses, with the stronger supported-input condition x E a. This works for
native equality and arbitrary finite parameter lists as well as equality-free
matrices. There is no assumption that full GIC follows from ZF without Power,
Foundation or the rank construction used in this particular proof.

## The internally coded bisimulation and quotient self-membership

Define E-Kuratowski codes using (3):

```
K_E(x,y) = pair_E(singleton_E(x), pair_E(x,y)),
k_AB = K_E(A,B),       k_BA = K_E(B,A),
r = pair_E(k_AB,k_BA).
```

These are actual objects of the old model, built by finitely many old pairs
and applications of the definable tau. They are consequently also objects
of the new domain.

Because `Same_E` is identity, the repository's profile-singleton and
profile-pair definitions become literal E-singletons and pairs. Its
`OrderedPair` is therefore exactly the E-Kuratowski relation. Endpoint
uniqueness needs only these pair profiles and Extensionality, not Foundation:
every inner member of K_E(x,y) contains x; comparing the singleton inner member
of a second code first gives equality of the first endpoints. Equality of the
unions of the inner profiles then gives equality of the second endpoints.
This is also the general lemma already proved up to `Same` in
`ProfilePairs.orderedPair_injective` (`ProfilePairs.lean:78`).

It follows that the complete relation represented by r is exactly

```
App_E(r,x,y) iff (x=A /\ y=B) or (x=B /\ y=A).                 (6)
```

For edge(A,B), the only left member is B and the only right member is A, so
both forth and back use edge(B,A). For edge(B,A), both use edge(A,B). Equation
(6) excludes additional unverified edges. Thus r is a represented
bisimulation, and `Eqv_E(A,B)` holds with the **internal object r** as witness.
No external two-element relation is being substituted for the represented
relation quantifier.

But B E A by (2). Taking u=B in the actual definition of Member gives

```
Member_E(A,A).
```

The established quotient congruence therefore yields self-membership of the
class of A. Raw profiles of A and B are different, while their bisimulation
classes coincide; `Same` and `Eqv` must remain distinct here.

## What this settles

Given an actual model M of ZF, the construction gives an actual model N of
CP + full native-form GIC + IR + Ext whose indicated quotient fails IR. The
same N satisfies the weaker equality-free CP/GIC schema used by the present
Lean quotient. This proves the conditional obstruction even with native
singletons, profile congruence and outgoing faithfulness available. It does
not assert the existence of M inside ZF, prove a new Lean theorem, or establish
an internally coded consistency reduction.

At the ordinary schema level the fixed definable interpretation proves each
translated CP/GIC/IR/Ext axiom and the translated finite witness to
`exists x Member(x,x)` in ZF. Under the usual consistency assumption for ZF,
this also rules out deriving quotient IR from those raw axioms. The argument
is about this specific bisimulation quotient, not every possible
interpretation or a separately chosen well-founded submodel.

The raw structure itself is still irreflexive and has native equality. The
obstruction does not refute a direct raw model of the numerical bundle, the
known equiconsistency of the upstream SIR theory, the already proved quotient
ZF0 axioms, or the current CP/full-GIC quotient transfer. It only blocks
silently transferring the **IR** part along that quotient. To use that quotient
as a new irreflexive native model, one must supply a further loop-free submodel
or a different interpretation. No machine bound, compiler simulation,
nonhalting equivalence or completed Foundation/Choice proof translation is
claimed.
