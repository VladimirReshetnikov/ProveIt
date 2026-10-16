# Equality-free PSC without congruence: the monochromatic decoder proof

Research note, 16 October 2026. This is the final alternative proof,
reconciled with late batch 144 source 08. That source already proves the
accepted equality-free PSC-only consistency calibration. This note supplies
an incoming-profile/nonempty-monochromatic bootstrap and directly derives
the interpreted ZF axioms; it adopts source 08's purity cut with credit.
Neither the consistency theorem nor hereditary saturation is claimed as
new. See `purity_cut_update.md` for the exact late-source provenance.
No Lean or literal-machine correctness theorem is asserted.

## Theorem and exact source theory

Use classical first-order logic without equality, one binary relation
written `in`, and a nonempty domain. Define

    Sub(x,b) := forall z (z in x -> z in b).

The sole nonlogical axiom schema is, for every equality-free formula
`rho(x,y;parameters)` with arbitrary finite parameters:

    [forall x exists b forall y (rho(x,y) -> Sub(y,b))]
      -> forall a exists C [
           forall x y (((Sub(x,a) or x in C) and rho(x,y)) -> y in C)
           and forall y (y in C -> exists x rho(x,y)) ].

All auxiliary bound variables are fresh. Call this theory `T_PSC`.
There is no Extensionality, equality, congruence, irreflexivity, or other
fixed nonlogical sentence. This is one infinite schema, not a finite
axiomatization.

**Theorem.** `T_PSC` interprets ZF without Foundation and Choice, with
full Separation and functional Replacement. Conversely ZFC proves every
instance of `T_PSC`. With the standard well-founded/constructible
interpretation, ZFC proves `Con(T_PSC) <-> Con(ZFC)`.

The interpretation is fixed and first order. A proof-code translator,
formal verification, and its connection to a literal machine remain
distinct engineering/proof obligations.

## 1. Exact classes, profile fragments, and saturated pairs

Define

    D(x,y) := forall z (z in x <-> z in y).

Pure logic makes D an equivalence relation and a congruence for the
**second** membership argument. No congruence in the first argument is
assumed or used without a separate saturation hypothesis.

**Exact-class lemma.** If `theta(y)` is subset-bounded by one object b,
an exact extension E exists:

    forall y (y in E <-> theta(y)).

Apply PSC to the constant relation `rho(x,y):=theta(y)`. At any seed a,
the initial input a is active because Sub(a,a). Closure includes every
theta-object; support excludes all others. The ambient first-order
domain is nonempty, so a seed can be chosen.

This gives:

* an empty object, by taking theta false;
* a raw power object for a, by taking theta(y):=Sub(y,a), with bound a;
* the saturated singleton `[a]={y:D(y,a)}`, with bound a;
* for arbitrary x,a, the **profile fragment**

      F(x,a) = {z : z in x and D(z,a)},

  with bound a. This fragment requires no Separation axiom: every
  member z is D-related to a and therefore is a subset of a. If a is
  a member of x, the fragment is nonempty, since it contains a.

For arbitrary a,b, PSC also gives the **saturated pair**

    P(a,b) = {z : D(z,a) or D(z,b)}.

Use the relation

    rho(x,y) := (D(x,a) and D(y,b)) or (D(x,b) and D(y,a)).

If D(a,b), both nonempty branches have the same output profile; otherwise
the input profiles are disjoint. Thus each nonempty fiber is one D-class
and is subset-bounded by its endpoint. At seed a, all D-copies of b enter
the hull; b itself is now a member, so closure adds all D-copies of a.
Support excludes other profiles. The displayed exact profile follows.
This is not a claim that a literal pair containing only the two raw
objects a,b has been constructed.

## 2. The nonempty monochromatic decoder

Put

    Mono(x,y) := (exists z z in x)
                  and forall z (z in x -> D(z,y)),

    Delta(x,y) := Mono(x,y)
      or ((not exists t Mono(x,t)) and Sub(y,x)).

**Local boundedness.** If Mono(x,t), choose one raw member u of x.
For any output endpoint y satisfying Mono(x,y), D(u,t) and D(u,y)
imply D(y,t), hence Sub(y,t). The second branch is gated off. Therefore
t bounds the whole fiber. If there is no monochromatic endpoint, the
outputs are exactly the subsets of x, bounded by x.

The nonempty clause is essential: without it an empty input would be
monochromatic at every y, producing an unbounded universal fiber.

**Descent lemma.** For any active input x, every raw member y of x enters
the PSC hull for Delta.

Proof. If Mono(x,t) holds, y in x gives D(y,t). Every member z of x is
D-related to t and hence to y. Thus Mono(x,y), and the first branch
puts y in the hull.

Otherwise take the profile fragment s=F(x,y) from Section 1. It is a
subset of x, nonempty because y in s, and every member of s is D-related
to y. Thus the second branch at x first puts s in the hull; the first
branch at s then puts y in the hull.

This proof works for **every raw object**, including nonsaturated ones.
It uses neither actual singleton sets nor Extensionality nor profile
congruence.

**Transitive-cover theorem.** For every A there exists a transitive C
with Sub(A,C).

Apply PSC to Delta at seed A. A is an allowed initial input, so descent
puts all members of A in C. Every member x of C is an active input, so
descent gives Sub(x,C); hence C is transitive. No claim that A belongs
to C is needed, and no support condition is needed for this theorem.

## 3. Raw Separation, Union, and exact local images

With a transitive cover C of A, every member y of A is a member of C
and hence is a subset of C. The exact-class lemma therefore gives

    {y : y in A and psi(y)}

for every equality-free formula psi with parameters. This is unrestricted
raw Separation for the source language.

Similarly, if y in x in A, then x in C, y in C, and y is a subset of C.
The exact-class lemma gives the exact raw union of A. Pairing the profiles
of arbitrary B,U and taking a raw Union gives the literal binary union
profile `{z:z in B or z in U}`. No actual-equality pair is required.

**Exact local-image theorem.** For every equality-free rho and A,

    [forall x in A exists b forall y (rho(x,y) -> Sub(y,b))]
      -> exists B forall y [y in B <-> exists x in A rho(x,y)].

Proof. Raw Separation produces the Russell root

    r={t in A : not(t in t)},

and Russell's argument gives `not(r in A)`. Let U be the raw union of A.
Use the auxiliary relation

    R(x,y) := (D(x,r) and not(x in A) and y in A)
                or (x in A and rho(x,y)).

The explicit `not(x in A)` gate is indispensable for arbitrary raw A:
a D-copy of r could belong to A even though r does not. With the gate,
the root branch and source branch are disjoint at every raw input.

At a root input, all outputs are members of A and hence subsets of U.
At an input in A, only the source branch can hold, and the assumed local
bound applies. Every other fiber is empty. Thus R is locally
subset-bounded.

Apply PSC at r. Since D(r,r) and r is not a member of A, its initial
fiber puts every member of A in the hull C. Closure at those members
adds every intended rho-output. Support says that every member of C
is either in A or in the intended image. Hence C has exactly the raw
profile `A union image(rho|A)`. Raw Separation in C gives the exact image.

No global family of bounds is chosen. In particular, the theorem applies
whenever every nonempty fiber is unique modulo D: any one output
subset-bounds all coextensional outputs. It applies to the relation

    rho(x,t) := forall z (z in t <-> phi(x,z)),

whose outputs are exact extensions of a definable class. There need not
be an output at every input.

**Optional further consequence.** The theory proves the equality-free
power-bounding transitive-container sentence CP from the repository.
Combine Delta with the relation giving all exact power objects at x.
The two local subset bounds can now be combined by binary union. A PSC
hull is Delta-closed and hence transitive; it contains a power object p
of its seed a, and a in p forces a into the hull. Every hull member
likewise has a power object in the hull. This does not by itself derive
the separate full GIC schema.

## 4. Saturated hereditary domain

Define

    S(x) := forall u v (D(u,v) -> (u in x <-> v in x)),

    H(x) := S(x) and exists T [Sub(x,T) and Trans(T)
                              and forall z in T S(z)].

These are fixed equality-free formulas. Both are D-invariant. H is
hereditary under raw membership: if H(x) and y in x, an S-only transitive
cover for x contains y, so S(y) holds, and transitivity puts every member
of y in the same cover. Every empty object is H.

**Closure lemma (source 08 purity cut).** If S(B) and every member of B
is H, then H(B).

Choose a raw transitive cover V of B, already proved to exist. Raw
Separation forms W={u in V:H(u)}. Every member of B lies in W. If x in W
and y in x, transitivity of V gives y in V and heredity of H gives H(y),
so y in W. Thus W is transitive. Every member of W is H and hence S.
Together with S(B), this W witnesses H(B).

No family of witnesses, canonical least cover, or Replacement is needed.
Neither V nor W is required to be saturated. This is not circular:
heredity follows directly from the definition of H before the closure
lemma. The exact-local-image theorem remains useful for Replacement.

The exact-image theorem also forms the saturation of every raw object A:

    Sat(A)={y:exists x in A D(y,x)}.

This observation is useful for implementations, although the Infinity
argument below avoids a final saturation operation.

## 5. Interpreted ZF axioms

Interpret equality by D, preserve raw membership, and restrict every
quantifier to H. On H assignments, membership is congruent under D in
both arguments: S of the target supplies the first-argument law and
D supplies the second. Formula induction gives invariance for every
translated formula. It does not give invariance for arbitrary raw
formulas.

**Extensionality.** All raw members of H objects belong to H. Thus
agreement on the interpreted members is agreement on the full raw
profile, precisely D.

**Empty Set and Pairing.** A raw empty object is H. The saturated pair
P(a,b) of H objects is S and has only H members, so the closure lemma
puts it in H. Its members are exactly the D-classes of a and b.

**Union.** The raw union U of H(a) is saturated, because every member
of a is saturated. Every member of U is H by heredity. The closure
lemma gives H(U); raw Union is exactly the interpreted Union statement.

**Power Set.** The exact-class lemma applied to

    theta(y):=Sub(y,a) and H(y)

with bound a produces a saturated object with H members, so the closure
lemma puts it in H. For an H object y, inclusion restricted to H is
ordinary raw inclusion, since all its raw members are H. This proves
the full interpreted Power Set axiom.

**Separation.** Raw Separation gives `{y in a:phi*(y)}` for a translated
matrix. Formula invariance and S(a) make the result saturated; all its
members are H. Apply the closure lemma.

**Replacement.** Under interpreted functionality, the outputs of
`H(y) and phi*(x,y)` are unique modulo D. At each input, an output if
present subset-bounds every other output. The exact-image theorem
collects all intended H outputs on a. Formula invariance makes this
image saturated; the closure lemma puts it in H. This is full
Replacement for arbitrary translated matrices with parameters.

**Infinity.** Pairing and Union already give, for each H object x, a
successor y with exact profile

    SuccD(x,y) := forall z (z in y <-> (z in x or D(z,x))).

It is saturated and has only H members, hence H(y). Use PSC on

    R(x,y) := H(x) and (D(x,y) or SuccD(x,y)).

If H(x), choose any successor s. For a self-profile output y, Sub(y,x)
and Sub(x,s), so Sub(y,s). Every successor output is D-related to s
and hence a subset of s. Thus s bounds the whole fiber. If H(x) fails,
the fiber is empty.

Apply PSC at an empty e, which is H. Initial self-profile closure puts
e in C. Support shows every member of C is H, even if its supporting
input was not active. At an active member x of C, the self-profile
branch puts every D-copy of x in C, so C is saturated. The successor
branch puts successors inside C. Therefore the closure lemma gives
H(C), and C is an interpreted ordinary inductive set.

This completes the equality-free interpretation of every ZF axiom except
Foundation and Choice. It uses no weak-Infinity bridge and no assumed
raw congruence.

## 6. Reverse construction and calibration scope

In ZFC every locally subset-bounded fiber has an exact set extension,
formed by Separation in a local power bound. Extensionality makes the
fiber independent of the chosen bound, so Replacement collects exact
fibers without Choice. Start with the seed set P(a), repeatedly take
the union of all fibers over the current stage, and take the union of
all positive finite stages. This gives both closure and support. Thus
ZFC proves each T_PSC axiom.

The standard well-founded core and constructible-universe interpretation
of ZFC in ZF without Foundation or Choice supplies the remaining
consistency bridge. Alternatively, state the entire calibration in ZFC
using completeness and the definable set-model interpretation H/D.
The source model need not be externally well-founded, and no choice of
quotient representatives is required to define the quotient set.

All predicates and inserted matrices above are first order. The proof
uses fixed finite schema patterns and parameter-preserving formula
translation. Turning those patterns into a proved proof-code translator,
then linking a refutation search and compiler to a fixed binary
transition table, remains necessary before a smaller-machine theorem
can be claimed. In particular this theorem does not certify the distinct
equality-free CP/GIC theory emitted by the current 252-state experiment.
