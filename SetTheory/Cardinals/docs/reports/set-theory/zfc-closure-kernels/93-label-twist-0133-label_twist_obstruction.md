# A label-twist obstruction to deleting either membership-congruence row

Research note, 18 October 2026. This note concerns the exact original
numerical calculus used by the 254-, 246-, and routed 245-state machines.
It proves a relative non-derivability result for two plausible row deletions.
It does not assert a new machine state bound, a consistency-strength
separation for either reduced calculus, or a proof-assistant formalization.

## 1. Precise result

Write C for the code-level calculus with truth code 0, modus ponens,
generalization, the original eight logical rows, and the original gated
CP/GIC/vacuity bundle. Its constructors are

    Imp(x,y) = 4 P(x,y),    Rel(i,j) = 4 P(i,j)+1,
    All(i,x) = 4 P(i,x)+2, Eq(i,j)  = 4 P(i,j)+3,
    P(x,y) = (x+y)(x+y+1)/2+y.

The two membership-congruence rows are

    rho3(a,b,c): Eq(a,b) -> (Rel(c,a) -> Rel(c,b)),
    rho5(a,b,c): Eq(c,a) -> (Rel(c,b) -> Rel(a,b)).

Let C-minus3 omit every rho3 instance, and let C-minus5 omit every rho5
instance. Every other rule and the entire literal nonlogical bundle remains.

**Theorem.** Assuming Con(ZFC):

1. C-minus3 does not derive rho3(0,1,2).
2. C-minus5 does not derive rho5(1,2,0).

The parameter ordering in the second assertion is the source ordering
rho5(a,b,c), so this is "Eq(0,1) -> (Rel(0,2) -> Rel(1,2))".
Thus neither missing axiom family is recoverable from all other original
axiom families, including CP, GIC, and both atomic-vacuity clauses.

The result is stronger than a pure-logic independence countermodel because
the literal set-theory bundle is also validated. It is weaker than a
consistency-strength separation: a different interpretation could still
calibrate a reduced calculus with ZFC. In particular, this theorem does not
prove that deleting a row necessarily loses equiconsistency.

## 2. A tempting argument, and its exact limitation

In ordinary first-order logic, let Q be a reflexive binary relation and let
M satisfy left congruence

    Q(x,y) and M(x,A) implies M(y,A).

Suppose there is a nonempty M-set and the full GIC schema, with Q allowed
in matrices. Then every formula psi is monotone along Q. Indeed, apply GIC
over a nonempty domain to the constant-in-input matrix

    phi(u,v) := Q(v,a) and psi(v).

If psi(a), reflexivity gives a possible output. GIC supplies an output v
in its collecting set C, with Q(v,a). Left congruence first gives M(a,C),
and Q(a,b) then gives M(b,C). GIC support at b gives psi(b). Taking
psi(v) := M(c,v) proves right congruence.

This is a correct ordinary first-order argument. It cannot be transplanted
without proof into the current reduced Tarski calculus: the quantifier
instantiations used by that argument are themselves derived using the
congruence rows. The interpretations below establish that this obstruction
is real, rather than merely a missing lemma in one proof development.

## 3. The interpretation

Work in ZFC. For each variable label i, choose two definable bijections
g_i and f_i of the universe onto itself, preserving rank exactly:

    rank(g_i(x)) = rank(x) = rank(f_i(x)).

Only a finite transposition will be needed, so no global-choice principle
or nondefinable class function is involved. Interpret a formula under a
valuation s by

    Rel(i,j)[s] iff g_i(s(i)) in f_j(s(j)),
    Eq(i,j)[s]  iff s(i)=s(j).

Implication has its usual Boolean meaning, and All_i varies the i-th
coordinate over all sets. The interpretation depends on the *names* of
variables as well as their values. It is consequently a general semantic
interpretation of the Hilbert calculus, not a usual one-relation
first-order structure. This distinction is deliberate.

Rank preservation gives, for every i and x,

    not(g_i(x) in f_i(x)).

Therefore every diagonal membership atom is false, including the actual
falsity alias Rel(0,0), code 1. Code 0 is interpreted as truth. The unique
collision "Imp(0,0)=0" respects truth values, and all constructor laws
remain valid. The usual negation, conjunction, and existential macros
therefore retain their intended semantic meanings.

The exact all-code freshness property survives: a positive decoded code c
only mentions labels below c, apart from the harmless closed truth/falsity
aliases. Its truth value is independent of changing coordinate c. Fixed
functions f_i,g_i associated with labels do not change when a coordinate
value changes.

## 4. Logical rows and rules

The Lukasiewicz axiom, quantified implication, quantifier commutation,
and Exists_i All_i A -> A hold for ordinary coordinate quantifiers and
Boolean connectives. Equality is literal equality of coordinate values,
so the equality-existence and Euclidean-equality rows hold as well.
Both atomic-vacuity clauses hold under exactly the original guard
c != a,b, since neither displayed atom depends on coordinate c.
Modus ponens and generalization preserve validity.

If all g_i are the identity, rho5 holds: its two membership atoms have
the same second label b and equality identifies their first values.
There is no corresponding reason for rho3 to hold when f_a differs from
f_b. Dually, if all f_i are the identity, rho3 holds and rho5 can fail.

## 5. The literal CP component remains valid

First take pairwise distinct a,b,c, as in the ordinary CP reading of the
named bundle, and let p=s(c). Choose a limit ordinal alpha above rank(p).
Set

    B = inverse(f_b)(V_alpha).

Then "Rel(c,b)" holds because g_c(p) belongs to V_alpha. If the universally
bound value X at a satisfies Rel(a,b), rank(X)<alpha.
The transitivity arm is true because

    f_a(X) is a subset of V_alpha.

For the power-container arm define the actual set

    K_X = {g_b(Y) : f_b(Y) is a subset of f_a(X)},
    W_X = inverse(f_c)(K_X).

This is a set: it is the image of the actual powerset of f_a(X) under
g_b composed with inverse(f_b). Rank preservation gives

    rank(K_X) <= rank(X)+1 < alpha,
    rank(W_X) = rank(K_X).

Consequently g_c(W_X) belongs to V_alpha, which is the required
"Rel(c,b)" after c has been rebound to W_X.

In the nested subset test, universal quantification over coordinate c
tests

    forall Z, g_c(Z) in f_b(Y) implies g_c(Z) in f_a(X).

Surjectivity of g_c makes this exactly "f_b(Y) subset f_a(X)". Its
conclusion "Rel(b,c)" is "g_b(Y) in f_c(W_X)=K_X", which holds by
definition. This accounts for the source formula's shadowed b and c
binders; it does not silently replace them with conventional membership.

When a=b, the universal closure premise becomes
"g_a(X) in f_a(X)" and is false by rank preservation. Only the seed
membership remains, supplied by the same choice of B. The original gate
still excludes c=a and c=b. Thus all allowed CP cases hold.

## 6. The literal GIC component remains valid

Assume a!=b. After fixing the other coordinates, let R(x,y) be the
interpreted matrix with a assigned x and b assigned y. The collection
binder c is semantically fresh, by the exact numerical freshness fact.
If B is the original value at the free domain label b, the actual input
set is

    A = inverse(g_a)[f_b(B)].

Ordinary ZFC Collection and Separation provide a set Y of witnesses such
that every nonempty R-fiber over A meets Y, and every member of Y is an
R-output. One may enforce the stronger support condition that its source
belongs to A; the literal bundle only asks for global support.

Choose

    C = inverse(f_c)(g_b[Y]).

Since g_b is injective,

    Rel(b,c) under b:=y,c:=C
      iff g_b(y) in f_c(C)
      iff g_b(y) in g_b[Y]
      iff y in Y.

Both coverage and support in the literal GIC tree now follow. When a=b,
the input premise is a diagonal membership and is false. Choose
C=inverse(f_c)(empty); its output-membership predicate is empty, so
support is also vacuous. This covers every gate-allowed collision.

The CP and GIC arguments use no inference from the omitted rho3 or rho5
inside the numerical calculus. They are explicit validations of the
transformed finite formulas in ordinary ZFC.

## 7. Explicit failures

Put

    e = empty, u = {e}, A = {u}, B = {e,u}.

A and B are distinct sets of rank 2. Let pi interchange A,B and fix all
other sets. It is a definable rank-preserving involution.

### Delete rho3

Take every g_i to be the identity, f_1=pi, and f_i=id otherwise. Set

    s(0)=s(1)=B, s(2)=e.

Then Eq(0,1) and Rel(2,0) are true, but Rel(2,1) is false, since
e belongs to B and not to A=pi(B). This refutes rho3(0,1,2).

### Delete rho5

Take every f_i to be the identity, g_1=pi, and g_i=id otherwise. Set

    s(0)=s(1)=B, s(2)={B}.

Then Eq(0,1) and Rel(0,2) are true, but Rel(1,2) is false, since
B belongs to {B} and A does not. This refutes rho5(1,2,0), in the
original parameter order.

## 8. Effective scope and the absence of a truth-predicate assumption

For each *finite* numerical derivation, recursively translate its decoded
formulas by replacing membership atoms with the displayed definable
twisted predicates. The constructor aliases are handled by their explicit
truth-value identities. Each translated logical axiom has a finite ZFC
proof, and Sections 5-6 provide uniform finite proof templates for each
translated CP/GIC instance. GIC uses the Separation/Replacement instances
for the one translated finite matrix, never a truth predicate for the
whole universe. MP and GEN translate directly.

Thus a reduced-calculus derivation of either displayed target would yield
a finite ZFC proof of the corresponding universally valid twisted target.
The fixed hereditarily finite valuation in Section 7 gives a ZFC proof of
its negation. Such a derivation would produce a ZFC contradiction. Under
Con(ZFC), it cannot exist.

This is an ordinary uniform proof-translation argument. A serialized
arithmetic translator and a Lean formalization have not been supplied.

## 9. Computational check and integration

"check_label_twist.py" verifies the numerical target codes, both explicit
countervaluations, and all instances of the retained atomic/equality/
vacuity rows on the 16-element hereditarily finite carrier V_4 with labels
0,1,2. It also tests constructor aliases and several quantified formula
families. The script explicitly does not test or claim CP/GIC on a finite
carrier; the infinite CP/GIC proof is Sections 5-6 above.

For a machine search, this rules out the inexpensive certificate strategy
"remove rho3/rho5 and derive it from the remaining outputs." A row-deletion
candidate needs a new consistency interpretation or a changed inference
engine. Retaining both rows and optimizing their emitted words preserves
the existing proof and avoids this new obstruction.

Primary source definitions:

- https://github.com/jeff87654/busy-beaver/blob/zf-254/ZF/m254/design/logic.md
- https://github.com/jeff87654/busy-beaver/blob/zf-254/ZF/m254/design/settheory.md
- https://github.com/jeff87654/busy-beaver/blob/zf-254/ZF/m254/coq/logic/Codes254.v
- https://github.com/VladimirReshetnikov/ProveIt/blob/6446ff5668307a2ac6aee1896037f0b792090389/Computability/BusyBeaver/Research/ZFC/tarski_logic_layer.md

The upstream authors' set theory, numerical calculus, and eight-row basis
retain their attribution. No historical-priority claim for the general
idea of name-dependent interpretations is made.

