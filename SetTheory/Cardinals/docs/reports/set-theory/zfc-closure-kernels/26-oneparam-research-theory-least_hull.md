# Least positive hulls without increasing the parameter budget

Research contribution, 16 October 2026. This note is an ordinary first-order
mathematical argument. It does not claim a proof-assistant certificate, a new
Turing machine, or a state bound. It builds on the explicitly parameter-counted
EPSC2 bootstrap in ProveIt's batch 150, source 21, while addressing a different
issue: removing an existential hull witness from later defining formulas.

## 1. Language and theory

Use classical equality-free first-order logic over a nonempty domain, with one
binary predicate `in` and genuine falsity. Let

    E(x)       := forall z not(z in x),
    Sub(y,b)   := forall z(z in y -> z in b),
    Trans(b)   := forall u forall v((u in v and v in b) -> u in b).

For a fixed formula R(x,y;p), or a fixed finite tuple of at most k ordinary
parameters p, write

    SB_R       := forall x exists b forall y(R(x,y;p) -> Sub(y,b)),
    Cl_R(c)    := forall x forall y(
                    ((E(x) or x in c) and R(x,y;p)) -> y in c),
    Supp_R(c)  := forall y(y in c -> exists x R(x,y;p)).

EPSC_k contains the universal closures of

    SB_R -> exists c(Cl_R(c) and Supp_R(c))

for matrices with at most k ordinary parameter slots. Input x and output y
are additional free variables. Arbitrary internal quantifiers and arbitrary
negations in R are allowed. All inserted binders are fresh. We take k >= 1.
The fixed empty-input predicate E is not another parameter.

The source-21 theorem establishes the ordinary ZFC-level equiconsistency of
EPSC_2 with ZFC. It does not establish the same claim for EPSC_1. The results
below preserve this distinction.

## 2. Two one-parameter bootstrap resources

We spell out the resources used, so that no unrestricted Separation or
unnoticed additional parameter is imported.

### 2.1 Exact formation of a globally subset-bounded class

**Lemma 1.** Suppose theta(y;p) has at most k ordinary parameters and

    exists b forall y(theta(y;p) -> Sub(y,b)).

Then EPSC_k proves the existence of a whose members are exactly the theta
objects.

**Proof.** First the false-matrix EPSC instance gives an empty object e: its
support clause says that it has no members. Its boundedness premise follows
from nonemptiness of the domain. Apply EPSC to the constant matrix
R(x,y;p) := theta(y;p). The assumed global bound supplies its local bound at
every x. The empty input e activates all theta outputs, while global support
gives the reverse implication. The existential bound is used only in proving
the premise; it is not a parameter of the matrix. ∎

### 2.2 A transitive container of an arbitrary object

**Lemma 2.** EPSC_1 proves

    forall a exists v(a in v and Trans(v)).

In particular, for every a there is a bound v such that every member of a is
a subset of v.

**Proof.** Define incoming and full profile equivalence by

    D(s,t) := forall z(z in s iff z in t),
    O(s,t) := D(s,t) and forall z(s in z iff t in z).

Pure logic makes O an equivalence relation and a congruence in both membership
coordinates. The exact-class lemma applied to O(y,t), with bound t, supplies
an O-singleton of t. Put

    SingO(s,t) := forall z(z in s iff O(z,t)),
    W(x,y) := SingO(x,y)
              or (not exists t SingO(x,t) and Sub(y,x)).

W is locally subset-bounded. If x is an O-singleton of some t, every possible
output is O-equivalent to t and hence a subset of t. Otherwise x bounds all
its outputs. For the given object a use the one-parameter matrix

    G_a(x,y) := (E(x) and Sub(y,a))
                or (not E(x) and W(x,y)).

Its branches are disjoint, so a local subset bound exists without combining
two bounds. An empty input emits a itself, and hence a belongs to its EPSC
hull v. To prove transitivity, take x in v and y in x. The input x is nonempty.
If x is an O-singleton, W(x,y) holds directly. Otherwise choose an O-singleton
s of y. Outgoing O-congruence implies s is a subset of x, so W(x,s), while
W(s,y) follows from its defining singleton property. The intermediate s is
nonempty. Both edges therefore remain enabled in G_a. Closure puts y in v.
Finally, y in a implies y in v, and transitivity gives Sub(y,v). ∎

This is the one-slot transitive-container bootstrap of source 21, reproduced
here to make the later parameter ledger explicit. No Pairing, Union,
Extensionality, Foundation or choice has been used.

## 3. A definable least pre-fixpoint

Fix R(x,y;p) and assume SB_R. Define the formula

    mu_R(y;p) := forall c(Cl_R(c) -> y in c).

The quantification ranges over raw objects in the first-order structure.
It does not range over all external subclasses. Nevertheless, because a
globally subset-bounded exact class can be formed, this intersection is
represented by a raw object.

**Theorem 3 (parameter-preserving least hull).** EPSC_k, for k >= 1, proves
that there is an object m with

    forall y(y in m iff mu_R(y;p)).

Every such m has all of the following properties:

1. Cl_R(m).
2. Supp_R(m).
3. For every raw object c, Cl_R(c) implies Sub(m,c).
4. Any two such m have the same incoming membership profile.

The defining formula mu_R has exactly the ordinary parameters of R.

**Proof.** EPSC gives one supported closed object c0. Lemma 2 gives a bound
v such that y in c0 implies Sub(y,v). If mu_R(y;p), then y belongs to c0,
because Cl_R(c0). Thus mu_R is globally subset-bounded by v. Lemma 1 forms
its exact extension m; neither c0 nor v occurs in the defining matrix.

For closure, suppose R(x,y;p) and either E(x) or x in m. Let c be any raw
closed object. In the recurrent case x in m implies x in c by the definition
of mu_R. In the empty-input case x is initially enabled in every closed c.
Thus y in c in either case. Since c was arbitrary, mu_R(y;p), hence y in m.

Minimality follows directly from the defining universal quantifier. In
particular m is a subset of c0, so its members inherit global support from
c0. Exact extensions of the same formula have the same incoming profile.
No uniqueness by actual equality is asserted. ∎

The key point is to quantify over **all closed objects**, not merely the
supported ones. Consequently minimality covers arbitrary represented
pre-fixpoints without constructing an intersection with a newly named c.
The choice of c0 is only a local existence witness in the boundedness proof.

## 4. Active support and an equivalent fixed-point schema

Define, still with only p as ordinary parameters,

    nu_R(y;p) := exists x(
                    (E(x) or mu_R(x;p)) and R(x,y;p)).

**Theorem 4 (exact active-support fixed point).** Under SB_R,

    forall y(mu_R(y;p) iff nu_R(y;p)).

**Proof.** The closure just proved gives nu_R(y;p) -> mu_R(y;p). Therefore
nu_R has the same global subset bound used for mu_R, and Lemma 1 supplies
an exact extension n using p alone. If R(x,y;p) and either E(x) or x in n,
then in the recurrent case nu_R(x;p) implies mu_R(x;p). Thus nu_R(y;p),
and y in n. Hence Cl_R(n). Minimality of m gives mu_R(y;p) -> y in n,
which is exactly the opposite implication. ∎

Thus the least represented positive hull contains precisely outputs of an
empty input or an input already in that hull. It need not contain the empty
inputs themselves. Minimality excludes a disconnected recurrent component
whenever some represented pre-fixpoint omits that component. It does not
identify this internal hull with the union of externally finite paths in an
arbitrary or nonstandard EPSC model: not every external subset need have a
representing object.

**Corollary 5 (equivalent schema).** For every k >= 1, EPSC_k is deductively
equivalent to the schema XFP_k consisting of

    SB_R -> exists c forall y(
       y in c iff exists x((E(x) or x in c) and R(x,y;p))).

Theorem 4 gives EPSC_k -> XFP_k. Conversely a displayed fixed point is
closed and has global support, so every XFP instance directly implies the
corresponding EPSC instance. This direction uses no bootstrap assumptions.
In particular, the established EPSC_2 consistency calibration transfers to
XFP_2. No EPSC_1/ZFC equiconsistency follows from this corollary.

This alternative has two written matrix occurrences if iff is counted as a
primitive: one in SB_R and one in the fixed-point body. Expanding iff in an
implication/falsity basis duplicates its right side, restoring three matrix
occurrences. A complete logical engine and literal compilation are needed to
decide whether the alternative has any actual state advantage.

**A limitation of changing the axiom.** Replacing EPSC merely by existence of
a least represented pre-fixpoint is not equivalent. In the one-object structure
with a in a, there are no empty objects. Both possible binary relations are
locally subset-bounded, and a is a least represented pre-fixpoint. The
false-matrix EPSC instance fails because its support would require an empty
object. The active-support fixed-point corollary avoids this issue: its false
matrix itself forces an empty object.

## 5. Definable induction and witness-free cuts

**Theorem 6 (induction with the same parameters).** Let I(y;p) use only the
ordinary parameters already allowed in the instance. Suppose

    forall x forall y((E(x) and R(x,y;p)) -> I(y;p)),
    forall x forall y((I(x;p) and R(x,y;p)) -> I(y;p)).

Then mu_R(y;p) implies I(y;p).

**Proof.** The class mu_R(y;p) and I(y;p) is globally subset-bounded and uses
only p, so it has an exact extension d. Its members are closed under the
transition R by the second premise, and the first premise handles initial
empty inputs; closure of mu_R supplies membership in mu_R in both cases.
Thus Cl_R(d), and minimality gives m subset d. ∎

For example the invariant may be the fixed hereditary-saturation predicate
H used by the existing interpretation. It may not silently contain a new
arbitrary parameter q when only one slot is available.

More generally, any formula referring to membership in the canonical hull m
can replace `z in m` by `mu_R(z;p)`. This removes the existential witness m
from the ordinary-parameter list, while retaining just R's parameters.
Only incoming-profile uses of m are eliminated this way. An occurrence
`m in z` in a raw nonextensional formula is not determined by mu_R and cannot
be replaced without a further invariance argument.

**Monotonicity.** If R(x,y;p) implies S(x,y;q), both relations are locally
subset-bounded, and their canonical hulls exist, then m_R is a subset of m_S.
Indeed m_S is already an R-pre-fixpoint. This proof may use the separate R
and S instances even when p and q together exceed one matrix's slot budget;
it does not construct a new schema matrix containing both tuples.

## 6. Parameter ledger and the still-open one-slot problem

| Resource | Matrix's ordinary parameters |
|---|---|
| Empty object | none |
| Full-profile singleton of t | t |
| Transitive container of a | a |
| Exact extension of mu_R | R's existing p only |
| Exact extension of nu_R | R's existing p only |
| Same-parameter invariant cut | p only |
| Chosen preliminary hull and transitive bound | none added to the matrices |

For EPSC_1 the remaining obstacle in source 21 is obtaining pure Pairing or
another tuple representation for two arbitrary hereditary objects. Two
arbitrary objects need not be definable from the same one parameter; the
least-hull construction does not supply a tuple code for them. In particular,
it does not justify regarding an externally definable-closure hull as an
elementary submodel. Establishing a directed hereditary core with internal
coding is a separate promising problem.

For machine design, mu_R is a calibration device. It does not need to be
computed on tape. XFP_2 is a concrete equiconsistent alternate theory wrapper
for a future full-cost comparison. The remaining cost is the complete logic,
matrix handling, proof enumeration and binary compiler, not the existence
proof of the canonical hull.

## 7. Finite semantic verification

`least_hull_check.py` independently checks all directed graphs and all seed
sets with up to three vertices. It compares:

* the intersection of all pre-fixpoints;
* the intersection of all globally supported pre-fixpoints;
* positive reachability from the seed set;
* the active-support fixed-point equation;
* all inductive invariants and monotonicity after adding each possible edge.

These are exhaustive finite tests in the full powerset semantics, where
every vertex subset is available as a candidate pre-fixpoint. They are not
a model search for EPSC, a formal proof of first-order definability, or a
refutation-compiler certificate. The note's proofs establish representable
minimality and the active fixed-point equation in arbitrary EPSC models,
with explicit parameter accounting. The comparison with external finite
reachability belongs only to the graph test's full powerset semantics.

## Sources

The current ProveIt pin used here is
`6ec2e80dbbe45a99b7812fb5757977307959a51e`.

1. ProveIt, `21-two-notes-two_parameter_proof.md`, batch 150 source 21:
   https://github.com/VladimirReshetnikov/ProveIt/blob/6ec2e80dbbe45a99b7812fb5757977307959a51e/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/21-two-notes-two_parameter_proof.md
2. ProveIt, `raw_psc.md`, current interpretation scope:
   https://github.com/VladimirReshetnikov/ProveIt/blob/6ec2e80dbbe45a99b7812fb5757977307959a51e/Computability/BusyBeaver/Research/ZFC/raw_psc.md
3. ProveIt, `subset_only.md`, extensional PSC calibration:
   https://github.com/VladimirReshetnikov/ProveIt/blob/6ec2e80dbbe45a99b7812fb5757977307959a51e/Computability/BusyBeaver/Research/ZFC/subset_only.md
4. Ralf Schindler and Philipp Schlicht, *ZFC without parameters (A note on a
   question of Kai Wehmeier)*, author-hosted note. Their parameter packing
   explicitly uses Pairing; the note attributes the earlier result to Azriel
   Levy's 1974 paper. This is relevant to why tuple packing is not free here:
   https://www.math.uni-bonn.de/people/schlicht/ZFC_without_parameters.pdf

