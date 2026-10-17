# Equality-free EPSC with two fixed parameter slots

Research note, 16 October 2026. This is an ordinary mathematical proof, not
a proof-assistant certificate or a Turing-machine simulation theorem.

## Result

Let EPSC2 use classical equality-free first-order logic over a nonempty
domain, with one binary relation symbol `in` and genuine logical falsity.
Its only nonlogical axioms are instances of the EPSC wrapper below, with
matrices whose free variables belong to **x,y,p,q**. The displayed p,q
are always universally quantified; either or both may be unused. Matrices
may have arbitrary bound variables, arbitrary quantifier complexity and
arbitrary negations. This is not the two-variable fragment of first-order
logic, and not a finite axiomatization.

Write E(x) := forall z not(z in x), and Sub(y,b) := forall z(z in y -> z in b).
For a matrix r(x,y;p,q), the axiom is

    forall p forall q (
      [forall x exists b forall y (r(x,y;p,q) -> Sub(y,b))]
      -> exists c (
        [forall x forall y (((E(x) or x in c) and r(x,y;p,q)) -> y in c)]
        and [forall y (y in c -> exists x r(x,y;p,q))])).

All wrapper binders are fresh for the matrix and all substitutions avoid
capture. There is no seed parameter, equality, Extensionality, profile
congruence, irreflexivity or empty-set constant.

**Theorem.** There is a fixed first-order interpretation of extensional,
arbitrarily parameterized subset PSC in EPSC2. Consequently

    ZFC proves Con(EPSC2) iff Con(ZFC).

The theorem restricts the number of free parameter slots in the theory
generator. It does not assert that unrestricted raw EPSC and EPSC2 have
the same raw-language theorems. The argument must first pass to the
hereditarily saturated interpretation before packing parameters.

## Provenance and scope

The EPSC empty-seed reduction itself is inherited from the incoming
`zfc_empty_seed_research.zip`, added by ProveIt commit
af518abcf8ca2a7c1b795c07973885041aee0d25. Its unrestricted EPSC/PSC
deductive-equivalence argument is sound on independent reading.

The hereditary-saturation interpretation is inherited from batch 144
source 08. The current source acknowledges its ordinary mathematical
proof; commit 45a1b47c4d742b74def38121388509985a907d25 certifies specified
semantic saturation lemmas, not the complete first-order interpretation.
The new observation in this note is the **fixed two-parameter resource
ledger and tuple reduction** for EPSC. No general priority claim is made.
Packing finitely many set parameters into one is a standard technique;
Schindler and Schlicht's primary note explicitly discusses it. The part
requiring proof here is that this particular very weak-looking raw
closure schema can bootstrap the necessary pure Pairing with two slots,
and that no hidden third parameter enters the root/filter construction.

## 1. Exact classes and a bootstrap with at most two parameters

Throughout this section only the parameter slots listed below are used.
Bounds established in a premise do not become free parameters of the
matrix unless they actually occur in that matrix.

### Empty object and exact constant classes

The false-matrix instance gives an empty output object by support,
whether or not empty inputs previously existed. If theta(y;parameters)
has a global subset bound and has at most two parameters, apply EPSC2 to
the constant matrix r(x,y):=theta(y). Any empty input activates every
theta-output; support proves the converse. Thus its extension is exact.

### Full-profile singletons and transitive containers

Put

    D(x,y) := forall z(z in x iff z in y),
    O(x,y) := D(x,y) and forall z(x in z iff y in z).

Pure logic proves O is an equivalence relation and a congruence in both
membership arguments. The one-parameter constant predicate O(y,t) is
subset-bounded by t, so its exact extension exists. Write

    SingO(s,t) := forall z(z in s iff O(z,t)),
    W(x,y) := SingO(x,y)
              or (not exists t SingO(x,t) and Sub(y,x)).

W has no ordinary parameters and is locally subset-bounded. If x is an
O-singleton, any witness t bounds every output; otherwise x bounds them.
Every membership edge y in x is either a W-edge x->y, or two W-edges
x->s->y through an O-singleton s of y. In the second case outgoing
O-congruence, not D-congruence, proves s is a subset of x.

For a given a use the one-parameter matrix

    G_a(x,y) := (E(x) and Sub(y,a)) or (not E(x) and W(x,y)).

The branches are disjoint, so a local bound exists without Union or
Pairing. Empty inputs emit every subset of a, including a. If y in x,
then x is nonempty; any intermediary O-singleton s is also nonempty.
Consequently the one- or two-edge decoder path stays enabled. Its hull
is transitive and contains a, hence also covers all members of a.

### Separation needed here, and Union

For any theta(y;p,q) already globally subset-bounded, exact extension is
available directly. To separate a predicate psi(y;p) from a raw object a,
use the constant matrix `y in a and psi(y;p)`, with parameters a,p.
A transitive container of a bounds its outputs. More generally the exact
cost is the free parameters of the displayed combined predicate, not an
unlimited Separation axiom.

In particular the fixed purity cut `y in v and H(y)` uses only v.
The raw Union predicate `exists t(t in a and y in t)` uses only a and is
bounded by a transitive container of a. This gives exact raw unions.

### Binary common subset bounds

For any a,b we can find u with a subset u and b subset u, with a
two-parameter proof. If a is empty, the exact power object of b contains
a and b. If a is nonempty, apply EPSC2 to

    J_ab(x,y) := (E(x) and Sub(y,a)) or (not E(x) and Sub(y,b)).

An initial empty input emits a, and the now active nonempty a emits b.
In either case some raw object P contains a and b. An exact raw union of
P is the required common subset bound. This combines two bounds at a
time and asserts no family-choice principle.

## 2. The hereditary domain and pure Pairing

Define the fixed formulas

    S(a) := forall u forall v(D(u,v) -> (u in a -> v in a)),
    H(a) := S(a) and exists T(
      Trans(T) and Sub(a,T) and forall u(u in T -> S(u))).

All inherited semantic lemmas apply using only the resources just listed.
H is nonempty, D-invariant, and hereditary. Given S(a) and all members of
a in H, choose a raw transitive cover V and make the fixed cut
U={u in V:H(u)}. U is transitive by heredity and witnesses H(a).
This uses one parameter V; it does not require unrestricted Separation.

The exact saturation of A is the class

    Sat_A(y) := exists x(x in A and D(x,y)).

Its outputs are subsets of any raw union of A. It uses one parameter A.
Saturation preserves membership in H by D-invariance, so the purity-cut
lemma makes the saturation of an H-only extension itself an H-object.

For H(u),H(v), take a common raw subset bound b of u,v. The predicate

    D(y,u) or D(y,v)

is subset-bounded by b and has exactly two parameters. Its exact
extension P exists. It is S by D-transitivity and all its members are H
by D-invariance. The purity-cut lemma gives H(P). In the H/D quotient P
is precisely the unordered pair {u,v}.

Membership on H respects D in both coordinates, and Extensionality holds
because every raw member of an H-object is again H. This gives ordinary
Pairing and Extensionality in the interpretation. Empty objects are H,
so an interpreted empty object is also available. No full PSC transfer
or Replacement has been used to obtain these coding resources.

## 3. Packing an arbitrary finite tuple of pure parameters

Within H/D, form ordinary Kuratowski ordered pairs and finite nested
ordered tuples using the Pairing just proved. For each fixed k, there is
a fixed formula Tuple_k(t,z1,...,zk) such that:

1. Every k-tuple of H-objects has an H-code t.
2. If Tuple_k(t,z1,...,zk) and Tuple_k(t,z1',...,zk') hold in H/D, then
   D(zi,zi') for every i.

These assertions use only finitely many Pairing instances for each k.
Here is a fully explicit choice. In the interpreted equality-bearing
language put

    Pair(a,b,w) := forall z(z in w iff (z=a or z=b)),
    OP(a,b,t) := exists s exists u(
      Pair(a,a,s) and Pair(a,b,u) and Pair(s,u,t)),
    Tuple_0(t) := forall z not(z in t),
    Tuple_(k+1)(t,z1,...,z_(k+1)) := exists s(
      Tuple_k(s,z2,...,z_(k+1)) and OP(z1,s,t)).

Translate every formula to H/D by the same syntactic interpretation.
The recursion is in the metatheory and expands to one finite first-order
formula for each k. Each OP existence proof requires three pure-pair
instances. There is no need to form the set of all finite tuples or to
prove an internal recursion theorem before interpreting full PSC.

For completeness, Kuratowski injectivity uses no Foundation. If
t={{a},{a,b}}, the objects belonging to every member of t are precisely
the objects equal to a: a belongs to both members, and membership in
the singleton {a} gives the converse. Hence equality of two OP codes
implies equality of their first coordinates. The members of members of
t are precisely a and b, so equality of codes also gives
{a,b}={a,b'} after the first coordinate is identified. If b differs
from a, membership of b in the latter pair gives b=b'; if b=a, the
right-hand pair is a singleton and gives b'=a. Thus second coordinates
agree too. These arguments are formulas about memberships; no actual
Intersection or Union set construction is needed. In H/D, the same
proof proves coordinate uniqueness up to D. Induction on the fixed k
now proves the stated uniqueness of every tuple coordinate.

Let r(x,y;z1,...,zk) be any equality-bearing matrix, and r^H its usual
translation: equality becomes D; membership is unchanged; quantifiers
are restricted to H. Translate Tuple_k in the same way. Define

    rhat(x,y;t) := exists z1...exists zk(
      H(z1) and ... and H(zk)
      and Tuple_k^H(t,z1,...,zk) and r^H(x,y;z1,...,zk)).

The sole ordinary parameter is t. For a chosen tuple code t of given
pure parameters p1,...,pk, tuple uniqueness and formula invariance give

    rhat(x,y;t) iff r^H(x,y;p1,...,pk)

for pure x,y. Invariance is available for every translated formula by
structural induction. Packing raw arbitrary matrices directly would not
be justified, because D is not a raw membership congruence.

## 4. Recovering the full interpreted PSC axiom with exactly two slots

Assume the interpreted local-bound premise for r at a chosen pure
parameter tuple, and choose its pure code t. Put

    R(x,y;t) := H(x) and H(y) and rhat(x,y;t).

This raw relation is locally subset-bounded: at non-H x it has no
outputs, and at H x the interpreted bound is a raw subset bound because
all raw members of H-objects are H.

Fix the pure seed a required by the target subset-PSC instance. Use

    Q(x,y;t,a) := R(x,y;t) or (E(x) and Sub(y,a)).

This has exactly the two allowed parameters t,a. For a fixed x, combine
its R-bound with a using the binary-bound lemma. That gives a local
Q-bound. EPSC2 yields a hull C0. Empty inputs emit every subset of a,
and C0 is recurrently closed under R.

Form the exact support cut

    y in C1 iff y in C0 and exists x R(x,y;t).

Its constant matrix has exactly the two parameters C0,t. A transitive
container of C0 bounds it. Notice that a does NOT occur in this cut.
If x subset a and R(x,y;t), then x belongs to C0, hence y belongs to C0
and the edge supplies its support witness. If x belongs to C1, it also
belongs to C0, so the same argument proves closure at recurrent inputs.
Thus C1 is a raw subset-PSC hull for R with the intended seed a and
unrestricted support. Its members are all H because R guards its output.

Finally saturate C1 under D. The result C is H by the purity-cut lemma.
Initial closure, recurrent closure and global support transfer exactly
as in the inherited saturation proof. Recurrent closure uses a D-copy
x0 in C1 of x in C and input invariance; support uses a D-copy y0 in C1
of y in C and output invariance. The tuple-code equivalence identifies
this with the desired translated matrix r^H.

Every source PSC instance, with any finite number of source parameters,
has therefore been derived inside H/D using only EPSC2 matrices.

## 5. Parameter ledger

| Required resource | Free ordinary matrix parameters | Maximum |
|---|---|---:|
| Empty object | none | 0 |
| Full-profile singleton of t | t | 1 |
| Transitive container G_a | a | 1 |
| Exact raw Union of A | A | 1 |
| Binary bound J_ab | a,b | 2 |
| Fixed purity cut | V | 1 |
| Incoming-profile saturation | A | 1 |
| Pure pair | u,v | 2 |
| Arbitrary target matrix after tuple packing | t | 1 |
| Root graft Q | t,a | 2 |
| Support cut | C0,t | 2 |

Bound witnesses used only in proofs of subset-boundedness are existential
local witnesses, not additional matrix parameters. Bound variables inside
D,O,H,Tuple_k or r may always be freshly renamed; they are unrestricted.

## 6. Internal ZFC calibration and implementation consequence

By the established extensional PSC/ZF0 comparison, the interpretation
gives a model of ZF without Foundation and Choice from any set-coded
EPSC2 model. ZFC proves the ordinary completeness theorem for these
recursive theories and the satisfaction lemma for this fixed first-order
interpretation. Internally well-founded sets, then the constructible
universe inside that interpretation, provide the usual ZF0-to-ZFC
consistency bridge. No externally well-founded model and no truth
predicate for the ambient universe are needed.

Conversely every EPSC2 instance is an EPSC instance and hence a ZFC
theorem. The construction by unique exact fibers and countable closure
proves this uniformly. Therefore both consistency implications are
formalizable in ZFC.

A search checker may now recognize a fixed wrapper with exactly two
universal parameter slots. It does not need to implement tuples,
hereditary saturation or the interpretation at runtime; those occur in
the calibration proof and in possible certificates, not the generator.
This can simplify the parameter-closure interface, but the changed
generator still needs soundness, refutation completeness, fair search,
compiler simulation and blank-tape initialization. No state saving is
proved by this theorem. Nor is a one-parameter version proved here.

## Primary sources and exact repository pins

* EPSC arrival: https://github.com/VladimirReshetnikov/ProveIt/commit/af518abcf8ca2a7c1b795c07973885041aee0d25
  (`docs/incoming/zfc_empty_seed_research.zip`, sections/fixed_empty_kernel.tex).
* Current accepted saturation/calibration scope:
  https://github.com/VladimirReshetnikov/ProveIt/blob/af518abcf8ca2a7c1b795c07973885041aee0d25/Computability/BusyBeaver/Research/ZFC/raw_psc.md
* Checked semantic saturation lemmas:
  https://github.com/VladimirReshetnikov/ProveIt/blob/af518abcf8ca2a7c1b795c07973885041aee0d25/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/PSCSaturation.lean
* Source 08 audit and proof provenance:
  https://github.com/VladimirReshetnikov/ProveIt/blob/af518abcf8ca2a7c1b795c07973885041aee0d25/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-144-source-08.md
* Extensional PSC/ZF0 comparison:
  https://github.com/VladimirReshetnikov/ProveIt/blob/af518abcf8ca2a7c1b795c07973885041aee0d25/Computability/BusyBeaver/Research/ZFC/subset_only.md
* Ralf Schindler and Philipp Schlicht, *ZFC without parameters (A note on
  a question of Kai Wehmeier)*, primary author-hosted note. It attributes
  the older general parameter-elimination result to Azriel Levy (1974).
  https://www.math.uni-bonn.de/people/schlicht/ZFC_without_parameters.pdf
* Zuhair Al-Johar, *ZF*-Extensionality interprets full ZF*, arXiv:2010.01938,
  especially the coextensional saturation and restricted-membership
  interpretation, attributed there to Marcel Crabbé's method.
  https://arxiv.org/html/2010.01938v1


