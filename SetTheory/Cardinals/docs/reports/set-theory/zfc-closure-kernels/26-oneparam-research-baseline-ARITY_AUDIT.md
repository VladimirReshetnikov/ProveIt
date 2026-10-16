# Independent audit of the EPSC parameter-collapse theorem

**Assessment:** the theorem is sound for classical first-order logic in the
pure equality-free language with one binary relation R, assuming the EPSC
schema is exactly the closure-plus-support schema stated below. I found no
hidden Extensionality, Foundation, Choice, or standard-model assumption.
The proof can be made syntactic; a quotient-model argument is unnecessary.
The arity bound is an upper bound, not a proof that arity two is optimal.

## Definitions and the one binder convention that must be explicit

Write R(u,v) as u in v. Define:

    E(x)       := forall z, not(z in x)
    Sub(u,v)   := forall z, z in u -> z in v
    O(a,b)     := [forall z, z in a <-> z in b]
                  and [forall z, a in z <-> b in z].

All bound variables in these abbreviations must be renamed to avoid capture.
In particular, a fiber-bound variable must not also be called the free
parameter b of the pairing matrix.

For a matrix r(x,y; p-vector), let:

    SB_r := forall x exists B forall y [r(x,y;p) -> Sub(y,B)].

EPSC_r is SB_r implying the existence of C satisfying:

    forall x y [((E(x) or x in C) and r(x,y;p)) -> y in C]
    and forall y [y in C -> exists x r(x,y;p)].

All free parameters are universally closed in the axiom instance. EPSC_k
should mean at most k parameter variables, or unused dummy parameters should
be permitted. If a syntactic convention requires exact occurrence, insert
the equality-free tautology O(t,t) to pad a dummy parameter.

## Empty object and pairing from two parameters

The false matrix has SB provable in pure nonempty-domain first-order logic.
Its support conclusion produces an empty object. This uses no pre-existing
empty-set axiom.

For fixed a,b, take the two-parameter matrix:

    r(x,y;a,b) := [E(x) and O(y,a)]
                  or [(not E(x) or E(a)) and O(y,b)].

Its local bounds are valid:

- If E(a) or not E(x), choose B=b. An O(y,b) output is a subset of b. Any
  possible O(y,a) output is empty because E(a), and hence is also a subset
  of b.
- If not E(a) and E(x), choose B=a. The second disjunct is false and every
  output is O-equivalent to a.

Let e be an empty object and C the EPSC output. The closure condition at e
places every O-equivalent copy of a in C. If E(a), the same use of e places
all copies of b in C. If not E(a), a is already a member of C; closure at
x=a then places all copies of b in C. The support condition gives the reverse
inclusion. Thus:

    forall a b exists C forall y
       [y in C <-> O(y,a) or O(y,b)].

This is precisely PairO. The derivation is uniform in a,b and uses one fixed
two-parameter EPSC instance plus the false-matrix instance. No distinction
test between a and b is needed.

## Why the quotient has enough equality for coding

Pure logic proves O reflexive, symmetric, and transitive. It also proves
R-congruence in both arguments. Consequently every equality-free formula
is invariant under replacing any free variable by an O-equivalent object.
The proof is structural induction on formulas, with fresh renaming before
quantifier steps.

Both incoming and outgoing profiles are needed. Incoming profiles alone
do not give congruence in the first argument: distinct empty objects can
have different containers.

In a set-sized model the quotient by O therefore has a well-defined R and
actual pairing. It does not necessarily have Extensionality. That omission
does not prevent injective ordered-pair coding. The following direct
first-order proof makes this point completely explicit.

## Direct proof of Kuratowski endpoint uniqueness without Extensionality

Define:

    Pair(s;a,b) := forall z [z in s <-> O(z,a) or O(z,b)]
    K(t;a,b)    := exists s p [Pair(s;a,a) and Pair(p;a,b)
                              and Pair(t;s,p)].

Define the two auxiliary formulas:

    I(t,z) := forall u [u in t -> z in u]
    U(t,z) := exists u [u in t and z in u].

Using only the displayed definitions and logical O-congruence, K(t;a,b)
implies:

    I(t,z) <-> O(z,a),
    U(t,z) <-> O(z,a) or O(z,b).

For I's forward direction use the singleton witness s, which is a member
of t. For its reverse direction, every member of t is O-equivalent to s or
p, and each contains every copy of a. For U's reverse direction use p;
its forward direction splits the same two possible member classes.

If O(t,t'), then I(t,z) and I(t',z) are equivalent, as are U(t,z) and
U(t',z). Therefore:

    K(t;a,b) and K(t';a',b') and O(t,t')
       -> O(a,a') and O(b,b').

The first coordinate follows from I. After identifying a and a', U says
the two unordered pairs agree modulo O. If b is equivalent to a, the
opposite inclusion forces b' to be equivalent to a as well. If b is not
equivalent to a, the forward inclusion forces it to be equivalent to b'.
This handles the diagonal case and requires no uniqueness of the raw pair,
singleton, or ordered-pair objects. It does not assert the existence of an
intersection or union object; I and U are formulas only.

## Finite tuple coding and elimination of extra parameters

Set T_1(t;a)=O(t,a). Inductively, for k>=2, let:

    T_k(t;a1,...,ak) := exists u
       [T_(k-1)(u;a1,...,a_(k-1)) and K(t;u,ak)].

PairO gives existence of a tuple code for every finite parameter tuple.
The stronger K uniqueness statement above proves coordinate uniqueness
modulo O, including when the two outer codes are merely O-equivalent.

For an arbitrary matrix r(x,y;a1,...,ak), form the one-parameter matrix:

    r_hat(x,y;t) := exists z1 ... zk
       [T_k(t;z1,...,zk) and r(x,y;z1,...,zk)].

If T_k(t;a1,...,ak), then for all x,y:

    r_hat(x,y;t) <-> r(x,y;a1,...,ak).

The reverse implication uses the given tuple coordinates as existential
witnesses. The forward implication uses endpoint uniqueness followed by
formula invariance. Consequently SB and both EPSC conclusions transfer
between r and r_hat. Instantiate EPSC_1 at t, and eliminate the existential
tuple code using PairO. This proves the original arbitrary-parameter EPSC
instance with its parameters still arbitrary.

The result is therefore the deductive equivalence, in the same language:

    full EPSC  <->  EPSC_1 + PairO  <->  EPSC_2.

This equivalence remains valid on adjoining any common additional axioms.

## Effectivity, nonstandard models, and appropriate claim strength

The argument above supplies a direct proof transformation, not merely a
semantic equiconsistency argument. Alpha-renaming, constructing T_k and
r_hat, generating the O-invariance proof by structural recursion, and
generating the tuple-uniqueness/existence proofs by recursion on k are all
effective syntactic operations. In a fixed standard proof calculus they can
be implemented as primitive-recursive proof constructors. Replacing each
full-EPSC axiom line by the corresponding EPSC_1+PairO derivation then gives
a uniform transformation of complete finite proofs.

Thus a PA-formalizable transformation is a sound conventional mathematical
claim if these proof constructors and their inductive correctness argument
are provided. It is not a claim that a particular PA/Lean/Coq certificate
has already been implemented or kernel checked. No specific polynomial or
elementary size bound should be claimed without counting the chosen
formula and proof encoding.

No restriction to well-founded or extensional models enters. The syntactic
proof applies to arbitrary first-order structures, and the same inductive
syntax argument is the route needed to cover nonstandard internally coded
formulas in an arithmetized statement. A bare appeal to semantic completeness
would leave that uniformity less explicit, so the direct I/U proof and the
recursive proof-transformer description are preferable.

Finally, the theorem says nothing by itself about a smaller literal Turing
machine. The fixed PairO axiom contains the full profile formula O, and its
cost must be compiled and counted. The existing 253 machine enumerates a
different gated SIR presentation with numeric aliases. Its completeness,
freshness and falsity conventions must not be assumed to survive merely
because abstract schema parameter arity has been reduced.

## Short adjunction surcharge: independent follow-up audit

The shorter fixed axiom suggested later is also sound. To avoid confusing
it with the auxiliary union-profile formula above, write the outgoing
preorder as U_out:

    U_out(y,b) := forall z [y in z -> b in z]
    AU := forall a b exists c forall y
             [y in c <-> (y in a or U_out(y,b))].

The key reduction U_out(y,b) <-> O(y,b) is **EPSC_1-provable, not pure
logic**. EPSC_1 supplies an observational singleton S_y for every y by the
constant one-parameter matrix r(x,z;y)=O(z,y). The fiber bound is y; an
empty object activates all outputs; support gives exactness. Since y is a
member of S_y, U_out(y,b) puts b in S_y and hence O(b,y). The opposite
implication follows from pure logical O-congruence.

Therefore EPSC_1+AU gives PairO: first obtain an observational singleton
S_a, then apply AU to S_a and b. Its resulting member predicate is
O(y,a) or O(y,b). The already audited parameter-collapse proof now yields
all EPSC instances.

For the converse, full EPSC must prove AU, including the boundedness of
its exact-class construction. PairO(a,b) alone would not provide that
bound. The following route does, and keeps the matrix at two parameters.

First, EPSC_1 proves a transitive container V containing any a. One explicit
bootstrap defines S(x) to mean that x is nonempty and all its members are
pairwise O-equivalent, and uses the one-parameter matrix

    G_a(x,y) := (E(x) and O(y,a))
             or (S(x) and y in x)
             or (not E(x) and not S(x) and Sub(y,x)).

Its fibers are bounded by a, a chosen member of the observational singleton
x, or x, respectively. The empty seed puts a in the closure C. To check
transitivity, suppose x in C and y in x. If S(x), the second branch puts y
in C. Otherwise x is nonempty and nonsingleton. Obtain an observational
singleton S_y. Every member of S_y is O-equivalent to y and hence belongs
to x; thus Sub(S_y,x), the third branch puts S_y in C, and the singleton
branch then puts y in C. The empty case is vacuous. This uses no PairO.

Second, EPSC_1 proves exact raw Union(P). Its constant one-parameter matrix
is r(x,y;P)=exists t(t in P and y in t). A transitive container of P bounds
every such y as a subset, so SB holds. The empty seed and support give
precisely the raw union member predicate. No third parameter is introduced.

Now use full EPSC to obtain a transitive container V with a in V, an
observational pair P of V and b, and its raw union B. Then V is a subset
of B and b is a subset of B. If y in a, transitivity makes y a subset of
V and therefore of B. If O(y,b), y is a subset of b and therefore of B.
Consequently the constant two-parameter matrix

    r(x,y;a,b) := y in a or O(y,b)

has its required fiber bound. B occurs only in the derivation of SB and
is not a free matrix parameter. EPSC_2 now supplies the exact extension;
U_out=O rewrites it to AU. This validates the strengthened conclusion

    full EPSC  <->  EPSC_2  <->  EPSC_1 + AU.

AU has four displayed relation atoms when biconditional is counted as a
primitive connective; PairO has nine with the same convention. Expanding
biconditionals or changing the formula codec changes this metric. It is a
syntactic comparison, not a machine-state saving or a claim of optimality.
As above, all proof steps are ordinary mathematical derivations awaiting
implementation as a checked proof transformation.
