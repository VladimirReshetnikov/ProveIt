# A 25-operation positive merge of typed prefix normal forms

Two nonzero binary stack partial maps can be composed by a fixed
arithmetic graph with **25=10M+15A operations, four positive auxiliary
witnesses and seven equations**, provided their input descriptors are
already typed. One sum-of-squares polynomial costs **45=17M+28A**.
The graph has a positive solution exactly when the composition is
nonzero and the supplied output is its exact prefix normal form. Output
typing follows from the equations; it is not another assumption.

This is a local composition theorem. Its four input length powers and
their code bounds are external hypotheses. A fixed tree of these merges
can be completely accounted for, but a variable action word, its tree
geometry, finite control, input loading and empty tests are not supplied
by this packet. No complete universal bound is improved.

## 1. The typed input and output interfaces

Write binary words top first and define

    L_w=2^len(w), E_w=L_w+sum_j w_j*2^j.

A positive pair(E,L) is **typed** when L is a power of two and

    L<=E<2L.                                         (1)

It then encodes exactly one finite binary word. The empty descriptor is
(1,1). Concatenation satisfies

    E_(uv)=E_u+L_u*(E_v-1), L_(uv)=L_u*L_v.           (2)

A nonzero prefix normal form(u,v) denotes the partial function

    u z -> v z, for every finite binary suffix z.     (3)

Supply two input descriptors, in this order:

    first  = (U,Lu,V,Lv), representing(u,v),
    second = (A,La,B,Lb), representing(a,b).

All four pairs(U,Lu),(V,Lv),(A,La),(B,Lb) must satisfy(1).
In particular, all four power-of-two claims are external to the local
certificate. They do not become free because a scale is stored as an
integer. Supply four output coordinates(C,Lc,D,Ld), representing the
proposed normal form(c,d). These are relation arguments, like the
source and target configurations of a scalar step; the four auxiliary
witnesses counted below are additional to them.

Composition means applying first and then second. Directly from(3):

    if v=a t, the output is(u,b t);
    if a=v t, the output is(u t,b);
    if a,v are prefix-incomparable, the product is0.  (4)

When a=v, both descriptions use the empty tail and give the same result.
The domain in(3) is retained exactly. A restricted identity such as
(0,0) is not silently replaced by(empty,empty).

The [preceding history note](two_stack_polycyclic_history_obstruction.md)
proves the normal-form contract and explains its relation to stack
actions. The partial-function substrate is also described in
[Kambites, Section4](https://arxiv.org/pdf/math/0601061). All arithmetic
claims here are proved below.

## 2. The seven equations

Supply only four strictly positive integers

    theta, theta_bar, T, S.

The first equation is

    theta+theta_bar=3.                               (5)

It forces theta in{1,2}. Define computed, not existential, quantities

    e=theta-1, g=T-1, s=S-1,
    f=e*g, h=e*s, J=La+Lv.                           (6)

Thus e is0 or1, g,s are nonnegative, and f,h select the second
orientation of(4). The two compatibility equations are

    V = A + La*g - J*f,
    Lv = La + La*s - J*h.                            (7)

The four output equations are

    C  = U  + Lu*f,
    D  = B  + Lb*(g-f),
    Lc = Lu + Lu*h,
    Ld = Lb + Lb*(s-h).                              (8)

All descriptor and auxiliary coordinates are positive. Subtractions and
computed zero values in(6)–(8) do not introduce zero-valued existential
witnesses. All seven equations are ordinary integer polynomial
equations. There is no arithmetic division, a variable exponent, or a
runtime string operation in their graph.

## 3. Full positive soundness and completeness

First suppose a positive assignment satisfies(5)–(8), with the four
input descriptors typed.

If e=0, (7) becomes

    V=A+La*(T-1), Lv=La*S.                            (9)

Because La and Lv are powers of two and S is a positive integer, S is
itself a power of two. The input bounds A in[La,2La) and
V in[Lv,2Lv) imply

    S-2 < (V-A)/La < 2S-1.

The middle expression is the integer T-1, so

    S<=T<2S.                                        (10)

There is therefore a unique binary tail t with code T and scale S.
Equation(2), together with(9), gives v=a t. Equations(8) then give
exactly c=u and d=b t, with their correct length powers. In particular
the output is typed without imposing another set of bounds or powers.

If e=1, (7) instead becomes

    A=V+Lv*(T-1), La=Lv*S.                           (11)

The same argument with A,V interchanged proves(10), so a=v t for the
unique typed tail(T,S). Equations(8) give c=u t and d=b with their
correct length powers. This is exactly the second case of(4).
Both cases prove that a positive solution represents the genuine
nonzero composition; an incomparable pair cannot satisfy the graph.

Conversely, if the composition is nonzero, use either applicable case
of(4). Take theta=1, theta_bar=2 for v=a t, or theta=2, theta_bar=1
for a=v t, and supply T=E_t, S=L_t. These are all strictly positive.
The concatenation identity(2) verifies every equation. All output
coordinates are the positive codes and scales of the words in(4).

For unequal middle words, the valid orientation and its tail are unique.
For equal middle words, both selector choices are valid, but both force
T=S=1 and the identical output. Hence auxiliary nonuniqueness creates
no ambiguity in the composed partial map.

The proof also shows that the output values in(8) are positive even if
their positivity is not assumed separately: each is a positive input
coordinate plus a nonnegative term.

## 4. Why input typing must remain visible

The graph does not type its own input scales. For example, take

    first=(1,1,6,6), second=(3,3,1,1),
    output=(1,1,2,2), auxiliaries=(1,2,2,2).

Every equation vanishes, but the scales3 and6 are not powers of two.
The actual binary words with codes6 and3 are(0,1) and(1); they are
prefix-incomparable. This is a false composition if one interprets just
the codes while discarding the scale typing.

Even honest powers alone do not suffice. The assignment

    first=(1,1,6,4), second=(4,2,1,1),
    output=(1,1,2,2), auxiliaries=(1,2,2,2)

also satisfies every equation. Now every scale is a power of two, but
the second input's A=4 violates A<2La=4. The actual words with codes6
and4 are(0,1) and(0,0), again incomparable. Thus the code bounds in(1)
are indispensable as well.

When the leaves of a finite composition tree are fixed typed word
constants, their typing is true by construction, and Section3 propagates
it to every internal output. No repeated exponent certificate is
needed in that fixed-tree setting. Arbitrarily supplied leaf descriptors
or a variable collection of leaves require their own paid typing.

## 5. Exact local and fixed-tree costs

The [literal source](typed_prefix_normal_form_merge25.py) uses the
following shared values and schedule:

| Block | Multiplications | Additions/subtractions |
|---|---:|---:|
| Bound(5), e,g,s,J, g-f and s-h |0|7|
| f=e*g and h=e*s |2|0|
| Two compatibility equations(7) |4|4|
| Four output equations(8) |4|4|
| **Total** |**10**|**15**|

The seven residual subtractions, seven squares, and six additions
combine the equations into one polynomial, costing7M+13A beyond the
graph. The total is **45=17M+28A**, with the same four positive
auxiliary witnesses. This is a literal schedule, not an optimality claim.

Now fix t>=2 typed leaf descriptors as source constants and fix any
ordered binary composition tree. Keep its four root coordinates as the
supplied output of the relation. There are t-1 merge nodes. Supply the
four coordinates of each of the t-2 nonroot internal outputs, and four
auxiliary witnesses per merge. Each child's output coordinates are used
as its parent's input coordinates. The exact totals are

    positive internal witnesses=4(t-2)+4(t-1)=8t-12,
    equations=7(t-1), graph=25(t-1),
    graph M=10(t-1), A=15(t-1),
    polynomial M=17(t-1), A=29(t-1)-1,
    polynomial operations=46t-47.                    (12)

The root coordinates are relation arguments and are not included in
the internal witness count. If a later construction makes them
existential, it must count those additional coordinates too.

Induction on the tree and Section3 prove exactness. If the full product
is nonzero, every subtree product is nonzero, since a zero partial map
is absorbing. All honest normal forms and local witnesses therefore
exist and are positive. Conversely, every satisfying tree assignment
consists of genuine nonzero subtree products and the correct root.
Root and intermediate output typing follow from the fixed leaves.

The equation count, witnesses and source geometry in(12) grow with t.
The construction does not quantify the tree shape or select leaf labels.
A formal product of arbitrarily many maps is not evaluated by one
25-operation call.

## 6. Empty tests, ordinary input and the remaining history work

This merge handles prefix cones(3). An empty-stack test has a singleton
domain and is not one of these nonzero binary normal forms. The earlier
history note gives an exact bottom-marker compilation. Using that
compilation still requires its marker/word encoding and its input
bridge; the ordinary affine binary-stack loader is not automatically a
loader for words encoded with an extra color. Another possible extension
would record whether the domain is a cone or a singleton and pay for
its composition cases. Neither extension is implemented or counted here.

For a pure binary push/pop word, each letter has a fixed typed descriptor:
push b is(empty,b), and pop b is(b,empty). A supplied starting stack with
ordinary code kappa*x+lambda belongs to the final domain only when it
has the prescribed prefix. Requiring an empty final stack imposes an
additional endpoint constraint. These input/domain checks are not
included in25, and a type for the variable starting stack's length
power is not silently supplied.

For a universal two-stack computation, both products must also refer to
the same selected finite state path. Constant-size local merges do not
encode that selection, synchronize the two products, or provide a
uniform arithmetic certificate for an arbitrary number of nodes. These
are concrete remaining costs, independent of the exact local theorem.

## 7. Replay and independent semantics

The [checker](typed_prefix_normal_form_merge25.py) compares by default
with its deterministic [receipt](typed_prefix_normal_form_merge25.json).
It exhausts bounded selector/tail assignments, both prefix directions,
empty tails and word-code boundaries; compares genuine merge witnesses
with independent string composition; and rejects corruption of every
output coordinate. Separate random cases compare actual partial-map
domains and arbitrary positive polynomial assignments. Both explicit
missing-typing counterexamples above are replayed.

Two independent full proof/source/default reviews passed. One also
checked the seven residuals and their sum of squares symbolically. The
other independently solved both orientations on10,000 typed input pairs,
finding2,880 positive orientations and rejecting7,233 zero products;
the overlap consists of equal middle words with two valid selectors.
Output mutation checks and the exact25/45 operation histograms passed.

Left-associated, right-associated and balanced fixed trees are checked
against sequential string composition. The tree source shares each
supplied child output with its parent's inputs; mutation checks include
internal scales and the root. Counts include all residuals and every
sum-of-squares operation. Finite replay supports the implementation; the
unbounded local theorem and its typing propagation follow from the proof
in Section3. No new universality theorem or complete Diophantine bound
is asserted.
