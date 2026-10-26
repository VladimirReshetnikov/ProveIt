# Round23: pruned arithmetic-DAG height-one quartics

All coordinates are unrestricted integers. Every delivered coefficient array defines a literal polynomial of exact total degree four, constant coefficient one, and nonzero collected coefficients exactly ±1. The polynomials are nonnegative on all real tuples. This file proves the unbounded algebraic equivalence; exact finite expansion checks the stated metrics independently of the construction algorithm.

## 1. Source interface and monic preliminary transformations

`SOURCE_BINDINGS.json` pins the exact original quadratic systems and identifies their surrounding ordinary consistency calibrations. The inherited source theorem is: ordinary ZFC proves that an integer zero exists exactly when a finite ZFC refutation exists. The present package transfers that theorem, and does not prove consistency. The source calibration is an explicit inherited hypothesis/interface, not a consequence of finite tests here.

For each selected rank-one quadratic part ηL(x)², η∈{−1,+1}, introduce the affine coordinate z=L(x)+k. Replace the original row R by ηz²+R−η(L+k)² and retain the monic definition of z. Identical definitions may be shared. Substitution of the unique affine values recovers every original row exactly. Conversely the definitions force those values, so zero sets are in bijection. Fixed selections are certificate data, not final equation parameters.

For positive integer coefficients, introduce triangular monic addition-chain constants and monic scale definitions s=cx as needed. Replace each row by a sum of signed monomial occurrences of degree at most two and coefficient ±1. Substituting all constructor values recovers each source row exactly; all constructor rows vanish. The independent checker verifies every source pullback, unique monic pivot and complete constructor coverage. Multiply any normalized row by its certified sign ε_r∈{−1,+1}; this does not change its zero set.

### 1.1. New Round21 multiplicative coefficient sharing

The inherited Round21 compact505 and compact512 profiles split an absolute
quadratic coefficient |c|=a*b into positive integer factors. Define
S(1,x)=x, and for d>1 retain one shared monic scale S(d,x)−K_d*x=0,
where the triangular addition-chain constructors force K_d=d. Replace
an occurrence c*x*y by sign(c)*S(a,x)*S(b,y). Its pullback is identically
c*x*y, including x=y and negative or zero values of x,y. No division or
congruence hypothesis is introduced. Repeated (d,x) scales are shared.
Constants and scales unused by the selected source representation are
not introduced. All retained constructors remain monic triangular, so
lift and projection are inverse bijections with the same original source
zeros. The complete independent source-row and constructor checks in §1
apply without change; both normalized product factors may be scales.

The deterministic selector starts with the inherited shared-scale
vertex-cover choices. For each distinct (|c|,x,y) pattern it enumerates
all positive factor pairs and both orientations. It makes at most ten
ordered sweeps, accepting only a strict decrease in the finite cost
(number of used scales plus number of directly needed constants).
The inherited addition-chain rule then constructs the needed constants.
This cost is a search heuristic, not a theorem of minimal final size.
Exact final collection and complete source pullbacks establish the
selected equations regardless of heuristic quality.

The old normalization, new normalization, and their final network
polynomials need not share a final coordinate namespace. Their zero-set
bijection is the composition of canonical projection to the common source
and the other canonical lift. The universal lift identity in §6 holds for
each, with its own certified row orientations. The frozen Round21 verification replayed
both the exact Round20 controls and its intermediate cycle-only controls
on identical sources, hubs and seeds. The current release instead pins the
resulting Round21 endpoint bytes as unchanged-normalization controls. Cycle-only counts 505/20483
and 512/18247 become Round21 selected counts 505/20405 and 512/18184. Round22 compact496, compact504, and compact507 retain that splitting rule before applying the additional constructors below.

### 1.2. Round22 product constructors for constants

Retain the exact inherited normalization variable list, constant values,
scale values, and source rows. A constant coordinate K_c originally has a
monic addition-chain definition. If the retained constant set contains
positive integers 1<a<=b<c with a*b=c, replace that definition by

    K_c - K_a*K_b = 0.

Choose the eligible pair with lexicographically least (b,a). Constants are
listed in increasing numerical order. Thus both factors have earlier
coordinates, even when a=b, and all unchanged addition-chain definitions
remain triangular. Induction forces K_c=c uniquely. The new constructor has
two signed monomial occurrences rather than three; no coordinate is added
at this normalization stage. Both residual degree and coefficient height at
the normalized occurrence level remain at most two and one respectively.
No division, positivity restriction on the final quantified coordinates,
or new existence assumption has been introduced: positivity is a property
of the uniquely forced integer constants, not a side condition.

The normalized zero sets before and after this replacement are literally
equal in the same coordinates. Both systems uniquely extend each original
source zero by the same constants and scales. Off zero, the constructor
residuals differ, and the final network polynomials generally differ.

### 1.3. Round22 chained scale constructors

For the minimum493 profile only, after §1.2 also consider each retained scale
S(c,x). If an integer d with 1<d<c has a retained K_d and the retained scales
include S(b,x) with d*b=c, replace

    S(c,x) - K_c*x = 0

by

    S(c,x) - K_d*S(b,x) = 0.

Choose the lexicographically least (d,b). All constants precede scales, and
scales are ordered by (coefficient,source-coordinate), so b<c makes the
predecessor scale strictly earlier. Induction forces S(c,x)=c*x for every
integer x, including zero and negative values. This is again a monic
triangular definition, without division or a divisibility hypothesis.
The normalized zero sets are identical, and lift and projection remain
inverse. Every original source row is unchanged, with the same pullback.

`check_product_constants.py` is independent of both normalizers. It removes
certified row orientations, checks the identical coordinate list and all
row metadata, enumerates the allowed earlier factors independently, checks
every expected changed row and every unchanged row exactly, and rejects five
constant/source mutation classes plus one extra chained-scale mutation.
`check_network.py` separately checks every monic pivot, constructor pullback,
source pullback, occurrence, alias, graph, coefficient, and symbolic lift.

The network compiler and its deterministic alias contractions see a
structurally changed residual system; final alias and flow coordinate counts
may therefore decrease although the normalization coordinate list is fixed.
The zero-set bijection between old and new final polynomials is canonical
projection to the shared original source followed by the other canonical
lift. It is not asserted to be the identity between different final
coordinate spaces. The universal identity in §6 applies to both, with their
own row orientations and lifts.

Every selected equation is compared against the unchanged-normalization
algorithm with identical original/refactored source, hub count, seed, and
coefficient splitting choice. All but the h26 control are byte-identical
frozen Round21 endpoints. The h26 control is newly generated and explicitly
labeled as such, not called a historical endpoint. For minimum493, the
constant-only intermediate compact494 is separately checked; its
494/24648 counts become 493/24828 under scale chaining. Neither support nor
variable count is claimed monotonically improved for every operation.
All selected outputs are fully collected and checked, rather than relying
on a collision heuristic. Fixed parameter selection is not a minimality
claim. The five historical endpoints 503/24183, 505/20405, 512/18184,
617/8314, and 713/7172 are dominated by some selected Round22 endpoint;
557/11991 remains as a tradeoff.

## 1.4. Round23 source-product fusion and dead-constructor pruning

Start from the triangular monic constant/product/scale normalization above.
For a source monomial of constant value c, replace a retained K_c by
K_a*K_b whenever a*b=c and both constants are available. For a source
linear term c*x, available alternatives are S(c,x) and K_a*S(b,x), where
S(c,x) is retained, or a*b=c and both factors are retained. Signs of the
source occurrences are unchanged. The inherited representation of every
quadratic source monomial is retained. Every replacement is one signed
monomial of degree at most two and has exactly the same pullback to the
original coordinates. It does not assert equality away from constructor
zeros: for instance K_6 and K_2*K_3 need not agree at an arbitrary tuple.

The producer enumerates these finite alternatives. It uses a deterministic
initial ordering (the selected profiles use product-first), then at most
five strict-cost-improving ordered sweeps, where cost is the number of
constructor coordinates reachable from source terms, then their total
occurrence count. Dependency closure is computed from the actual selected
constructor rows. Every constructor not reachable from a source term is
deleted, and remaining coordinates are compacted in inherited order.
This heuristic is not a theorem of minimality. The complete final literal
coefficient array, not the cost, justifies every final dimension/support
claim.

To prove deletion safe, note that every retained constructor dependency is
retained. Thus their monic triangular definitions still uniquely extend any
original tuple. Every deleted coordinate in the old normalization also has
a unique intended value (its integer constant or its coefficient times its
original coordinate). Given a zero of either normalization, projection to
the original tuple and canonical evaluation of the other constructors gives
a zero of the other. The compositions are identities on zero sets. In the
old-to-new direction this is ordinary projection to the retained coordinates;
the reverse restores exactly the deleted intended values. No positivity,
congruence assumption or division has been added.

## 1.5. Round23 additive inlining of low-use constants

Let K_c be a retained constant coordinate, and let a+b=c, with
1<=a<=b<c. Define K_1=1 as notation, not a new coordinate. If a,b>1 their
coordinates are retained and earlier than K_c. Delete the defining row of
K_c. In every remaining normalized row, substitute K_a+K_b for every
occurrence of K_c and expand distributively. If K_c occurs twice in a
quadratic monomial, all four signed occurrences are retained; no coefficient
is silently divided or changed. In particular a=b gives repeated
occurrences, each with coefficient ±1, rather than a purported collected
coefficient-one identity.

All replacement monomials still have degree at most two. Every other
constructor keeps its own coefficient-one pivot, and substituted factors
are earlier, so its triangular monic property persists. Induction gives
its original intended value. Every source pullback remains exact because
a+b=c. Conversely a new normalized zero restores K_c=c, and all old source
rows and the deleted constructor vanish. Deleting/restoring K_c gives
inverse bijections on real and integer zero sets. Repeated inlining composes
these maps in reverse deletion order. The producer's usage budget and
pair-selection order only choose which valid identities to use; they are
not necessary hypotheses of this proof and do not guarantee monotone final
support or variable counts.

## 1.6. Round23 expansion of rare scale coordinates

Let S(c,x) be a retained scale, c>1. Delete its defining monic row and
replace every occurrence of this coordinate in remaining rows by c copies
of x, distributively. This means the integer linear polynomial c*x, not a
newly quantified coordinate. A quadratic occurrence containing the scale
twice expands to c² equal signed degree-two occurrences. Each occurrence
has coefficient ±1. The source coordinates are earlier than every
constructor, so all remaining constructor pivots stay monic and triangular.
Their pullbacks are unchanged. The deleted scale is restored uniquely as
c*x, over all real or integer x, including negative and zero values.
Projection and restoration again give inverse zero-set bijections.

After scale expansion, dependency closure deletes unused constructors as
in §1.4. The selected rule tests the exact normalized occurrence increase
against a fixed budget, but full graph expansion can increase or decrease
final support. No general monotonicity is asserted. These repeated signed
occurrences are subsequently represented by distinct source occurrences in
the graph, with independent alias choices as needed; repeated occurrences
are never confused with a collected height-one coefficient. Only the final
fully collected polynomial is required to have coefficient height one.

## 1.7. Independent normalization and provenance checks

The inherited `check_network.py` is unchanged: it imports no producer and
computes each retained coordinate's intended polynomial from its metadata.
For every normalized row it independently substitutes these polynomials.
It requires every source row, with its certified sign, to pull back exactly
to its pinned source residual, each constructor to pull back identically to
zero, every extra coordinate to have precisely one monic triangular pivot,
and every source row to appear exactly once. This validates all fusion,
inlining and pruning steps without trusting their selectors or their
recorded costs. `check_factor.py` separately verifies the complete affine
source pullbacks to the four byte-pinned inherited original sources.

The final independent audit reconstructs the literal polynomial from
square differences, checks every occurrence and factor binding, every graph
boundary, each internal spanning tree, all aliases, units, and all symbolic
lift divergences. It requires exact degree four, constant coefficient one,
coefficient set {-1,+1}, and participation of every claimed coordinate.
`verify.py` additionally parses the literal text independently, checks all
endpoint hashes, exercises mutation rejection, and byte-rebuilds selected
outputs and exact same-source/hub/seed controls in both ordinary Python
and `python -O`. The normal and optimized receipts apply to the final
snapshot, not to earlier exploratory results.

The controls are the frozen Round22 equations when the graph parameters
match; any newly generated parameter-matched controls are explicitly marked
as such. The new profiles may use inherited scale chaining in addition to
fusion/inlining; a full-normalization comparison is not incorrectly called
an isolated one-operation experiment. The claimed Pareto comparisons concern
only the explicitly enumerated finite candidate set, not all Diophantine
representations or all graph choices.

## 2. Incidence and equality energy

Assign a nonempty vertex block to each normalized row and one to a hub. Each block has independent integral flow coordinates on a spanning tree. Represent each normalized monomial occurrence by an edge from its row block to the hub, or pair identical opposite-sign occurrences in different rows and use one direct edge between those blocks. Every occurrence is bound exactly once. Each prescribed edge has a signed degree-two label in aliases of its logical factors; aliases of one homogenize lower-degree terms.

Let d_v be the signed divergence at vertex v. Set E=½∑_v d_v². Internal tree flows cancel in block sums. After all aliases take their logical values and units take one, the row-block boundary sum is the signed normalized residual T_r and the hub boundary is −∑_rT_r.

For a class with k≥3 aliases use

    C(a_1,…,a_k)=∑a_i²−∑a_i a_(i+1), cyclically.

Then 2C=∑(a_i−a_(i+1))², so its zero set is equality of all aliases. A singleton needs no penalty. For two aliases one may use the quartic penalty

    Q(a,b)=a⁴+b⁴−a³b−ab³=(a−b)²(a²+ab+b²).

It is nonnegative and vanishes exactly at a=b; also 2Q=(a²−b²)²+(a²−ab)²+(ab−b²)². Otherwise the prior construction adds one equality dummy d and uses C(a,b,d).

For unit aliases u_1,…,u_l, l≥2, use

    U=1+∑u_i²−u_1−u_l−∑_(i<l)u_i u_(i+1).

Its double is (u_1−1)²+∑_(i<l)(u_i−u_(i+1))²+(u_l−1)². Thus U is nonnegative and is zero exactly when every unit alias is one. The final polynomial is incidence energy plus the chosen equality penalties plus U.

Same-logical alias identifications preserve the source interface and are accepted only when full coefficient collection passes. The inherited polarization step may change prescribed a² or b² labels to ab within a two-alias logical class and replace C(a,b,d) by Q(a,b), deleting d. At equality the labels have identical values; the complete polynomial is again checked for height one. `INHERITED_POLARIZATION_PROOF.md` and `INHERITED_NETWORK_PROOF.tex` retain the complete prior arguments.

## 3. New operation: replace an equality dummy by an anchored-unit product

Suppose d appears only in C(a,b,d), and u is an already existing unit alias in the unchanged unit path. Substitute d=au. The new penalty is

    G(a,b,u)=C(a,b,au)
             =a²+b²+a²u²−ab−abu−a²u.

It has degree at most four and

    2G=(a−b)²+(b−au)²+(au−a)².

Therefore G≥0 for every real tuple, without assuming u=1. In a zero of the complete energy the independent unit summand forces u=1. Then G=0 is equivalent to a=b. Conversely every old zero has u=1 and d=a=b, so it satisfies d=au; projection deletes d and preserves zero. Every new zero uniquely restores d=a (equivalently au), giving the inverse map. No new coordinate is introduced. One may interchange a and b and use bu instead.

The independent step checker verifies literally that d is an equality dummy in one three-cycle, occurs in no edge or other equality/unit relation, and that the selected u is an existing anchored unit. It substitutes d=au into the entire old literal coefficient array and checks equality to the new array. The final checker reconstructs G from its three square differences independently of the producer.

This operation need not preserve height for an arbitrary choice of u. The finite algorithm tests all eligible anchor/unit choices against the complete current coefficient map, chooses deterministically by support then indices, and accepts only height one. Final full expansion checks height, degree, constant and participation of every coordinate. These finite checks, not an unproved collision heuristic, justify the numeric claims.

## 4. New operation: contract an internal tree edge

Let an internal free edge of a row or hub block run from u to v with its independent flow coordinate w and coefficient +1. Write d_u=A+w and d_v=B−w, where A and B do not involve w. Delete w, identify v with u, and redirect every other endpoint v to u. The merged divergence is A+B. All other divergences and all equality/unit penalties are unchanged. A tree contracted at one edge is again a tree; source-block boundary sums are unchanged.

Projection maps every old zero to a new zero, since d_u=d_v=0 implies A+B=0. Given any new zero, uniquely restore w=B. Then d_v=0 and d_u=A+B=0, so this is the inverse on zero sets, entirely over integers. More strongly, for every remaining tuple,

    P_old(w=B)=P_new,

because ½[(A+B)²+0²]=½(A+B)². The restore polynomial B has degree at most two and integer coefficients. Repeating contractions preserves the bijection; restores compose in reverse order.

The implementation only contracts within one block, never across constraints. The independent step checker verifies the exact edge, retained namespaces and quotient graph, then verifies the full literal off-zero substitution identity above. A contraction is accepted only if the full collected new polynomial still has height one; released profiles may additionally require that support not increase. No theorem says that arbitrary edge contractions preserve height.

After contraction, one may repeat same-logical alias identification on the changed graph and rebuild its equality penalties. Both graphs have the same source zero set with the same unique tree-flow construction. Hence this optional renewed contraction also induces a bijection, and its final source/alias/edge semantics are checked directly.

## 5. New Round21 operation: unit-homogenize the equality cycle

Let a and b be the two aliases of one logical variable. Their old equality
penalty is either Q(a,b), or C(a,b,a*u) (possibly with b as anchor), proved
above. Let f1,f2,f3 each be a or b, optionally multiplied by one existing
unit alias from the unchanged anchored unit path. Require that both a and b
occur as the alias factors. No new coordinate is introduced. Replace the
old equality penalty by

    H = C(f1,f2,f3) = f1² + f2² + f3² − f1*f2 − f2*f3 − f3*f1.

Exactly, for every real tuple,

    2H = (f1−f2)² + (f2−f3)² + (f3−f1)².

Thus H is nonnegative everywhere and has degree at most four. In a zero
of the complete polynomial the independent unit path forces every unit to
one. Then every fi equals its underlying alias. Since both aliases occur,
H=0 is equivalent to a=b. Conversely every old zero already has a=b and
all units one, hence H=0. Therefore replacement preserves the entire real
and integer zero sets, literally in the same coordinate space. The witness
map and its inverse for this step are both the identity, not only an
existential extension/projection. This assertion is about zero sets: the
old and new polynomials are generally unequal away from zero.

The useful selected shape is C(a,b*u,b*v), or its alias-swapped form. The
new negative term −b²uv can cancel an existing positive incidence-energy
coefficient, while its positive terms do not collide after full collection.
This explains a possible support gain; it does not assert that an arbitrary
choice of anchors or units preserves height. `anchored_cycles.py` enumerates
a fixed finite family: a bare first alias (both alias orders), a second alias
optionally multiplied by a unit, and either alias optionally multiplied by
a unit as the third form. It requires distinct monomials, tests every
changed coefficient against the complete current coefficient map, accepts
only exact height one and a strict collected-support decrease, and breaks
ties by the literal tuple of forms. No random seed or search optimum is
part of this improvement.

The independent checker verifies that each form uses exactly one of the
two aliases and at most one existing anchored unit, that both aliases are
covered, and that there are no dummy or extra free factors. It independently
expands the three square differences, combines them with every incidence,
unit, and other equality square, checks divisibility by two, and compares
every coefficient to the literal file. The independent step checker verifies
the unchanged graph, units and coordinate namespace, the complete changed
relation ledger, and the exact full-polynomial identity

    2(P_new − P_old) = sum(new cyclic difference squares)
                      − sum(old equality difference squares).

It does not incorrectly claim P_new=P_old off zero. The frozen Round21 release replayed exact hashes of all six
Round20 input polynomials and semantic certificates on matched sources,
hub counts and seeds. The current verifier independently rechecks the
selected step identities and its pinned Round21 controls. For the matched cycle-only controls, the six strict support
decreases are 10, 8, 8, 8, 4 and 4 monomials respectively. The two compact
selected equations additionally use §1.1 and have the stronger support
reductions stated there. All coordinates
remain live after collection; variable counts are unchanged.

## 6. Universal lift, inverse and consistency transfer

Given any original source tuple x, evaluate every monic constructor. Assign each alias its logical value, units the value one, and any remaining equality dummy its class value. In each block root the internal tree at the first listed vertex. Let b_v be prescribed divergence and let τ_v=±1 be the sign of the tree edge at child v. Put

    w_v=−τ_v∑_(t in the subtree rooted at v)b_t.

Leaf elimination makes all nonroot divergences zero, leaves signed normalized residual T_r at row root r, and leaves −∑T_r at the hub root. All equality and unit penalties vanish universally on this lift, including G and H because every anchored unit is one and all aliases of a logical variable agree. Constructor residuals vanish and original residuals pull back with their certified signs. Thus, for every original tuple, not merely zeros,

    P(L(x))=[∑_j R_j(x)²+(∑_j δ_j R_j(x))²]/2,

where R_j are the original residuals and δ_j their certified row signs. The hub cross term is essential; this is not generally the bare source sum of squares. The checker verifies the symbolic lift at every vertex and exact source pullbacks, so the full composed identity is checked rather than inferred from samples.

Conversely, P=0 forces every nonnegative summand to vanish. Units equal one; C, Q, G and H force equality of all aliases in each logical class; all divergences vanish. Summing over each row block gives T_r=0. Monic definitions force their intended values, so projection gives an original source zero. Aliases, constructors and remaining equality dummies have unique values, and tree leaf elimination uniquely determines every flow. Canonical lift and projection are inverse bijections on integer zero sets.

Combining with the pinned source calibration, ordinary ZFC proves

    (∃z∈Z^n, P(z)=0) ↔ (there is a finite ZFC refutation),
    (∀z∈Z^n, P(z)≠0) ↔ Con(ZFC).

No consistency assumption is needed for these equivalences. Neither unsolvability nor Con(ZFC) itself is established. No global minimum, exhaustive Pareto frontier, literature priority, or new complete proof-assistant certificate is claimed.
