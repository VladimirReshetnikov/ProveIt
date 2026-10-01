# Exact binary empty tests and prefix composition in 31 operations

The [typed prefix merge](typed_prefix_normal_form_merge25.md) extends to
singleton domains with **31=13M+18A operations, four positive auxiliary
witnesses and ten equations**. Its single polynomial costs
**60=23M+37A**. The extension represents empty-stack tests exactly while
keeping the binary stack alphabet. Positive domain flags save two
operations over the preliminary33-operation schedule.

A typed root normal form accepts an ordinary starting stack into empty
exactly when its output word is empty and its input word has code
**kappa*x+lambda**. This costs one multiplication and one addition.
The root's length power is supplied and typed by the composition tree,
so no separate input-length decoder or exponent relation is assumed.

The packet also gives fully paid fixed-tree and fixed-word endpoint
certificates. For a fixed word, its domain flags can be computed when
constructing the circuit, reducing each merge to the earlier25 gates
plus explicit zero equations. None of these families supplies a uniform
selected-word, finite-control or variable-tree compiler. There is no new
complete universal arithmetic bound.

## 1. Typed normal forms with exact domains

Write finite binary words top first. Their codes and length powers are

    E_w=2^len(w)+sum_j w_j*2^j, L_w=2^len(w).

An integer pair(E,L) is typed if L is a power of two and L<=E<2L.
The empty pair is(1,1), and

    E_(uv)=E_u+L_u*(E_v-1), L_(uv)=L_u*L_v.           (1)

Extend the prefix normal form(u,v) by a flag F in{0,1}:

    F=0: u z -> v z for every binary suffix z;
    F=1: u -> v, defined only on that single word.    (2)

The positive stored flag is sigma=1+F. The nowhere-defined map is0 and
has no normal-form descriptor. A descriptor is

    (U,Lu,V,Lv,sigma),                               (3)

where both code/power pairs are typed and sigma belongs to{1,2}.
The cone and singleton versions of(u,v) have different domains even
when their word coordinates agree.

The exact primitive stack operations are

| Operation | Normal form | Positive flag |
|---|---|---:|
| Push bit b |(empty,b)|1|
| Pop matching bit b |(b,empty)|1|
| Test empty |(empty,empty)|2|
| Do nothing |(empty,empty)|1|

A machine branch reading bit b and replacing it with a fixed word v
is(b,v,0). Reading empty and writing v is(empty,v,1). Thus the
[ordinary-input two-stack model](two_stack_affine_input_step.md) already
has fixed typed leaf descriptors in this binary representation. There
is no new third-color input encoding or a bottom-marker conversion in
this construction. The underlying prefix-map convention is discussed
in [Kambites, Section4](https://arxiv.org/pdf/math/0601061); the added
singleton domains and all arithmetic claims here are proved directly.

## 2. Generic positive local equations

The two typed input descriptors are

    first  = (U,Lu,V,Lv,sigma), for(u,v,F),
    second = (A,La,B,Lb,tau),  for(a,b,G).

The proposed output is(C,Lc,D,Ld,eta), for(c,d,H). These fifteen
coordinates are arguments of the composition relation. In addition,
supply only four strictly positive auxiliary witnesses

    theta, theta_bar, T, S.

All four input code/power pairs and both input flags are externally
typed. The local equations do not impose those input typing conditions.
They do prove typing of every output coordinate and its flag.

Keep all seven equations and shared values of merge25:

    theta+theta_bar=3,
    e=theta-1, g=T-1, s=S-1,
    f=e*g, h=e*s, J=La+Lv,

    V  = A  + La*g - J*f,
    Lv = La + La*s - J*h,
    C  = U  + Lu*f,
    D  = B  + Lb*(g-f),
    Lc = Lu + Lu*h,
    Ld = Lb + Lb*(s-h).                              (4)

The definitions in(4) name computed values, not extra equations or
witnesses. Supply three more equations:

    sigma*f = f,
    tau*(g-f) = g-f,
    eta = 2-(2-sigma)*(2-tau).                        (5)

Since sigma=1+F and tau=1+G, the first two equations in(5) mean

    F*e*(T-1)=0, G*(1-e)*(T-1)=0.                    (6)

The last gives eta=1+(F or G). Working directly with the positive flags
avoids separately computing F and G. The new guards cost2M. Computing
the two complements, their product and the final subtraction costs
1M+3A. Consequently the extension adds only3M+3A to merge25:

    31=13M+18A, four positive auxiliaries, ten equations.

Ten residual subtractions, ten squares and nine sums add10M+19A,
giving **60=23M+37A** for one polynomial. Computed zeros such as f and
2-sigma are allowed; every supplied coordinate remains strictly positive.

## 3. Exact nonzero composition in both orientations

Composition applies the first map and then the second. The merge25
proof shows that positive solutions of(4), on typed inputs, have exactly
one of the following interpretations:

    e=0: v=a t, (c,d)=(u,b t);
    e=1: a=v t, (c,d)=(u t,b).                       (7)

In either case the length equation forces S to be an integral ratio
of powers of two, hence a power of two. The input code bounds then
force S<=T<2S. Thus(T,S) is precisely the code and length power of the
tail t. Both output word pairs are typed. Incomparable middle words
give no positive solution.

The new domain guards in(5) are exactly what(7) needs:

* If e=0, then f=0 and g-f=T-1. When the second map is a singleton,
  it accepts only a, so v=a t can reach it only if t is empty. The
  second guard imposes exactly this condition. If the first map is a
  singleton, its starting suffix is already empty; the result is the
  singleton map u->b t. If both are cones, the result is the cone
  u z->b t z.
* If e=1, then f=T-1 and g-f=0. When the first map is a singleton,
  its output is exactly v, so it can meet the longer required prefix
  a=v t only if t is empty. The first guard imposes exactly this
  condition. If the second map is a singleton, the result is the
  singleton map u t->b. If both are cones, the result is the cone
  u t z->b z.

If both inputs are singletons, the two guards force T=1, hence t is
empty and v=a. The result is precisely u->b. If neither is a
singleton, both guards are automatic and merge25 is recovered.
The output domain is a singleton exactly when F or G is1, agreeing
with the last equation of(5).

This proves soundness for every positive solution, including its exact
domain, rather than only an extension of its affine action. Conversely,
every nonzero composition has an applicable orientation in(7). Choose
the corresponding positive selector and the genuine tail code and
scale. The domain conditions just proved ensure that both guards hold,
and the output flag is the positive numeral1 or2. This supplies all
four positive auxiliary witnesses. Equal middle words allow both
orientations with T=S=1; they give the same typed output and domain.

The two new guards are individually necessary. For example, composing
the singleton empty->empty with the cone0z->z has zero domain. The
cone-only merge would incorrectly return0->empty; the first guard
rejects it. Composing the cone z->0z with the singleton empty->empty
also has zero domain, and the second guard rejects it.

Input flag typing remains essential. Setting both input word pairs to
empty, both input flags to3, the output word pairs to empty and its flag
to1, with witnesses(1,2,1,1), makes every equation vanish. Those input
flags have no meaning in(2). Fixed typed leaves and inductive output
typing exclude this assignment in a composition tree. The earlier
missing-power and missing-code-bound counterexamples remain excluded
by the explicit input typing hypotheses as well.

## 4. Ordinary input to an empty endpoint

For either domain flag in(2), the represented map sends a starting word
w to empty exactly when

    u=w and v=empty.                                 (8)

For a cone, v z can be empty only when both v and z are empty; for a
singleton, the statement follows directly from its domain definition.
Thus a root already typed by a tree accepts a stack of ordinary code
kappa*x+lambda into empty exactly when

    U=kappa*x+lambda, V=1.                           (9)

Here x is a positive ordinary input, kappa>0 and lambda>=0 are fixed
program numerals. For the fixed binary program prefix p, they are
kappa=2^len(p) and lambda=sum_j p_j*2^j. The affine code in(9) is
computed with one multiplication and one addition. Root typing forces
Lv=1 when V=1, so both may be fixed to1 in the circuit. The positive
root Lu is still counted as a witness, but its power-of-two property
and its correct length are consequences of the merge tree. No separate
input power or digit-extraction relation is used.

For the universal two-stack interface, the left input is empty and the
right input has this affine code. Fix the left root word/scale coordinates
to(1,1,1,1); fix the right ones to(kappa*x+lambda,Lu,1,1). Only the
right Lu remains existential. Both output flags can be omitted: the
domain type is determined by the typed child maps, while(8) is valid
for either type. All flags at nonroot internal nodes remain available
for use by their parents.

Neither(8) nor(9) checks finite control. A pair of histories must still
come from the same selected sequence of machine branches, start at the
designated state and end in the accepting state. An empty stack endpoint
alone does not imply an accepting machine state.

## 5. Fully paid generic fixed-tree schedules

Fix an ordered binary tree with t>=2 typed leaf descriptors and let
m=t-1 be its number of merge nodes. Leaf descriptors and tree geometry
are source data. Every nonroot internal output has five positive
coordinates, and every merge has four auxiliary witnesses. With five
supplied root coordinates, the generic relation therefore has

    witnesses=5(t-2)+4(t-1)=9t-14,
    equations=10m,
    graph=13m M+18m A=31m,
    polynomial=23m M+(38m-1)A=61m-1.                 (10)

The root coordinates are relation arguments and are not included in
the internal witness count. Each child's supplied output is reused as
its parent's input. By induction, every satisfying assignment gives
the exact typed nonzero subtree product. Conversely, if the full product
is nonzero, every subtree product is nonzero because the empty partial
map is absorbing. All honest typed outputs and positive local witnesses
therefore exist.

For the endpoint specializations, omit the unused output flag at each
root. This removes1M+3A and one equation per tree. Fix the root word
coordinates as in Section4. The following schedules include the
two-operation affine ordinary-input loader exactly once:

| Fixed-tree certificate | Graph operations | Positive witnesses | Equations | Single polynomial |
|---|---:|---:|---:|---:|
| One input stack to empty |31m-2|9t-13|10m-1|61m-6|
| Two stacks, left initially empty |62m-6|18t-27|20m-2|122m-13|

For one stack the graph counts are13m M+(18m-2)A and the polynomial
counts are(23m-1)M+(38m-5)A. For two stacks they are
(26m-1)M+(36m-5)A and(46m-3)M+(76m-10)A respectively.
The one-stack witness count adds the root Lu to(10). In the two-stack
case the left root scale is the fixed numeral1, so only the right Lu
adds a witness across both trees. All intermediate flags and powers are
included in these counts.

The roots' remaining nine equations still prove their output words and
scales and impose both domain guards. The missing flag equation affects
no ancestor and is unnecessary for(8). It has been removed from the
actual source schedule, not merely from the witness list.

## 6. Cheaper specialization when leaf flags are fixed

If the leaf normal forms are fixed program data, each subtree flag is
the OR of its leaf singleton flags. It can be computed while constructing
the circuit. Let K count the singleton-child edges of a fixed tree:
each merge contributes0,1 or2 according to its two child flags. Then
0<=K<=2m.

At a merge with source-known flags, use the25-gate word/scale schedule
and impose f=0 if its first child is a singleton, and g-f=0 if its
second child is a singleton. These are the exact guards from(6), with
no additional arithmetic gates. Omit the output-flag equation and all
internal flag witnesses; every flag is a source numeral. No test on
an existential value chooses which equations to generate.

The resulting exact schedules are

| Fixed-flag certificate | Graph operations | Positive witnesses | Equations | Single polynomial |
|---|---:|---:|---:|---:|
| Root word/scale relation |25m|8t-12|7m+K|46m+3K-1|
| One ordinary input stack to empty |25m+2|8t-11|7m+K|46m+3K+1|
| Two stacks, left initially empty |50m+2|16t-23|14m+K|92m+3K+1|

In the last row K is the total across both trees, so0<=K<=4m. Its graph
counts are(20m+1)M+(30m+1)A and its polynomial counts are
(34m+K+1)M+(58m+2K)A. The affine loader is included; only the right
root input scale remains an additional witness. The two-stack bound
is at most104m+1 polynomial operations in this schedule, but this is
still a separate circuit for each fixed pair of action words and trees.

The same typing and composition induction proves the specialization.
It is cheaper because the flags are fixed before the arithmetic
instance exists. For variable selected leaves, their flags and the
OR propagation cannot be treated as program numerals without another
paid construction. This specialization supplies no such construction.

## 7. Verification and remaining universal-history work

The [literal checker](typed_prefix_singleton_merge31.py) and
[deterministic receipt](typed_prefix_singleton_merge31.json) cover all
four input-domain combinations and both prefix orientations. Independent
domain-first string composition is compared with the arithmetic source,
including empty tails, boundary codes, input-domain exclusions and
mutations of all five output coordinates. Separate arbitrary positive
assignments audit every residual and the sum-of-squares schedule.

The checker also compares products of push, pop and empty-test actions
with direct stack execution, including underflow and wrong-symbol cases.
Both individually necessary singleton guards and the missing-input-flag
typing counterexample are tested. Left, right and balanced trees share
the actual supplied child outputs with their parent inputs. Internal
flag and word-coordinate mutations are rejected. All generic and
fixed-flag endpoint ledgers are replayed, including wrong ordinary
inputs and a nonempty final word.

Two independent full proof/source/default reviews passed without
findings. One also checked all ten residuals symbolically, both full
and root-omitted sum-of-squares identities, and all eight flag/orientation
cases. The other independently tested10,000 typed input pairs, finding
2,314 positive orientations and7,947 zero products, and checked200 mixed
push/pop/empty-test traces with affine4x+3 loading. Generic and compiled
flag endpoints, wrong-input rejection and all operation counts passed.

This closes two specific representation gaps of cone-only normal forms:
empty reads remain binary, and the typed history root supports a paid
ordinary-input endpoint. It does not select the leaf word, enforce its
finite-control state path, synchronize independently chosen left/right
leaves, or encode an arbitrary number of merge nodes in one fixed
Diophantine equation. Those are the remaining uniform-history costs.
The previous fixed universal interpreter contract is unchanged; no
small universal transition table, new universality theorem, or complete
universal arithmetic improvement is claimed.
