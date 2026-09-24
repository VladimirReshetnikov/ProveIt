# One shared native offset for all twelve fields: 110 operations

The 114-operation intrinsic-width construction represents twelve Boolean
words by adding J=(q-1)/2 to each. Reparameterize those words directly
as positive raw integers and apply the native offset once to their whole
packing. Seven additions disappear and three are introduced, giving the
complete count **110 operations, 55 products and 55 additions/subtractions**,
with **39 positive unknowns and 27 equations**. Independent source/proof
reviews and full fresh verification pass. The universal frontier
remains 90.

The source/checker is `../verification/explore_global_native_offset.py`.
The fixed program, intrinsic forbidden mask Zstar and full positive
kernel come from `EXPLORATION_INTRINSIC_PROGRAM_WIDTH.md`. A minor fixed
prefix annotation ensures at least one true zero request on every
compiled accepting path; it adds no arithmetic operation.
The separate proof and executable compiler adapter are in
`EXPLORATION_GLOBAL_OFFSET_POSITIVITY.md` and
`../verification/explore_global_offset_positivity.py/.json`.

## 1. Source equations and exact count

The positive outer variables are

    q,J,W,H,v,T,A0,A1,B0,B1,Kp,Km,Z,D,alphaI,R,
    C,V,TC,TV,beta,Jwide.

Retain the same seventeen positive kernel variables, including r.
The raw packed word and evaluated power are

    Praw=Kp+q B0+q^2 A0+q^3 B1+q^4 A1+q^5 Km
        +q^6 Z+q^7 D+q^8 C+q^9 V+q^10 TC+q^11 TV,
    L=q^12.

The outer equations are

    q=2J+1, q=Wv, W=R^3, H(R-1)=2J,
    Kp+Km=H, Z+D=H,
    6(J-T)=(R-3)D,
    B0=A0+T, B1=A1+T,
    W(A0+A1+Kp-Km)=A0+A1-2x,
    2x+alphaI=R,
    C+J=SH+TC, TV=V+Zstar H,
    (RK-g)C=(gI)(2J)+R(V+hs Kp+hz D),
    2Jwide+1=L, r=Praw+Jwide, r+beta=L.            (1)

The ten full fixed-sign kernel equations are unchanged, with D0=L.
All displayed abbreviations used by the certificate are evaluated by
the checker using ordinary binary additions and multiplications.
In particular q^12 uses the same four-product addition chain.

Compared with 114, remove these seven additions:

* The head target 2J+H: the two raw flag pairs now compare to H.
* Extracting A from F0+F1 by subtracting 2J.
* Extracting the raw complementary zero word from its native field.
* Extracting the raw positive-sign word from its native field.
* The three exclusive native program adapters for V,TC,TV.

The expression C+J remains necessary for its support equality and is
not counted as a deleted adapter. The twelve-field Horner packing has
the same 22 operations. Add exactly three additions: Jwide+Jwide,
then +1, and Praw+Jwide. Thus 114-7+3=110. Removing the four supplied
native program coordinates and adding Jwide gives 39 unknowns;
removing their four comparisons and adding the wide-offset geometry
gives 27 equations.

## 2. The wide offset has exactly the required value

The two geometries q=2J+1 and 2Jwide+1=q^12 imply, over integers,

    Jwide=J(1+q+...+q^11).                        (2)

Consequently the mathematical packed integer Praw+Jwide equals the
old twelve-field packing with fields J plus each raw word. This is
an algebraic identity, not twelve uncharged adapter evaluations.
The implemented schedule evaluates the left expression directly.

All raw fields are supplied positive. Since r=Praw+Jwide and
r+beta=q^12 with beta>0,

    0<Praw<=Jwide, q^11<Praw<r<q^12.

Because Jwide=J q^11 plus a strictly smaller nonnegative remainder,
the top raw field satisfies TV<=J. The source TV=V+Zstar H and V>0
therefore gives R-1=2J/H>2Zstar. Exactly the intrinsic-width choice
of Zstar provides R>=9, q>=R^3>=729, H<=J/4 and every required
fixed-ROM row bound. These facts precede the kernel and all digit
interpretations.

## 3. Strong raw bounds before the kernel

Positivity and the raw flag pairs give

    0<Kp,Km,Z,D<H.

Since D>0 and R>3, the top source gives 0<T<J. Write
A=A0+A1>0 and delta=Kp-Km>-H. The exact time equation gives

    A<WH/(W-1)<J.

Thus A0,A1<J and B0,B1<2J<q. All eight raw counter/zero fields
are already positive and below q, without a Boolean assumption.
Also V<TV<=J. For the routing expression,

    0<O=V+hs Kp+hz D<V+Zstar H=TV<=J<q.

The fixed bounds K>=3, gI<R and g<R imply RK-g>gI+R, so the
cyclic route yields C<q, again before any source support or Booleanity
is used. Finally TC=C+J-SH<q+J; its tighter bound is deferred.

The positive packed word satisfies every kernel hypothesis:
D0=q^12>=81, r>=27, r<D0<2D0 and D0<r^2, the last from r>q^11.
The full 43-operation kernel therefore recovers q as a power of three
and v3(binomial(2r,r))>=log_3(D0).

## 4. Decode the raw packing and its last possible carry

Since r<D0, the direct native-mask theorem says that all ternary
digits of r are 1 or 2 and its unit digit is 2. Jwide is precisely
the length-log_3(D0) all-one ternary word. Subtracting it from r
has no borrow, so Praw is Boolean ternary with unit digit one.

All the first ten supplied raw fields, through V, were already below
q. Thus they equal their base-q chunks and are Boolean; there is no
incoming carry into TC. In particular C<=J. The support identity
now sharpens its bound to

    TC=C+J-SH<2J<q.

Thus TC also equals its Boolean chunk, has no outgoing carry, and
TV<=J is its Boolean chunk as well. All twelve supplied raw words
are recovered. No untyped-program carry assumption was used to
deduce C<=J.

The two Boolean flag pairs sum to the head mask H with no ternary
carry, and hence are complementary head subsets. The top equation
gives T=(R/3)H+((R-3)/6)Z. Since the raw Boolean guards obey
B_i=A_i+T, their supports are disjoint and the numerical tracks
have zero top bits, vanishing at every requested zero event.
The ordinary numerical counter transport, complete even banks,
one-state ROM marker, allowed edges and both label projections
now have exactly the intrinsic-width predecessor's interpretations.
The unit of Praw forces the first sign plus. Cyclic entry retains
the same first-return raw-input acceptance contract.

## 5. Strict positivity of all twelve raw fields

This reparameterization must respect the strictly positive supplied
variable convention. It is not justified just because Boolean words
are nonnegative. The following facts supply positivity in every
compiled accepting history.

Kp is nonzero because the first sign is plus. Km is nonzero because
the last active source value is one and its update is minus. That
last source cannot request zero, so the complementary word D is
nonzero. The first physical counter starts at 2x>=2 and reaches
zero by unit changes. It therefore has a source value exactly 2
at some step. In a sum of two Boolean ternary tracks representing
this value, its unit digit two forces a unit one in both tracks;
there is no ternary carry because two Boolean digits sum to at
most two. Hence A0,A1>0, and B0,B1=A0,A1+T>0.

For Z, mark the second lane of the initial all-plus prefix with a
true zero request. Its active counter is initially zero, so the
test always holds. This vertex is otherwise unique to the prefix;
later cyclic traversals also reach it from zero counters after
accepting cleanup. The extra test therefore preserves every old
accepting run and cannot add an accepting run. The fixed graph is
then compiled normally with this annotation, including its
complementary ROM label and high forbidden digit. Thus Z>0.

C is positive because the path has a state at every row. V retains
the positive count-marker junk. TC=C+J-SH>0 by R>2S+1. TV is
positive by its definition. All remaining outer and kernel
coordinates have the same positive constructions as before.

## 6. Converse, parity and universal quantifiers

For any recursively enumerable set of positive integers, take its
fixed three-counter compiler, add the valid prefix annotation, and
use its cyclic entry. Choose a sufficiently large power-of-three
radix, as permitted by the intrinsic-width converse. Construct its
positive raw tracks, flags and program words as above, and set
Jwide=(q^12-1)/2 and r=Praw+Jwide. Each raw field is Boolean,
so r has all twelve native chunks and r<q^12. Put beta=q^12-r>0.

The canonical duration remains a multiple of six. The corresponding
native packed integer is exactly the predecessor's mathematical
packing, so its unit digit is two and its parity is even. Equivalently,
the flag pairs contribute even H, the two track/guard pairs have
even sum, and the four native program fields have the established
even sum 2(C+V)+5J+(Zstar-S)H. The full fixed-sign positive converse
constructs every remaining Pell coordinate.

The program annotation and all fixed numeral choices depend only
on the simulated set, never on x. Thus the construction has the full
ordinary-input universal interface. Independent full proof/source
reviews and fresh checks pass. The existing
90-operation universal family remains smaller.

## 7. Exact evidence and positivity coverage

The full source checker verifies all 110 instructions and 27 source
comparisons, including the exact wide-offset residual identity and
the unchanged auxiliary-norm correction. Forty-two integer offset
checks include non-power q, and 1,022 Boolean words check the native
offset through nine ternary positions.

Both full canonical histories are checked afresh at width 1,508
ternary digits. Each has twelve strictly positive raw fields and
satisfies all seventeen outer source comparisons. Their packed sizes
are 344,178 and 516,267 bits, with valuations 217,152 and 325,728.
All positivity, parity and kernel bounds are checked; enormous Pell
coordinates are supplied by the full positive converse.

The separate positivity regression checks 1,714 complete unit walks
and 5,142 digit splits. Its marked compiler preserves the prefix on
101 inputs, including an all-zero restart, and follows all 31 sample
machine executions through 1,307,856 serial blocks and 1,514 source
zero tests. The 16 accepting runs all have the required positive raw
fields and admit the marked prefix after cleanup. These finite checks
support the arbitrary-walk and first-return proofs; they do not
replace the universal quantifier argument.
