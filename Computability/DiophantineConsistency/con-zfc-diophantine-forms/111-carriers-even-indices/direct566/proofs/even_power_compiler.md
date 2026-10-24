# A quartic compiler using even Pell indices

This is an ordinary, unbounded proof of the source transformation.
The literal transformed rows, complete projections and collected polynomials
are supplied in this packet. Their independently checked metrics are in
`README.md` and `INDEPENDENT_CHECK.json`.

## 0. Scope and fixed input

The frozen starting body is the 1,259-variable, 1,177-row raw body in
`research/factorial-radius-output-sign-profile/raw/parent.json`, at ProveIt
commit `84e16e43092614bae262ca59651cb9d77e31a255`. The source metadata in
`candidates/projected-radius-mixed-bounds/source/raw_builder.json` lists
21 calls `m=n^k`, 15 distinct seed indices, and one derived index `t+1`.
The first 594 rows, using coordinates 0 through 642, are called the
**front**. Its nonnegative semantic coordinates, the source CRT/refutation
calibration, and its ordinary correctness theorem are inherited.

The retained front-domain predicates, with the new remainder-product
batching, imply exactly the old front signs before any power is interpreted.
In particular the factorial sign recovery is the unchanged identity

    f>=2, r>=0, s>=0,
    C=r+s+1, f*C=N+s,
    N=f*r+(f-1)*s+f>=2.

This restores the old initially required sign of N/raw93. The finite
front-prefix sign proof therefore remains available. The batching proof
is separate and uses only unchanged front rows and retained anchor signs.
Neither step uses a Pell index theorem or the intended meaning of a power.

Let the set of distinct front coordinates occurring as a base, an
exponent, or an output be the exact `frame_arguments` list in the frozen
source certificate. Every such coordinate is a nonnegative integer. Every
exponent k is strictly positive by its actual source constructor. Every
base is at least one. All proposed outputs m are nonnegative. In particular,
the base raw112=1+raw107*raw4^2 is allowed to equal one before the second
factorial has been interpreted; its strict increase must not be assumed.

Each seed has a designated supporting call whose base is at least two
before power semantics. The supporting call numbers are

    0,1,5,7,9,10,12,13,14,15,16,17,18,19,20.

Their bases are among raw5, raw92, raw530 and raw531. The first is
t0+2>=2, the second is 1+f*K^2>=3 using f>=2 and K>=1, and the last
two are the positive radix and radix-plus-one. The front inequalities
give raw530>=9, so both are at least two. Only these supporting calls
are used to fix the signs of a seed's main Pell pair.

Only the arithmetic power-certification part changes. The target relation
for each call is now `m^2=n^(2k)`. Because m,n are nonnegative, this is
equivalent to the original equality `m=n^k`.

## 1. Pell notation and elementary facts

For an integer a>=2 put D=a^2-1, alpha=a+sqrt(D), and define

    alpha^j = chi_a(j)+psi_a(j)*sqrt(D),  j>=0.

The pairs start at (1,0), then (a,1), and obey

    chi_a(j+1)=a*chi_a(j)+D*psi_a(j),
    psi_a(j+1)=chi_a(j)+a*psi_a(j).

Thus both coordinates are nonnegative, chi is strictly increasing,
psi is strictly increasing, and psi_a(j)>=j. Every integral solution of
x^2-D*y^2=1 is, up to the independent signs of x and y, one such pair.
This follows by reducing a positive norm-one unit by powers of alpha;
alpha is the smallest nontrivial positive integral norm-one unit because
the smallest possible nonzero positive ordinate is 1, with abscissa a.

The same recurrences define integer polynomials chi_b(j),psi_b(j) for
every signed integer b. Changing b to -b multiplies chi by (-1)^j and
psi by (-1)^(j-1). Consequently, when |b|>=2, every signed Pell solution
can still be written `S=epsilon*chi_b(j), R=delta*psi_b(j)` with independent
signs epsilon,delta in {+1,-1}. Polynomial dependence transfers base
congruences. In particular b==1 modulo M implies psi_b(j)==j modulo M.

Two divisibility/residue facts will be used, with their proofs included.

**Squared-divisibility fact.** If i,h>=1 and psi_a(i)^2 divides psi_a(h),
then psi_a(i) divides h and i<=h.

To prove this, put x=chi_a(i),y=psi_a(i), and write h=qi+r,0<=r<i.
The addition formula, reduced modulo y, gives

    psi_a(h)==x^q psi_a(r) (mod y).

The norm gives gcd(x,y)=1, and 0<=psi_a(r)<y, so r=0. Expansion of
`(x+y*sqrt(D))^q` then gives

    psi_a(qi)==q*x^(q-1)*y (mod y^2).

Hence y divides q, so y divides h. Monotonicity gives i<=h.

**Abscissa residue fact.** For 1<=i<=h, if

    chi_a(j)==+/-chi_a(i) (mod chi_a(h)),

then j==+/-i modulo 2h.

Indeed, writing u=chi_a(h),v=psi_a(h), the doubling formula gives
`alpha^(2h)==-1` in the quadratic ring modulo u. Reduce j modulo 2h and
reflect about h to obtain a residue +/-chi_a(r),0<=r<=h, with
r==+/-j modulo 2h. If i=h, only r=h has residue zero. If i<h, then

    2*chi_a(h-1)<chi_a(h).

The last inequality follows from the recurrence and a>=2. Thus two
coordinates indexed below h cannot sum to u. Congruence up to sign
forces chi_a(r)=chi_a(i), hence r=i. This proves the fact, including
the endpoint i=h. Taking i=1 proves the useful special case that
`chi_a(j)==+/-a (mod chi_a(h))` forces j odd.

## 2. The modified common frame

Let O be the set of 21 output coordinates, and let F be the frozen set
of distinct frame-argument coordinates. Define

    W0 = 2 + sum(v in F\O) v + sum(m in O) m^2,
    W = 2 W0.

The raw frame-chain edits implement exactly this expression. A coordinate
that is both an output and some other semantic atom is counted once,
as in the frozen set; squaring it is harmless because v^2>=v for every
nonnegative integer v. Consequently W>=4 and, for every call,

    1<=n<W,  1<=k,  2k<W,  0<=m^2<W.

The unchanged frame norm is

    A^2-W^3(W+2)Z^2=1.                       (F)

The retained base0 modulus guard is `T0>=0`, with exact defining row
`T0=2A*n0-n0^2-1`, where n0=t0+2>=2. This forces A>=2.
Equation (F) now excludes Z=0. Since it is also

    A^2-((W+1)^2-1)(WZ)^2=1,

Pell classification gives A=chi_(W+1)(h), |WZ|=psi_(W+1)(h),h>=1.
Modulo W the recurrences give chi_(W+1)(h)==1 and
psi_(W+1)(h)==h. Thus W divides h, so h>=W. It follows that

    A >= (W+1)^h >= (W+1)^W > W^W > W^2.       (B)

For each base n the unchanged modulus definition gives

    T_n=2An-n^2-1 >= 2A-2 > A.

Here n lies in [1,W-1] and W<A, and the displayed quadratic is increasing
on that interval. The stronger A>W^W will also control the inverse-residue
sign cases below. No index sign has been used to obtain these bounds.

## 3. All seed-index bounds follow from parity

The 15 seed families retain their equations, but their R congruence uses
K=2k:

    X^2-(A^2-1)Y^2=1,
    S^2-(B^2-1)R^2=1,
    S==X (mod U),  R==K (mod 4Y).             (I)

The unchanged shared equations are

    U^2-(A^2-1)V^2=1,
    V=(product over seeds Y^2)*(v+1),
    B=1+4V(q+1),  B==A (mod U),  V>=1.       (C)

The product identity and V>=1 immediately imply that every Y is nonzero,
every Y^2 divides V, and v+1>=1. They do not require any seed-index guard.
The common norm gives |U|=chi_A(h),V=psi_A(h) for some h>=1.
The integer B is odd. It cannot be +/-1: for h=1, |U|=A does not divide
A+/-1; for h>=2, |U|>=2A^2-1>A+1. Thus |B|>=3.

Suppose |Y|=1. The main norm gives X=+/-A. Classifying the auxiliary
norm gives S=epsilon*chi_B(j),R=delta*psi_B(j). Since B==A modulo U,
the congruence S==X gives chi_A(j)==+/-A modulo chi_A(h). The residue
fact in Section 1 forces j odd. As B is odd, psi_B(j)==j modulo 2, so
R is odd. But R==K modulo 4Y and K=2k is even. This is impossible.

Therefore |Y|>=2. Its main Pell index is at least two, whence

    |Y| >= psi_A(2)=2A > K.                  (L)

This proves every required lower bound without any index-slack predicate.

For completeness of the logic, Y=0 could also be excluded without the
product implementation. In that case R=K exactly. Every nonzero B==A
modulo U has |B|>=A, by the same size argument above. The even positive
K cannot be a Pell ordinate of index 0 or 1, so K=|R|>=2|B|>=2A,
contradicting K<W<A.

## 4. Exact identification with arbitrary signs

We give the signed index argument explicitly, including negative B.
Classify

    |X|=chi_A(i), |Y|=psi_A(i),
    |U|=chi_A(h), V=psi_A(h),
    S=epsilon*chi_B(j), R=delta*psi_B(j).

Here i,h>=1. Since Y^2 divides V, the squared-divisibility fact gives
i<=h and |Y| divides h. The S congruence and base transfer give

    chi_A(j)==+/-chi_A(i) (mod chi_A(h)),

so j==+/-i modulo 2h. The construction B=1+4V(q+1) and Y^2|V give
B==1 modulo 4|Y|, even if B is negative. Polynomial base-one reduction
therefore gives psi_B(j)==j modulo 4|Y|. The R congruence yields
j==+/-K modulo 4|Y|. Since |Y| divides h, these combine to give

    i==+/-K (mod 2|Y|).

We have 1<=i<=|Y| and, by (L),1<=K<|Y|. The plus congruence forces
i=K. In the minus case, 0<i+K<2|Y|, impossible for a multiple of 2|Y|.
Thus i=K=2k. Consequently

    |X|=chi_A(2k), |Y|=psi_A(2k).             (D)

No sign of U,B,S,R,X,Y was silently assumed in this deduction.

## 5. Squared output and main-coordinate signs

First consider a designated supporting call, so n>=2. For its exponent
k and nonnegative output m, the modified
power row is

    X+nY=AY+m^2+T_n*q.                       (P)

Write e=2k, N=n^e and M=m^2. From the frame, n,e,M<W. In particular
N<W^(W-1), and M*N<W^W<A. Let x=chi_A(e), y=psi_A(e), and set

    H=x-(A-n)y, J=x+(A-n)y.

The Pell recurrence gives

    H==n^e=N (mod T_n),
    H*J=1+T_n*y^2, so N*J==1 (mod T_n).

There are four possibilities for the signs of X,Y in (D):

* X=x,Y=y: equation (P) gives M==N modulo T_n.
* X=-x,Y=-y: it gives T_n|(M+N).
* X=x,Y=-y: it gives T_n|(M*N-1).
* X=-x,Y=y: it gives T_n|(M*N+1).

The second case is impossible: as W>=4,

    0<M+N<W+W^(W-1)<W^W<A<T_n.

The fourth is
impossible because 0<M*N+1<=A<T_n. In the third, |M*N-1|<T_n and
the value cannot be zero: n>=2 and e>=2 make N>=4, whereas M is a
nonnegative integer. Thus the third case is impossible as well.
Only X=x,Y=y remains. Both 0<=M<T_n and 0<N<A<T_n, so the first
congruence gives M=N exactly. Nonnegativity then gives

    m=n^k.

Applying this argument to the fifteen supporting calls orients every
actual seed pair positively. No factorial or binomial semantic theorem
was needed to orient the seed that certifies it.

For every remaining call with a seed pair, its base n>=1 is now sufficient.
The pair has positive signs, so (P) gives M==n^(2k) modulo T_n directly.
The frame bounds put both nonnegative integers in [0,T_n); they are
equal, and m=n^k follows. This includes n=1 and m=1. The derived pair is
handled just below, after the source seed has been oriented. Thus every
one of the 21 powers is interpreted without assuming that a base which
is initially only positive already has its eventual factorial value.

### The derived `(t+1)` pair requires two steps

There is one derived pair: call 11 uses exponent t+1, where t=raw4 and
t+1=raw5. The frozen pair was obtained by one Pell step from the t seed.
After doubling, its seed has index 2t, so the derived pair must take
**two** steps to reach 2(t+1). This is a necessary change.

With raw919=A*X, raw920=(A^2-1)*Y and raw650=A^2, change the two old
definitions to

    Xplus2 = 2A*(raw919+raw920)-X,
    Yplus2 = 2*raw919+2*raw650*Y-Y.

Both are quadratic in the actual stored coordinates. The identities
`chi_A(j+2)=2A*chi_A(j+1)-chi_A(j)` and the analogous identity for psi
prove that the resulting pair is exactly the positive pair at 2(t+1).
The seed at t is positively oriented by call 0, whose base is t+1>=2,
before this derived call is used. The squared-output argument then applies
to the derived call as well.

## 6. Simultaneous completeness with fresh auxiliary witnesses

Start with front arithmetic data satisfying all 21 true equalities m=n^k.
Such front data are supplied by the frozen source's soundness/completeness
interface. No consistency assumption is made: this is a conditional map
from any given finite front witness.

1. Compute W0 and W=2W0 from the fixed finite front data. Set
   A=chi_(W+1)(W) and Z=psi_(W+1)(W)/W. The recurrence modulo W proves
   that Z is a positive integer. This gives the exact frame norm (F),
   its exponential bound, and positive T_n for every base.
2. For each distinct seed exponent k choose the positive pair
   X=chi_A(2k),Y=psi_A(2k). Define the derived pair by two Pell steps.
   The unused old slack rows `Y=k+slack` can be filled by slack=Y-k;
   these integers are in fact positive, although their guards are gone.
3. Put P=product over the 15 seeds of Y^2, and L=4P. In the finite ring

       (Z/LZ)[s]/(s^2-(A^2-1)),

   the element A+s is a unit with inverse A-s. Its finite multiplicative
   order gives some positive h with `(A+s)^h=1`. Take
   U=chi_A(h),V=psi_A(h). Then U==1 modulo L and V==0 modulo L;
   in particular U is odd, V>0 and P divides V. Set v=V/P-1>=0.
4. Pell's norm gives gcd(U,V)=1; since U is odd, gcd(U,4V)=1.
   Ordinary CRT supplies B==A modulo U and B==1 modulo 4V.
   Raise B by a positive multiple of 4UV until B>A and B>1+4V.
   Then b=(B-A)/U and q=(B-1)/(4V)-1 are nonnegative integers and
   satisfy the exact shared constructors.
5. For each seed choose S=chi_B(2k),R=psi_B(2k). Polynomial dependence
   in the base gives S==X modulo U, and the base-one formula gives
   R==2k modulo 4Y. Monotonicity in the positive base B>A gives S>=X;
   also R>=2k. Thus all progression quotients exist as integers (indeed
   as nonnegative integers). The new even-index equations are satisfied.
6. For each call set

       q_power=sum_(j=0)^(2k-1) n^(2k-1-j)*psi_A(j).

   The exact recurrence identity

       chi_A(e)-(A-n)psi_A(e)-n^e
         = T_n*sum_(j=0)^(e-1) n^(e-1-j)*psi_A(j)

   proves the modified power row, since m^2=n^(2k). Fill all remaining
   gate coordinates by their displayed polynomial definitions.
7. Every retained domain predicate holds. Keep or regenerate its ordinary
   three-square witnesses. The removed index predicates need no witnesses.

The ordering is explicit: front data, then W, then A and the main pairs,
then one common U,V, then B, then every S,R and quotient. There is no
choice of a modulus depending on a later residue that already constrained
the modulus. Shared witnesses work for all 15 seeds at once, because
the finite-ring modulus includes their entire product.

## 7. Both zero-existence maps to the frozen source

For a zero of the new system, Section 0 restores the old front signs.
Sections 2-5 prove all 21 original power equalities at the same front
tuple. To obtain a zero of the frozen old system, retain that front tuple
and build a **fresh old** common frame and synchronized certificates:
use the frozen frame sum, seed indices k rather than 2k, one Pell step
for the derived t+1 pair, and the same finite-ring/CRT construction from
Section 6. Every old index slack is nonnegative because psi_A(k)>=k.
The old guard triples can therefore be supplied by the usual three-square
representation of a nonnegative integer. The original auxiliary tuple is
not claimed to solve the old equations pointwise.

Conversely, any frozen old zero has a front tuple with the true power
equalities, by the inherited ordinary source theorem. Keep that tuple,
apply the construction of Section 6, and supply the retained guards.
This gives a new zero.

Thus the integer-zero **existence** assertions are equivalent. Composing
with the frozen direct C222/front/calculus/refutation calibration gives
the desired equivalence with syntactic ZFC refutability, and hence the
equivalence of nonexistence with Con(ZFC). The new construction uses no
K215 coefficient tuple or Jones universal polynomial. Its inherited
logical source must still be cited explicitly.

## 8. Ordinary formalizability and artifact boundary

Every new argument uses polynomial identities, integer induction,
division with remainder, finite rings, finite group order, ordinary CRT,
and the elementary classification of solutions for discriminant a^2-1.
All are formalizable in ZFC's internal arithmetic. No assertion that ZFC
is sound or consistent was used. This is an ordinary proof of an internal
provable equivalence; it is not a newly emitted Lean theorem or a sealed
object-ZFC proof certificate.

The producer and independent checker must verify the exact 21 squared
output substitutions, all 15 doubled seed congruences, the two-step
derived pair, the exact squared frame identity, the complete retained
domain and both projection maps. Omitting the derived-pair correction
would invalidate the intended compiler transformation. Finite test
success cannot substitute for the unbounded proof above.
