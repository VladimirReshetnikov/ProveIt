# Cofinal Pell majorants in place of an exact exponential
## Independent mathematical audit of the trial source

This note specifies an experimental source mutation of the included
`../../sources/factorial_free/direct/factorial_free_affine/raw_source.json`.
It is retained as an arithmetic research note, not as the selected endpoint
or as a numerical improvement. The new local rows are given explicitly
below. It is an ordinary mathematical
proof, formalizable in ZFC. It is not a new end-to-end Lean/Rocq proof and
does not independently re-prove the inherited C222/ZF/ZFC calibration or
the unchanged signed Pell power compiler.

The new source retains the parent local proof calculus, generalized
binomial CRT compiler, signed square frame, indexed Pell anchor,
normalization of eleven remainder bounds, endpoint equations, and all
power requests except the first exact majorant request. Its final
coefficient-level identity and projection claims require the finite
checker for the actual emitted source.

## 1. The exact new front

Every displayed coordinate below is an unrestricted integer. The retained
horizon row gives t=16+h^2. Put

    d=6(t+1),        a=d+1,
    Y=d(3v+1),      F=Y^2,
    D=d(d+2),       X^2-D F=1,
    s=(5b+1)^2,     y=F s,
    q=4z+1.

The new binomial radius is R=F, instead of the parent's R=F^2. Thus the
semantic digit eventually authenticated is

    B=binom(F+t,t),

and its index congruence is

    C+F+1=B*iota.

Here C is the actual nonnegative CRT row-index representative; the stored
source coordinate is C-1. The remaining major requests include

    N=B^x,          q=(B H)^x,

where H=2 plus the sum of the nine actual CRT representatives. These
exponentiations describe the meanings of retained polynomial graphs, not
operations allowed in the final equation.

The new four quadratic rows, using d as its existing graph coordinate, are

    Y-d-3dv=0,
    F-Y^2=0,
    D-d^2-2d=0,
    X^2-D F-1=0.

The beta square row is s-25b^2-10b-1=0. The radix row is q-4z-1=0.
The definition d=6(t+1) is linear in the retained t0=h^2 coordinate.
The replacement radius row is R-F=0.

## 2. A large-majorant theorem on every integer zero

For integer a>=2, define the Pell sequences by

    X_0=1, Y_0=0,
    X_(n+1)=a X_n+(a^2-1)Y_n,
    Y_(n+1)=X_n+a Y_n.

Every integer solution of X^2-(a^2-1)Y^2=1 has
(|X|,|Y|)=(X_n(a),Y_n(a)) for some n>=0. One elementary proof uses descent:
for a positive solution with Y>0, let

    X'=aX-(a^2-1)Y,       Y'=aY-X.

The norm identity gives (a-1)Y<X<=aY, so 0<=Y'<Y, and X'>0.
Iterating reaches (1,0); reversing the recurrence proves the assertion.
The signs of X and Y need not agree.

In the new graph d>0, and 3v+1 is nonzero for every integer v. Thus Y is
nonzero and F>0. The classification therefore has n>=1. Reduction of the
recurrence modulo d=a-1 gives Y_n(a)=n (mod d). Since d divides |Y|,
d divides n; consequently n>=d.

For n>=1, Y_(n+1)=X_n+aY_n>=aY_n. Hence

    |Y|=Y_n(a)>=a^(n-1)> (t+1)^t,

because a=6(t+1)+1>t+1 and n-1>=d-1>t. It follows that

    F>(t+1)^(2t)>(t!)^2>=lcm(1,...,t)^2.                 (1)

In particular F>2^32, F>t, and F>(t+1)^t. These conclusions precede
all exponentiation, binomial, CRT, or sign interpretations in the inherited
front. They authenticate a sufficiently large F, without authenticating
any particular value of F.

The source needs the two consequences F>(t+1)^t (for polynomial
multiplicity separation) and R=F>=lcm(1,...,t)^2 (for generalized
binomial prime-power CRT). Both follow from (1).

## 3. The retained signed-power interface

The retained signed square frame and full indexed anchor first identify
all requested signed Pell indices. Their ordinary theorem bounds every
actual base, exponent, and output atom in absolute value by W and has
|A|>W^W. Deleting the first output request does not invalidate the frame
or anchor: their equations are retained, and the deleted request's
unconstrained private values play no role in the remaining interfaces.

The inherited exact-power lemma for a signed nonzero base n uses

    T_n=2An-n^2-1.

For |n|>=2, it rules out a negative exponent k: the integer congruence
would become m n^(-k)=1, since its absolute error is smaller than |T_n|.
It then yields k>=0 and m=n^k. For n=1 or -1, it yields the appropriate
unit power. This lemma is applied to the retained requests, not to F.

The application to each numerator request at base q+1 is valid before
knowing the sign of q. Indeed q=4z+1 gives

    q !=0,           |q+1|=|4z+2|>=2.

Consequently every actual CRT representative is nonnegative, and H>=2.
The index row C+F+1=B*iota, with C>=0 and F>0, excludes B=0.
Thus |BH|>=2 and the retained request q=(BH)^x proves

    x>=0,            q=(BH)^x.                         (2)

This signed conclusion does not assume B>0 or q>0.

## 4. Recover x and then the sign of the radix

Since 5b+1 cannot vanish, y=F(5b+1)^2>=F>0. The endpoint equations are

    x=F+1+(y+1)u0,
    x=1+[1+(t+1)y]ut.

The second excludes x=0. If u0<=-1, the first gives x<=F-y<=0, so
u0>=0 and x>=F+1. Then ut>=1 and

    x>=2+(t+1)y>=2+(t+1)F.                             (3)

Put Q=|q|. By (2),

    Q=|BH|^x>=2^x>1,             |B|<Q/2.               (4)

These conclusions suffice to decode the first binomial using a signed
radix. For 0<=j<=t, write c_j=binom(F+t,j). Since F>=t and F>=7,

    c_j <= (F+t)^t <= (F^2+F)^t <= 2^(t(F-1)).

The elementary inequality F(F+1)<=2^(F-1) holds at F=7 and persists
by induction. Equations (3) and (4) show

    max_j c_j/(Q-1)<1/32,       c_t<Q/32.

The actual low part of the binomial expansion, which may have either
sign when q is negative, is

    r_* = sum_(j=0)^(t-1) c_j q^j.

The triangle inequality gives |r_*|<Q^t/32=|q^t|/32.

The unchanged normalized remainder budget is

    M^2=1+4 sum rho_i^2+alpha^2+beta^2+gamma(gamma+1),

with M=q^x. It implies |rho_i|<|M|/2. The unchanged ratio and digit
rows yield an integer r_i with rho_i=(M/D_i)r_i and D_i|M; hence

    |r_i|<|D_i|/2.

All these assertions concern divisibility in Z and are valid for
negative nonzero M or D_i. In particular the first digit row gives
r_i congruent to r_* modulo D_i=q^t. Their difference has absolute
value smaller than |D_i|, so r_i=r_*. The next digit consequently yields

    B = c_t (mod q).

By (4), |B-c_t|<Q/2+Q/32<Q, so B=c_t>0. Equation (2) now gives
q=(BH)^x>0. This order is essential: positivity of q is a conclusion
of binomial authentication, not a premise of the early sign recovery.

From here N=B^x>0, q=B^x H^x, and all remaining radix and prime-power
arguments have exactly their positive meanings.

## 5. The remaining source proof still applies

The generalized binomial CRT theorem needs R>=Lambda_t^2, where
Lambda_t=lcm(1,...,t). Section 2 supplies it for R=F. It does not
need R to equal F^2 or to be a certified factorial square.

The independent-column range powers use N=B^x. Every ordinary
representative is below H, so its relevant binomial coefficients
are at most H^x. The derived label obeys the retained literal
majorant J<=H^ell with ell=2^22; (3) and F>ell imply ell(t+1)<x.
Thus its coefficients have the same bound. Since B>=2,

    H^x/(q-1)<2/2^x<1/32.

The common remainder bounds select all remaining low parts correctly.

The retained local source ledger bounds its nonnegative value L by
R0^E, with R0=2+t+x+y+F and E=2^23. Equations (3), y>=F, and F>t
give R0<2x; x>2^32 gives (2x)^E<2^x. These are the same scalar
bounds used by the parent. Prime-power precision therefore converts
the local congruences into actual local zero equations.

The exceptional case y=F still must be excluded. If y=F, the first
endpoint gives beta remainder zero at the initial modulus y+1.
The decoded local flow identity

    S'_i(1+v_i F)=S_i(1+p_i F)(1+q_i F)

has positive label weights. It propagates a zero accumulator through
every row, whereas the final endpoint has remainder one. Contradiction.
Thus y>F; for the new square progression this even gives y>=16F,
because the only integer b with |5b+1|=1 is b=0, and the next
possible absolute value is four.

Now the initial remainder is F+1, all accumulator values are positive,
and telescoping yields the parent's label-product equality. The
inequality F>(t+1)^t recovers multiplicities, and the
single-conclusion Horn-flow theorem gives a finite C222 refutation.
The named inherited C222/ZF/ZFC interfaces then give a finite
syntactic ZFC refutation.

## 6. Completeness: choose the allowed Pell witnesses in the right order

Start with a finite C222 proof tree. Choose h arbitrarily large with
3 not dividing h, and choose t=16+h^2 beyond its size, labels, schema
parameters, and all padding requirements. This is a cofinal subset of
the parent's allowed horizons. It satisfies

    t=2 (mod 3),        9|d,       d=6(t+1).

No new horizon equation is needed. Its use only restricts the
constructive completeness choice.

Set

    n=d*10^t,          a=d+1,
    Y=Y_n(a)>0,        X=X_n(a),       F=Y^2.

We next verify all congruence and divisibility promises. The powers
in this witness recipe are part of a finite existence construction,
not operations in the final polynomial.

### 6.1 The required ordinate progression

As an integer polynomial in a, Y_n(a) has

    Y_n(1)=n,         Y'_n(1)=n(n^2-1)/3.

Both identities follow from Y_0=0, Y_1=1,
Y_(n+2)=2aY_(n+1)-Y_n; differentiation gives the cubic formula.
Taylor expansion over Z therefore has an integer remainder Z_n with

    Y_n(1+d)=n+d*n(n^2-1)/3+d^2 Z_n.

Since 9|n and 3|d, the last two terms are divisible by 3d. Hence

    Y_n(a)=n (mod 3d),
    Y_n(a)/d = n/d = 10^t = 1 (mod 3).

Thus v=(Y/d-1)/3 is an integer. All four new Pell rows hold.

The restriction 3 not dividing h is material. It is NOT true for all
allowed horizons that Y_(d*10^t)(d+1)/d is 1 modulo 3. At t=16,
d=102, the quotient is 0 modulo 3. The finite test supplied with this
note retains that rejected shortcut as a regression control.

### 6.2 Enough powers of two

The integer a is odd. The recurrences give X_m(a) odd and
Y_m(a)=m (mod 2). Doubling gives

    Y_(2m)(a)=2 X_m(a)Y_m(a),

so v_2(Y_m(a))=v_2(m) for every m>=1. In particular

    v_2(Y)>=t+1,        v_2(F)>=2t+2.

Since R=F, v_2(R)>floor(log_2 t). For 1<=i<=t this implies
v_2(R+i)=v_2(i). The numerator and denominator valuations cancel in
B=binom(R+t,t), so B is odd.

### 6.3 Enough powers of five

The Pell matrix

    M = [[a,a^2-1],[1,a]]

has determinant one. The finite group SL_2(F_5) has 120 elements:
there are 24 nonzero first columns and five second columns of
determinant one for each. Hence M^120=I modulo 5. Repeated matrix
binomial expansion gives

    M^(120*5^(t-1))=I modulo 5^t.

This exponent divides n=d*10^t, since their quotient is

    (t+1)*2^(t-2).

Thus 5^t divides Y, and 5^(2t) divides F. In particular F supplies
the entire 5-primary part of t!.

### 6.4 The beta square and all remaining witnesses

Let O be the largest divisor of t! not divisible by five. By CRT,
there are arbitrarily large positive integers u with

    O|u,             u=1 (mod 5).

Take b=(u-1)/5 and y=F u^2. Then t!|y, y is even, and y can
exceed every pending-multiset accumulator and F+1. The moduli
1+(i+1)y, 0<=i<=t, are pairwise coprime: a shared prime divides
an index difference and hence t!, contradicting coprimality with y.

CRT now supplies the desired state residues. All moduli are odd, so
x may be chosen even, positive, and arbitrarily large. In particular
the endpoint quotients are nonnegative, and all row quotients satisfy
the unchanged local ranges.

Now compute R=F, B=binom(R+t,t), and N=B^x. The generalized binomial
CRT completeness theorem selects all row representatives. As B and N
are odd, their required parity choices remain available: choose the
dominant representative odd and the others even, ensuring H odd and
the even semantic anchor as in the parent. The local constraints
and dominant representative lift are otherwise unchanged.

Set q=(BH)^x. It is a positive odd square, so q=1 (mod 4) and
z=(q-1)/4 is an integer. All common-root, normalized remainder, and
signed Pell frame witnesses can now be chosen by the retained
completeness constructions. The choices are acyclic:

    proof -> cofinal t -> Pell X,Y,F -> pending states -> beta y,x
          -> binomial B,N -> CRT representatives -> H,q
          -> remaining power outputs and Pell frame witnesses.

The first exact-power request F=[2(t+1)]^t is not reconstructed.
It has been replaced semantically by a sufficient cofinal family,
not eliminated by a bijection of its old zero set.

## 7. Scope of the result

Combining Sections 2--5 with Section 6 proves that the modified raw
source has an integer zero if and only if the calibrated numerical
calculus has a finite refutation. Certified integral projections,
Horn private-witness exchanges, coordinate translations, and
invertible residual-row operations preserve the existence of zeros.

Accordingly any final emitted quartic obtained from this exact
modified source by independently certified transformations has
nonsolvability ZFC-provably equivalent to Con(ZFC), relative to the
same explicitly named inherited logical and arithmetic dependencies.

The advance is the removal of one exact power request by a cofinal
Pell majorant, together with its compatible beta progression and
linear binomial radius. It is not an assertion of a minimum among
all Diophantine equations, nor an equation proving consistency.

