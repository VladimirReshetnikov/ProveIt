# Independent audit of the 26-integer extension

Audit scope: the robust-weight extension of the twelve-variable quadratic
norm, its signed-domain boundary cases, rational and integral root recovery,
and the exact substituted arithmetic circuit. This note does not replace
the inherited signed Pell/rank or blank compiler proofs.

## Result

The new reduction is mathematically valid under the stated inherited
blank-compiler and signed-rank interface. In particular, the T=0 branch is
handled without presuming that the eliminated strong root f is rational.
No mathematical defect was found in the signed weighted-sum construction.

The guarded coordinates are J,F,alpha,z,i,eta,zeta>0. The free coordinates
are h,T,t,s_integer,w_integer, with s=2*s_integer+1 and w=w_integer^2.
Replacing each guarded coordinate by 1+u^2+v^2+r(r+1) gives exactly
7*3+5=26 unrestricted integer unknowns. This surjection is onto the positive
integers by the classical three-square theorem.

## 1. Bounds before reconstructing any root

Weak transport still proves Cword>=0 when w>=0, including w=0. If Cword<0,
then Nt< -1 because kappa>=2, z>=1, and F>=1; thus it cannot be a unit.
The usual fixed mask bounds then give 0<R<q^4, independently of the signs
of h and s. Because s is odd, |Y|>=q^3 and

    |a|=(X+1)|Y|>=q^3,  c!=0,  sign(c)=sign(a),  |H|>1.

Even before proving X>0,

    Delta=a^2+4a+3 >= q^6-4q^3+3 > q^4 > R.

The last strict bound holds for q>=16. Therefore D=1+Delta H^2 i^2 c^4
is much larger than |c|, and

    b=c+R D >1,
    Q-b=(Delta-R)D-Delta-c >1.

In particular 1<b<Q-1. These inequalities do not use either the main norm
or the positivity of s. That is essential to the zero-T exclusion.

## 2. Robust separating weights

Write

    Wbound=(T^2+1)(a^2+5)H^2 i c^4,
    M=1+2(Wbound+b),
    N=1+H^2 M(A+1).

Both are positive. Since |c|>=1 and i>=1,

    sqrt(D)<(|a|+3)|H|i c^2,
    |v|sqrt(D)<Wbound.

The second bound follows from |T|<=T^2+1, |a|+3<=a^2+5,
|H|<=H^2, and |c|^3<=c^4. For every complex branch of the auxiliary
root, the same triangle-inequality argument as in the positive theorem
gives |y|<2(|v|sqrt(D)+b)<M.

Here A=1+L(L+k)>=1 because L=kXY^2>=0. Thus M sqrt(A)>|y|. Also

    N sqrt(S)/|H|
      > |H|M(A+1)sqrt(S)
      >= M(A+1) >= 2M sqrt(A)
      > M sqrt(A)+|y|.

Consequently the value t=y+M tau+N gamma separates the triples
(gamma,tau,y) on the algebraic solution set. It need not separate f when
T=0, and the proof correctly refrains from claiming that it does.

## 3. Rationality and denominators: the exceptional branch

The norm factorization provides an algebraic solution tuple with the
specified integer t. Galois conjugation and triple separation imply that
gamma,tau,y are rational. The square equations make tau and P+H gamma
integers, so the reduced denominator of gamma divides |H|.

The delivered proof uses the quartic directly:

    d^2*y^4-2*d*e*y^2+e^2-Baux^2*D=0.

Write y=r/s in lowest terms. For every prime dividing s, multiplication
by s^4 and reduction modulo that prime show that it divides d. On the
other hand y=t-M tau-N gamma has denominator dividing H. Since Q is
divisible by H^2, gcd(H,d)=1. Thus s=1. Since N=1 modulo H, the integral
relation N gamma+y=t-M tau now makes gamma integral too. This proves
integrality without splitting on T or presuming anything about f.

If T=0, the auxiliary equation becomes

    Q b^2-(Q-1)y^2=1.

Since 1<b<Q and y is integral, this is impossible: rearrangement gives

    d(y^2-b^2)=b^2-1>0.

Thus |y|>=b+1, whereas d>=b forces

    d(y^2-b^2)>=d(2b+1)>=b(2b+1)>b^2-1.

This contradiction excludes T=0. Then Baux=2Qvb is nonzero, and
f=(e-d*y^2)/Baux is rational. Its square equals the integer D, so it is
integral. No unproved assertion of its rationality was needed in the
exceptional branch.

## 4. Returning to the signed parent theorem

Now all four eliminated roots have been restored as integers. The main
equation excludes X=0: modulo H, its left-hand norm would be zero, while
the norm equals one and |H|>1.

The negative-s exclusion in ODD_SCALE_27_PROOF.md applies with the
normalized multiplier H*i. Its soundness proof uses only nonzeroness of
that multiplier, not oddness. In the normalized strong-index argument,

    psi(m)=|H*i|*c0^2

still gives p*c0 dividing m and m>2p. The subsequent rank and main-root
congruence arguments are unchanged. Thus s>0, and the reconstructed
solution lies in the established signed blank-machine domain.

Completeness combines three independent choices already justified:
canonical odd s, canonical square w, and the strong Pell index divisible
enough that psi(m)/(Hc^2) is a positive integer. The latter can be enforced
by the finite matrix-period construction without changing s or w. No
oddness claim for this new quotient i is used. Seven positive surjections
then supply integer preimages. This avoids the obstruction that would
arise from imposing odd i at the same time as the new H-divisibility.

## 5. Circuit and degree audit

The explicit polynomial circuit was inspected gate by gate against the
two quadratic norms, and the seven positive substitutions, odd s, and
square w were checked. A separate implementation multiplied generic
elements of Z[r,u]/(r^2-A,u^2-S) and applied conjugation twice. It did not
copy the scalar f0,f1,f2,f3 formulas from the builder.

All 27 exact cases passed, including every combination of T=0, X=0,
negative s, and nonzero alternatives. The same cases checked the signed
radicand, b/Q, denominator, and separating-weight bounds. Details and the
exact audited polynomial SHA-256 are in INTEGER26_INDEPENDENT_CHECKS.json.
The finite checks supplement the general proof; they are not K215 witnesses.

The weighted degrees, after the seven positive substitutions, are

    c:9, H,a:11, Delta:22, A,S:40, G:31, D:84,
    Q,d:106, b:92, M:92, N:154.

The two main gamma roots have orders 9 and -2 under a common scaling of
all integer unknowns. Their N-weighted orders are 163 and 152, both
strictly greater than the orders 112 of M tau and 92 of y. Thus the norm's
leading homogeneous form is

    d_top^8 N_top^16 (P^2-S)_top^8
      =d_top^8 N_top^16 (H_top c_top^2)^8,

with exact degree 8*106+16*154+8*29=3544. Multiplication by Nk and Nt,
of degrees 12 and 4, gives exact degree 3560. No cancellation is possible
in these displayed nonzero products. The builder's modular specialization
independently attains these degrees and this leading coefficient.

The audited single equation uses 199 operations, split into 120
multiplications and 79 additions/subtractions. The comparison system uses
195 operations, while explicitly subtracting one from Nk and Nt gives
197. The sum of squares uses 202 operations and has degree 7088.

## Status

The new arithmetic and domain reduction have independent mathematical
and finite-computation review. The full compiler, signed rank lemmas,
machine endpoint, and the new proof are not claimed to have been freshly
compiled in Lean or Rocq during this audit. No claim of global minimality
or a proof of Con(ZFC) is made.
