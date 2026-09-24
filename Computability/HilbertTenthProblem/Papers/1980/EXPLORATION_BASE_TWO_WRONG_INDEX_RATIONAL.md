# A rational-root wrong-index family for the base-two Pell subsystem

The first/main Pell equations and first exponent congruence do not,
by themselves, force the main Pell index to be J=2r+1. This note
constructs an exact positive family with main index J-2 after the
relaxed and half-parameter auxiliary block is omitted.

This is a subsystem result. The family cannot satisfy the current
full packed-r equation with power-of-two n=q^8, for the explicit
modulo-three reason in Section 6. Thus it is not a counterexample
to deleting that auxiliary block from the complete universal system,
and it establishes no improved operation count.

## 1. The corrected rational root

Let h>=2 be an integer and define

    p=6h+1, t=3h+2, r=t-1=3h+1, J=2r+1=p+2,
    U=2^p,
    F=(U+1)^(2h)/(U^h*2^(2h+1)), Y=floor(F).

Expanding F in powers of U gives the exact integer part

    Y=sum_(j=h+1)^(2h) binom(2h,j)*U^(j-h)/2^(2h+1). (1)

Each summand in (1) is an integer divisible by 2^(4h), since
U/2^(2h+1)=2^(4h). In particular,

    Y>=2^(4h), 2^(4h) divides Y.                 (2)

To justify (1), write F=Y+f with the proposed integer sum. The
remaining terms are positive and consist of the central term
binom(2h,h)/2^(2h+1) and the terms with negative powers of U.
The ratios binom(2h,h)/4^h decrease with h, and at h=2 equal 3/8.
The negative-power tail is smaller than

    (1/U)*2^(2h-1)/2^(2h+1)=1/(4U).

Consequently

    0<f<3/16+1/(4U)<1/5.                       (3)

Thus f<1 and the integer sum is indeed floor(F).

The uncorrected choice Y=2^((p-4)(p+1)/6) would omit the factor
(1+1/U) in a=Y(U+1). It fails the strict interval by a large
absolute amount. The rational root above retains that factor exactly.

## 2. Exact leading ratio and strict interval

Set

    a=Y(U+1), A=a+2, D=A^2-1,
    E=UY, P=2UY^2+1,
    c=psi_A(p), d=chi_A(p), k=psi_P(t).

The leading ratio is exactly

    R0=(2a)^(p-1)/(4UY^2)^(t-1)=F^3/Y^2.       (4)

The last identity uses U=2^(6h+1). From F=Y+f, (2), and (3),

    R0-Y=3f+3f^2/Y+f^3/Y^2
          <3/5+3/50+1/500=331/500<2/3.

In particular Y<R0<Y+2/3.

For a Pell base z>=2 and integer index m>=2, the elementary recurrence
gives (2z-1)^(m-1)<=psi_z(m)<=(2z)^(m-1), with strict inequalities
where needed here. Applying those bounds gives

    c/k >= R0*(1+3/(2a))^(6h)
                   /(1+1/(2UY^2))^(3h+1) > R0. (5)

Indeed 6h>=3h+1 and 3/(2a)>1/(2UY^2). Thus c/k>Y.

For the upper bound, 2P-1>4UY^2 gives

    c/k < R0*(1+2/a)^(6h).

Here a>24h, so the elementary estimate
(1+z)^m<=1/(1-mz)<1+2mz for 0<mz<1/2 yields

    c/k < R0*(1+24h/a)
        < R0+48h/(U+1) < Y+1.                (6)

The second inequality uses R0<Y+2/3<2Y. The final one follows from
U+1>144h. Both a>24h and U+1>144h hold for h=2 and persist as h
increases, since U grows by a factor 64 at each step.

Equations (5)--(6) prove the required strict interval

    Y<c/k<Y+1.                                (7)

Therefore eta=c-Yk and zeta=(Y+1)k-c are strictly positive integers,
with c=Yk+eta and k=eta+zeta.

## 3. First norm and positive index quotient

The first Pell identity gives

    chi_P(t)^2-(P^2-1)k^2=1.

P is odd, so chi_P(t) is odd. Thus

    tau=(chi_P(t)-1)/2

is a positive integer, and the exact first source norm is

    tau(tau+1)=(E^2+U)(Yk)^2.

Since P=1 modulo E, the recurrence for psi gives k=t modulo E.
Strict Pell growth gives k>t. Hence

    h_index=(k-t)/E>0

is integral and k=r+1+h_index E. The parameter h of this family
and the supplied first-index quotient h_index are different integers.

The main norm is exact by construction:

    d^2=1+D c^2.

Its index is p=J-2, strictly different from the index J=2r+1 that
the omitted auxiliary block is used to prove.

## 4. First exponent congruence and its positive quotient

For M=4a+3=4A-5, put

    H_m=chi_A(m)-(A-2)psi_A(m).

This sequence has H_0=1,H_1=2 and the Pell recurrence. The sequence
2^m satisfies that same recurrence modulo M, because

    2A*2^(m+1)-2^m-2^(m+2)=2^m(4A-5).

Therefore H_p=2^p=U modulo M, so

    gamma=(d-U-a c)/(4a+3)

is integral. Its positivity is strict:

    d-a c=2c-psi_A(p-1)>c>U.

The last inequality follows from p>=13 and A=Y(U+1)+2>U.
Consequently the retained source equality

    d=U+a c+gamma(4a+3)

has a positive quotient. It correctly encodes U=2^p; without the
auxiliary index argument, it does not identify p with J.

## 5. Positive scaling variables and size ranges

For any power n=2^j with 1<=j<=2h, (2) and U=2^(6h+1) give

    w=U/n^2>0, s=Y/n^2>0

as integers. Thus the source scalings U=wn^2,Y=sn^2 hold. All
first/main source witnesses discussed above are strictly positive.

If only the usual pre-exponent ranges n<=r<2n^3 are desired, one
may choose n as the largest power of two not exceeding r. Then
n<=r<2n, j<=2h, a>n^4, and E>r+1. These simple size estimates
already coexist with the wrong index. The finite regression includes
such choices with n>=64 at h=21 and h=31.

The stronger packing range n^2-1<=r<2n^3 can also coexist with this
Pell family in the absence of the actual packed-r equality. For a
fixed power of two n>=4, choose h satisfying

    n^2-1<=3h+1<2n^3, log2(n)<=2h.

This interval contains integers, and all the preceding constructions
apply. This observation is still only a size-range statement; it
does not assert the existence of compatible encoded S,Tplus.

No second fixed-index equation, admissible code, product code bound,
or relaxed/half-parameter auxiliary norm has been asserted here.

## 6. Why the family cannot satisfy the current full packing

In the full construction, q is a power of two and n=q^8. Hence
n=1 modulo three. The packed equation

    r=S(n^2-n)+Tplus(n^2-1)

then forces r=0 modulo three for every integer S,Tplus. Our family
has r=3h+1=1 modulo three. Thus it cannot extend to that full
packing, independently of every other coding condition.

This proves that the auxiliary-free Pell subsystem permits incorrect
indices. It does not prove that the complete auxiliary-free universal
system permits them. A separate argument would be needed either
to produce a full-system false witness or to show that the remaining
coding equations exclude every wrong-index case.

## 7. Focused exact verification

`../verification/explore_base_two_wrong_index_rational.py` checks
h=2,3,4,8,16,21,31 with exact integer arithmetic. It verifies the
fractional-root bound, 2^(4h) divisibility, both strict ratio bounds,
both norms, the positive interval, integral positive tau,h_index,
gamma, and positive scaled w,s. It also checks p=J-2 and the
modulo-three packing obstruction. No giant auxiliary witness or
full encoded-system witness is instantiated. The finite receipt
corroborates the general subsystem proof and preserves that scope.
