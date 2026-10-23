# A common sparse-padding source, with two correct threshold interfaces

## 1. Fixed source and positional interface

Use the selectively shifted natural source in `selective12_source.json`.
Its positive-parent equivalence is proved in `SELECTIVE_POSITIVITY_PROOF.md`.
There are n=31 variable digit positions, m=22 target positions, and 109
weighted source records. Let the independently verified positional data have:

- distinct nonnegative variable positions w_i;
- a distinct padding position p;
- W=max(p,w_1,...,w_31);
- distinct targets H_j, all at most K;
- D(t)=sum c_(j,alpha)t^(H_j-e(alpha)), where
  e(alpha)=(2-|alpha|)p+sum alpha_i w_i;
- d=deg D, K=d+2W, and a positive leading coefficient of D.

Every reversed exponent is nonnegative. The positional isolation certificate
must prove, for every source record and every quadratic multinomial label,
that H_j-e(alpha)+e(beta)=H_l exactly when j=l and alpha=beta.
It then gives

 [t^H_j] (t^p+sum x_i t^w_i)^2 D(t) = 2r_j(x).

The targets need NOT have maximum d, and interior p need NOT be zero.
All formulas below retain that distinction. No full Sidon hypothesis is used.

Let M be a positive integer strictly exceeding every absolute weighted
coefficient. Isolation implies the 109 reversed positions are distinct,
so every coefficient of D also has absolute value less than M, without a
factor of 109. Choose even kappa with a=2^kappa >=8192M.
For the complete round8 native tuple, the independent exact audit supplies

 M=2^864013, kappa=864026, a=2^864026.

The coefficients are ordinary explicit integer constants. These exponents
are fixed numbers, not variable exponentiation in the final polynomial.

For every real B>M+1, the positive integer leading coefficient gives D(B)>0:
the total magnitude of lower terms is less than M B^d/(B-1)<B^d, while the
leading contribution is at least B^d. Also

 0<D(B)<M B^(d+1)/(B-1).

## 2. Sparse source formulas and bounds

For integer b>=1 and integer g>=0, put

 B=a b^2, ell=sum_i B^w_i, A=sum_j B^H_j,
 N0=B^(W+1), Z=B^(K+1), E=K+W+2,
 mask=N0-1-(b-1)ell,
 J=2(B^p+g)^2 D(B)+A,
 S=g+N0 J,
 T=mask+N0(B-2)A.

All are polynomial abbreviations. Every digit of mask is B-b at a selected
variable position and B-1 elsewhere through W. Thus 0<=mask<N0 and T>=0,
without assuming a binary base. Since D(B)>0 and B^p>0, J>0 and S>0.

If additionally g<4b B^W, then g<N0 and B^p+g<5b B^W. Consequently

 2(B^p+g)^2D(B) <50 M b^2 B^(K+1)/(B-1)
                    <=(50/8192) B Z/(B-1) <Z/128.

The last inequality holds since B>5. Since Hmax<=K and B>129,
A<B^(Hmax+1)/(B-1)<=Z/(B-1)<Z/128. Hence 0<J<Z/64<Z.
Also (B-2)A<B^(Hmax+1)<=Z. Integrality and the low-block bounds imply

 0<=S,T<N0 Z=B^E, and S+T<2B^E.                  (1)

This bound explicitly covers interior padding. Replacing B^p+g by 1+g
would not be a valid justification when p is nonzero.

## 3. Signed-borrow target test

Assume now b=2^k, so B=2^v with v=kappa+2k. The low mask condition

 g AND mask = 0

is equivalent to g=sum x_i B^w_i with 0<=x_i<b. This uses g<N0, distinct
positions, and the binary digits of B-b. The padding position is not a
variable digit.

For such a tuple write h_t for the coefficient of
(t^p+sum x_i t^w_i)^2D(t). Its degree is at most K. Each coefficient is
bounded using nonnegative coefficients of the square:

 |h_t| < M(1+sum x_i)^2 <=M(31b)^2 <1024 M b^2 <=B/8.

Thus J=sum_t(2h_t+delta_t)B^t, where delta_t is 1 at each target and zero
elsewhere. Starting at incoming borrow c_-1=0, normalize from low to high
with c_t=floor((2h_t+delta_t+c_(t-1))/B). Inductively c_t is -1 or 0.
At a target:

- h_t=0 gives digit 0 or 1, disjoint from the mask B-2;
- h_t>0 gives a digit at least 2 and below B/2, not disjoint;
- h_t<0 gives a digit above B/2, not disjoint.

Since J>0 and J<Z, these normalized digits describe an ordinary finite
nonnegative integer. No convention for bits of negative integers is used.
Therefore J AND ((B-2)A)=0 exactly when all target coefficients vanish.
By positional extraction that is exactly the common-zero condition r_j(x)=0.
The disjoint low and high blocks now yield

 S AND T=0 iff g codes a common natural zero of the source.           (2)

## 4. Common two-block identity

For nonnegative S,T with S+T<L=2^u, and any fixed positive integer c, define

 R_c=c L^2+(S+T)L+(L-1-S).

The three words do not overlap. Let pop denote binary digit sum and
Delta_pop=pop(S)+pop(T)-pop(S+T). Then

 pop(R_c)=pop(c)+u+pop(T)-Delta_pop.

Delta_pop>=0, with equality exactly when S AND T=0. The elementary factorial
valuation identity v_2(binomial(2R_c,R_c))=pop(R_c) gives

 2^(u+pop(T)+pop(c)) divides binomial(2R_c,R_c)
 iff S AND T=0.                                                    (3)

This is the exact threshold, not a generic 2u threshold. For the current
mask, the 31 low variable positions each remove k set bits and the 22 high
target positions each contribute v-1 bits. Thus

 pop(T)=(W+1)v-31k+22(v-1)=(W+23)v-31k-22.           (4)

## 5. Nine-natural Jones interface: calibrate a polynomial square

Jones's ratio theorem requires a threshold of the form N^2. Set

 L=2bB^E, R=L^2+(S+T)L+L-1-S, Gcap=32bB^W.

Bound (1) gives S+T<L. Here u=1+k+Ev and pop(c)=1, so (3)-(4) give the
threshold exponent

 (E+W+23)v-30k-20.                                  (5)

Write V=E+W+23=K+2W+25. If K is even, set

 q=(K+2W+10)/2,
 N=2^(15kappa/2-10) B^q.                            (6)

Since kappa is even, the constant exponent and q are integers; twice
log_2 N is exactly (5). If K is odd, a valid alternative is

 q=(K+2W+9)/2,
 N=2^(8kappa-10) b B^q.

The 174-packed and 170-packed-shifted examples have even K and use no
extra b factor. The degree-minimizing 170-packed example has K=4425, so it
uses the displayed odd-K branch: q=2387 and N=2^(8kappa-10)bB^2387.
Its source degrees are deg R=18390, deg N=4775, deg Gcap=341. This parity check must not be omitted when changing positions.

For every natural outer assignment b>=1 and g>=1, S>0,T>=0 and
R=L^2+(L-1)S+LT+L-1>=L^2+L-1>=8. Also R>=b, N>=8, N>=b and Gcap>0.
These unconditional hypotheses are exactly what the imported Jones ratio
interface needs before a candidate polynomial zero has been established.
Under its soundness output 8g<Gcap, g<4bB^W and the preceding source test
applies. Conversely, a common source zero x can be encoded for every
sufficiently large power of two b by g=sum x_iB^w_i. The source origin is
not a zero, hence g>=1. Moreover

 g< bB^W, so 32g<Gcap.

The endpoint b=1 is harmless: its digit mask forces every decoded digit to
zero, contradicting the nonzero-source guard. Thus allowing b=1 introduces
no new polynomial zeros. The positive equation may use b itself as an input;
the natural equation uses b=b0+1.

All sufficiently large powers of two are allowed; no extra cofinality or
parity assumption on the exponent of b is introduced.

For W174,p81,d4072,K4420,Hmax4276, E4596 and q2389, the exact relevant degrees
in the outer natural inputs are

 deg R=4E+2=18386, deg N=2q=4778, deg Gcap=2W+1=349.

The leading term of R is L^2, of positive coefficient. Indeed S,T have degree
at most 2E, while L has degree 2E+1. The selected native kappa gives the
fixed coefficient in (6) as 2^6480185. N and L are DIFFERENT quantities.

## 6. Ten-integer interface: retain the sharper nonsquare threshold

The ten-integer bridge permits an arbitrary polynomial threshold Y, not
necessarily a polynomial square. Take the usual b=1+3f with f!=0 and b a
square, so b>=4. Put

 L=B^E,
 X=L^2+(S+T)L+L-1-S,
 Y=2^[kappa(K+2W+25)-21] b^[2(K+2W+25)-31],
 cap=bB^W.

The bridge's upper bound g<2cap is stronger than the common bound used in
Section2. In fact S+T<L for this branch: J<Z/64;
(B-2)A<B^(Hmax+1), and in the selected certificates Hmax<=K-2, so
(B-2)A<Z/B^2<Z/128. Also (g+mask)/N0<2<Z/128.
Their sum is less than Z, proving the strict block bound. More generally,
Hmax<=K and B>=8192 give (B-2)A<=22B^(Hmax+1)<=22Z, which alone is NOT
sufficient; use the actual target gap or a separately proved stronger bound.
The selected round8 target gaps K-Hmax are 144 and 134, so the displayed
stronger estimate has ample margin.

Now u=Ev, so the exact exponent from (3)-(4) is

 (E+W+23)v-31k-21
 =kappa(K+2W+25)+[2(K+2W+25)-31]k-21,

exactly log_2 Y. The source therefore has the required divisibility test.
The selected values give deg X=4E and deg Y=2(K+2W+25)-31.

Before any binary-base assumption, b,B,L are 1 modulo 3 because kappa is
even. Since ell has 31 terms and A has 22, the source formulas give
T= -22=2 modulo3. Hence X=1+T=0 modulo3. Moreover X>=L^2+L-1>3b and
Y>max(b,256). These are the inherited integer bridge's unconditional
size/congruence hypotheses.

Completeness needs b<=g<cap. At every common source zero, D>0 and Delta>0.
These are distinct natural coordinates, and at most one variable position
is zero. Thus at least one positive coordinate has positive weight, giving
g>=B>=b. The upper bound follows as in Section5. A sufficiently large
power-of-two square b can therefore be chosen within the inherited integer
bridge's admissible family.

Do NOT copy the natural L=2bB^E/top1 construction into the integer bridge:
it need not give 3|X. If a square threshold were ever required there, one
valid correction would use L=bB^E and top word c=10. That word has popcount2
and is 1 modulo3, preserving both (5) and 3|X. It raises deg X by2 and deg Y
by1 versus the nonsquare branch, so it is not the recommended integer form.

## 7. Proof boundary

The positivity bijection, sparse bounds, signed-borrow analysis, popcount
threshold and modular facts above are elementary mathematical arguments.
Finite checks authenticate the data and exercise the identities, but do not
prove consistency. The compiler/refutation equivalence and the chosen Jones
or Sun bridge remain the explicitly inherited mathematical dependencies.
