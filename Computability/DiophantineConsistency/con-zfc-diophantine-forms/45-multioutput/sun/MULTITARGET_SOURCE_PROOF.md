# Simultaneous quadratic positional coding: the main construction

## Fixed source and finite certificate

Take the 22 quadratic residuals r_j of the included
`data/parent_system60.json`. They have 31 positive
unknowns. The transport coordinate is the already shifted convention z_old=z+1
of package31's 60-operation parent. Write q_j(z)=r_j(z+1), so all z_i are nonnegative. The inherited
quartic proof and complete four-port compiler tuple establish

  exists z in N^31, all q_j(z)=0 iff not Con(ZFC).

In particular the fifth shifted row has q_5(0)=1; thus no simultaneous
zero has every coordinate zero. This construction uses the quadratic
rows directly; it does not first form the quartic sum of squares.

Choose the 31 positive B2 weights in `../quartic/B2_CERTIFICATE.json`,
whose maximum is W=799. The 528 unordered pairs, with repetitions and
padding weight zero, have different sums. Consequently all monomials of
total degree at most two have different weighted exponents.

Let h=2W+1=1599, and order the rows as 1,2,3,4,6,...,22,5.
The 22 targets are H_j=jh for j=1,...,22. Put

  Hmax=35178; K=Hmax+2W=36776.

For the row at target H_j and its coefficient p_{j,alpha}, define

  c_{j,alpha}=(2-|alpha|)! prod_i(alpha_i!) p_{j,alpha},
  D_j(t)=sum_alpha c_{j,alpha} t^(H_j-alpha.w),
  D(t)=sum_j D_j(t).

All exponents are nonnegative. Each D_j is supported on [H_j-2W,H_j],
and these intervals are disjoint. The maximum exponent Hmax has
coefficient 2q_5(0)=2. There are 136 nonzero symbolic coefficient records,
including their explicit polynomials in the four fixed compiler ports.
No row choice or coefficient is an additional witness.

Let M>=1 bound the absolute values of all these fixed c_{j,alpha}.
The payloads and exact coefficient checks give M<2^2134926. Set

  beta_sun=2^2134940.

Then beta_sun>4 M*32^2. The exponent is even, so beta_sun is a square
power of two. This coefficient bound is substantially smaller than that
required by the old quartic source, but it is not a new compiler tuple.

## Source polynomials in the two integers f,g

Put

  b=1+3f; B=beta_sun*b^2;
  ell=sum_i B^w_i; Targets=sum_{j=1}^{22} B^H_j;
  N0=B^(W+1); N1=4B^(K+1); N=N0*N1;
  Mask=N0-1-(b-1)ell;
  T=Mask+(B-2)*Targets*N0;
  J=2(1+g)^2 D(B)+B*sum_{i=0}^K B^i;
  S=g+J*N0;
  R=(S+T+1)*N+T+1;
  X=(N-1)*R; Y=N^2; Ccap=b*B^W.

These are ordinary integer polynomials. All exponents and sums are fixed.
The program expands powers and geometric sums into binary arithmetic
gates without division or exponentiation by a variable. For efficient
evaluation set u_0=B^W, u_i=B^(W-w_i), and let V_j be the homogeneous
quadratic sum of c_{j,alpha}u_0^(2-|alpha|)prod_i u_i^alpha_i. Then
D(B)=B sum_{j=1}^{22}(B^(2W+1))^(j-1)V_j, evaluated by Horner.
This identity follows from H_j=j(2W+1), and reduces the live circuit
from 954 to 936 binary operations without changing its polynomial.

Assume f!=0 and b is a square. Since b=1 mod3, f>0 and b>=4.
All source quantities in the next bounds are positive or nonnegative.
The leading coefficient 2 of D and its remaining coefficient bound M
imply D(B)>0: the absolute value of the lower terms is at most
M*(B^Hmax-1)/(B-1)<B^Hmax, whereas the leading term is 2B^Hmax.
The disjoint row supports and B2 property give |coeff_i D|<=M.

If 0<=g<2Ccap, then g<N0 and 1+g<=3bB^W. Therefore

  0<J < [(B/2)+B]*B^(K+1)/(B-1) < 4B^(K+1)=N1.

Here 2M(3b)^2<B/2 follows from the fixed beta bound.
The integer Mask has digits B-b at the allowed positions and B-1
elsewhere through W. Thus 0<=Mask<N0. The polynomial
(B-2)*Targets has digits B-2 at distinct positions <=Hmax<K+1,
so it is <B^(K+1)<N1. Consequently 0<=T<N and 0<=S<N.
As in the single-target source proof, X>3b, Y>max(b,256), and 3|X.
The last fact uses beta_sun=1 mod3, b=1 mod3, hence N=1 mod3.
Also Ccap=2^(2134940 W)b^(2W+1), the required fixed monomial bound.

## Simultaneous coefficient isolation

If b is also a power of two, the same is true of B and N. Write N=2^r
and let s_2 denote binary digit sum. Expanding the definition gives

  X=(S+T)N^2+(N-1-S)N+(N-1-T).

The low two base-N digits are valid because 0<=S,T<N, even if S+T>=N.
Hence s_2(X)=2r-s_2(S)-s_2(T)+s_2(S+T). Legendre's formula gives
v_2(binomial(2X,X))=s_2(X). Since s_2(S)+s_2(T)-s_2(S+T)
is the nonnegative number of binary carries, Y=N^2 divides that binomial
exactly when S and T add without binary carries. Splitting at the
power-of-two boundary N0 proves

  Y | binomial(2X,X)
  iff g has no binary carry with Mask
      and J has no binary carry with (B-2)*Targets.

The first condition, together with g<2Ccap, is equivalent to

  g=sum_i z_i B^w_i, with 0<=z_i<b.

For such g define C(t)=(1+sum_i z_i t^w_i)^2. For any j,

  coeff_{H_j}(C(t)D_j(t))=2q_j(z).

This is the multinomial expansion and uniqueness of all degree-at-most-two
weighted sums. If k!=j, then

  support(C D_k) is contained in [H_k-2W,H_k+2W].

Since |H_j-H_k|>=2W+1, the coefficient of t^H_j in C D_k is zero.
Therefore coeff_{H_j}(CD)=2q_j(z) for every row.

Off-target overlaps between different C D_k do not affect the bound:
for each exponent of D there is at most one supported row monomial, so
every coefficient of CD has absolute value at most

  M*sum coeff(C)=M(1+sum_i z_i)^2<=M(31b)^2<B/4.

For every exponent e=0,...,K put

  a_e=coeff_e(CD)+B/2.

These integers satisfy 0<a_e<B and give J=2 sum_e a_e B^e.
After dividing both binary summands by two, absence of carries with
(B-2)*Targets is equivalent to absence of carries when
sum_e a_e B^e is added to (B/2-1)*Targets. At a target cell, the latter
mask has ones at all binary digits below the top binary digit of that
base-B cell. Since 0<a_e<B, carry-freeness is equivalent to a_e=B/2.
At non-target cells the mask is zero. Thus

  J has no carry with (B-2)*Targets iff every q_j(z)=0.

This proves exactly the simultaneous-row replacement of the old single
quartic coefficient test.

## Completeness and reverse direction

If all q_j(z)=0 for a nonnegative vector z, that vector is not zero.
Choose an arbitrarily large even k and b=2^k exceeding every z_i;
then f=(b-1)/3 is a positive integer, b is a square, and the encoded g
satisfies b<=g<Ccap. The carry calculation proves
Y|binomial(2X,X).

Conversely, f!=0, b square and a power of two, 0<=g<2Ccap, and the
binomial divisibility decode a nonnegative simultaneous zero of all rows.
These are the exact forward/reverse and size properties used by the
Sun 2026 binomial/Lucas bridge. Nothing in that bridge uses whether the
source was originally a single polynomial or several residuals; its
input consists of these proved source properties.

## Final ten-integer polynomial and inherited endpoint

Keep the exact three-radicand, quintic-merger ten-integer tail of
`upstream/SIGNED10_PROOF.md`, Sections 4–8, and replace only b,X,Y,Ccap
by the formulas above. There are still exactly ten unrestricted integer
variables f,g,h,k,l,w,x,y,z,m. The tail is written explicitly as a
radical-free arithmetic circuit in `generated/multitarget_sun10.json`.
Its validity is the cited Sun-2026 Lucas/binomial bridge together with
the coprime square merger, rational-root-free quintic divisibility merger,
and separating-norm proof reproduced in the upstream proof document.
The newly authored verifier compares the tail with the old one under
exactly those four substitutions.

Consequently a zero of the new ten-integer polynomial exists iff the
22 shifted source residuals have a simultaneous nonnegative zero.
Composing with the inherited compiler/K215 arithmetic endpoint gives,
in ZFC, that the polynomial has no integer zero iff Con(ZFC).
This proves an equivalence, neither side separately. It is an ordinary
mathematical proof, not a new kernel-checked certificate.

## Attribution and new content

The Lucas/binomial bridge is Sun's work, and the factorial-weighted
coefficient method builds on the Matiyasevich–Robinson–Sun constructions.
The new synthesis simultaneously codes the quadratic residuals rather
than their quartic sum of squares, uses a short finite B2 positional
certificate, and tests all target digits with one no-carry condition.
The theorem preserves the ten-integer count while reducing both degree
and arithmetic-circuit size. No global minimality is asserted.
