# The direct q-squared scale reduction from 89 to 88 is unsound

Replacing only `n=q^4` by `n=q^2` in the published universal89 system
does save one multiplication. The resulting source has **88 operations:
46 multiplications and 42 additions**, with the same 34 positive unknowns
and 22 equations. It is unsound: the construction below supplies a full
positive solution at x=1 for a genuine fixed compiler index representing
the empty set.

This refutes this exact scale deletion. It is not a lower bound on other
88-operation certificates, other field layouts, or changed encodings.
The published89 files remain unchanged. The counterexample includes
the original product bound, input gap, radix threshold, fixed-code
congruence and every retained Pell equation.

## 1. The precise source change

In `round38_1980_binary_product_certificate.py`, delete exactly

    q4=q2*q2

and replace the free equality `n=q4` by `n=q2`. No other register or
equality changes. The deleted register has no remaining consumer.
Thus the sole changed source residual is

    n-q^4  ->  n-q^2.

The companion checker compares all 22 residuals with the 88 primitive
instructions, including the unchanged acyclic corrections. All positive
inputs and all three fixed index components remain present.

The packed words remain those of universal89:

    S2=ell+e*q,
    S=g+q*sigma+q^2*S2,
    Tplus=q^2*theta*lambda+ell*(theta*q-b),
    r=S*(n^2-n)+Tplus*(n^2-1).                   (1)

Although g^2<q still follows from the positive product bound, S2 alone
occupies two q-fields. For canonical positive e, S>q^3>q^2=n. The
ordinary packed-mask lemma therefore does not apply. The counterexample
shows that its missing range condition cannot simply be ignored.

## 2. A genuine empty-set compiler index

Use the actual finite sample compiler in
`round37_1980_binary_product_encoding.py`, changing its ordinary row
`2*zero*delta=0` to

    2*delta*delta_copy=0.                         (2)

As with every ordinary row, retain both signs. Its existing copy and
normalization tests give delta_copy=delta, and the existing two unit
tests force delta=1. Equation (2) is then impossible. This is a compiled
inconsistent circuit, not a freely chosen pair of coefficient words.
All other rows, true coordinates, helper complements, resets and support
conventions are unchanged. The formerly used zero coordinate may remain
as an unused physical coordinate; no compiler argument requires every
coordinate to occur in an ordinary equation.

The checker substitutes exactly this row while constructing the sample
layout, restores the inherited compiler immediately, verifies both
resulting expanded signs of (2), and reruns its symbolic coefficient,
target, reset, padding, dummy-exclusion and binary-code checks. The
resulting support bounds are

    K = 36861378055565095491085666132971,
    L = 162259276829213363391578010288128 = 2^107,
    L > 3K+2.

There are 35 coordinates including x, 24 main rows, 121 tested starts,
397 indicator positions, and 912 nonzero complementary coefficients.
Write the resulting fixed polynomials as ell0,e0,D=e0-ell0, exactly as
in the published compiler. Their fixed index will use

    d=2L+4, H0=2^(d-1),
    H=H0-1, V=ell0(2)+2^L*e0(2), Tindex=psi_2(L). (3)

These are fixed positive integers, independent of the queried input.
The threshold is genuine: d-1=2L+3 exceeds 2L+2, so
H0>2*2^(2L+1). It also exceeds the bit lengths needed for
128*D1*cstar^2, 3L and 1024, where D1=912 and cstar=398.
The checker verifies these comparisons without constructing H0.

## 3. Positive coding coordinates at the false input

Take

    x=1, g=1, C=x+g=2,
    B=2H0=2^d, b=H0-1, beta=H0-2, theta=B-2,
    ell=ell0(B), e=e0(B), q=B^L, n=q^2,
    sigma=4*D(B), alpha=q-ell-sigma,
    lambda=(q^2-1)/(B-1),
    t=(ell+e*q-V)/(B-2).                         (4)

All these supplied coordinates are positive integers. In particular,
the binary compiler gives D(B)>0 and ell,e>0. Their degrees are below K,
so ell+4D(B)<5B^K<B^L=q, making alpha positive. The fixed-code
polynomial ell0(T)+T^L*e0(T) is nonconstant with nonnegative
coefficients. Evaluation at B is larger than at two and congruent to
it modulo B-2, making t positive integral. The remaining equalities
follow directly:

    b=x+beta, theta=H+b,
    sigma=(e-ell)*(x+g)^2, ell+sigma+alpha=q,
    lambda*(B-1)=q^2-1, ell+e*q=V+t*theta.

Set S,Tplus,r by their actual expressions (1), with the new n=q^2.
Their positivity gives r>=n^2-1>=n. Also r is even: n and q are even,
ell is divisible by B, Tplus is even, and n^2-n is even. No physical
coordinate interpretation is being assumed for C=2. Indeed, the
original first mask rejects g=1 because its unit digit is forbidden.

The remaining issue is the actual central-binomial divisibility. It
cannot be justified by the old masks. The next section evaluates its
exact valuation instead.

## 4. Exact symbolic population count at the genuine threshold

The companion checker proves, for this fixed layout and every integer
d>=4 with B=2^d, the identity

    popcount(r) = (4L+1201)*d - 99.              (5)

Since n=B^(2L), the required valuation threshold is

    log2(n^2)=4Ld.

Thus the margin is 1201d-99>0. Kummer's identity
v2(binom(2r,r))=popcount(r) proves

    n^2 divides binom(2r,r),                     (6)

including the enormous actual d=2L+4 in (3). This is an exact symbolic
carry calculation, not an extrapolation from smaller numerical radices.

Here is the finite arithmetic certificate for that calculation. Put
Q=B/2=2^(d-1). Every sparse raw coefficient is represented by a pair
(a,c) denoting aQ+c. The geometric part theta*lambda has digit B-2 in
positions 0 through 2L-1. Expanding (1) with n=B^(2L) therefore yields
two constant raw-digit intervals:

    -(B-2) at positions [2L,4L),
    +(B-2) at positions [6L,8L),

and the following finite polynomial contributions, where shifting by h
means multiplication by B^h:

    +1 at 4L, -1 at 2L,
    +sigma shifted 5L, -sigma shifted 3L,
    +ell shifted 6L, -ell shifted 4L,
    +e shifted 7L, -e shifted 5L,
    +(B-2)*ell shifted 5L, -(B-2)*ell shifted L,
    -b*ell shifted 4L, +b*ell.

These are exactly S*n^2-S*n+Tplus*n^2-Tplus. They are sparse except
for the two specified intervals, even though their exponents are huge.

At a digit normalization, include the incoming integer carry in c and
write a=2h+epsilon with epsilon in {0,1}. Under Q>|c|, the following
four rules are exact:

| epsilon | sign of c | outgoing carry | normalized digit | its popcount |
|---|---|---|---|---|
| 0 | c>=0 | h | c | popcount(c) |
| 0 | c<0 | h-1 | B+c | d-popcount(-c-1) |
| 1 | c>=0 | h | Q+c | 1+popcount(c) |
| 1 | c<0 | h | Q+c | d-1-popcount(-c-1) |

Thus every digit contributes an affine function of d, while its outgoing
carry is independent of d. Between sparse events, normalize the constant
background until its outgoing carry equals its incoming carry; all
remaining positions in that interval then contribute the same affine
function, multiplied by the exact interval length. This skips no carry
transition. The final carry is zero.

The recorded run uses 4,825 event positions and 9,110 normalization
calls. Every absolute offset |c| is at most 6. Consequently Q>=8 for
d>=4 justifies every one of its symbolic branches simultaneously. The
sum of the affine contributions is exactly (5). The receipt records
the normalization categories, coefficient sum, constant sum and offset
bound, so all arithmetic is reproducible without materializing B, q
or r. Independent dense-integer comparisons on 12 small support cases
check the algorithm against ordinary `int.bit_count`; five numerical
radices on the genuine sparse layout also match (5). Those finite
crosschecks are distinct from the symbolic certificate valid for all d.

## 5. A fresh full positive Pell extension

The preliminary soundness estimate r<3n^3 need not hold for (4), and
is not used here. The converse constructs witnesses directly at this
actual even r. We have B,q,n powers of two, q=B^L, r>=n>=64,
L<2r+1, and (6). Put

    J=2r+1, U=2^J, w=U/n^2,
    xi=(U+1)^(2r)/U^r, Y=floor(xi), s=Y/n^2,
    a=Y*(U+1), A=a+2, Dpell=A^2-1,
    E=UY, P=2UY^2+1,
    c=psi_A(J), dP=chi_A(J), k=psi_P(r+1).

The symbol dP denotes the source variable d; it is unrelated to the
radix bit width d used above. Because n^2<=r^2<U, w is positive integral.
The binomial expansion gives Y=binom(2r,r) modulo U, so (6) makes s
positive integral. Also Y>=U^r and a>U^(r+1). Hence 4r/a<1/2 and
16r/(U+1)<1/2 directly, regardless of r/n^3. The exact base-two Pell
ratio proof gives

    Y<xi<c/k<Y+3/4.

It follows that eta=c-Y*k and zeta=k-eta are positive integers. Set

    tau=(chi_P(r+1)-1)/2, h=(k-r-1)/E.

The odd P and its congruence modulo P-1=2UY^2 give their integrality;
strict Pell growth gives positivity. The first norm and index equations
are therefore satisfied.

For the relaxed norm and half-parameter block, use the same constructive
formulas as in `HALF_PARAMETER_PELL_92_PROOF.md` at this new A:

    m=2cJ, f=chi_A(m), i=Dpell*psi_A(m)/c^2,
    R=i*c^2, y_aux=psi_R(J), u_star=chi_R(J)/R,
    o=(u_star-c)/f, j=(u_star-J)/c.

The required positive signs hold because r is even and J=1 modulo four.
The generic construction proves each displayed quotient integral and
positive and satisfies both auxiliary norms and congruences.

For the second index set

    kappa=psi_A(L), mu=chi_A(L), phi=c-kappa,
    Delta=(psi_A(L)-psi_2(L))/a.

Since 2<=L<J and A>2, phi and Delta are positive; A=2 modulo a gives
the integral index quotient. Both exponent relations already hold by
construction, U=2^J and q=B^L. Their size hypotheses are valid:

    2^(3J)=U^3<U^(r+1)<a,
    B^(3L)=q^3<n^2<=r^2<U<a.

The chi congruences therefore give integer gamma and rho, and their
signs follow from

    dP-a*c=2c-psi_A(J-1)>c>U,
    mu-(A-B)*kappa=B*kappa-psi_A(L-1)
                         >(B-1)*kappa>q.

Their moduli 4a+3 and Dpell-(A-B)^2 are positive. This constructs all
remaining supplied positive coordinates. Thus all 22 equations of the
88-operation candidate hold at the false input x=1 for the genuine
empty-set index (3). No old Pell tuple or failed soundness hypothesis
has been reused.

## 6. Scope of the bounded investigation

The exact source, sparse symbolic calculation, layout checks and finite
crosschecks are in `explore_binary_scale_q2.py/.json`. The proof above
adds the fixed-threshold and full positive-witness argument; giant
Pell coordinates are not numerically materialized.

The same investigation found no operation saving from elementary
Horner rearrangements of the universal89 S,Tplus and packed-r formulas.
That bounded inspection is not a circuit lower bound. Introducing a
square-root field width to use g^2<q also requires a paid relation
establishing that width. A different open proposal replaces the two-add
bound ell+sigma+alpha=q by S+alpha=n; it is not analyzed or certified
here. Its possible spill across code fields remains an explicit
soundness obligation, rather than an accepted 88-operation result.

Review status: author and independent full scoped mathematical/source
reviews pass. The independent fresh call matches the saved JSON exactly
and preserves both source and receipt hashes. In addition, all 16 recorded
digit-normalization categories were independently checked with ordinary
integer division and population count at widths 4, 5, 9, 31, 257 and 1024
(96 checks). The review includes the genuine empty-set compiler index,
fixed-threshold inequalities and fresh positive Pell extension; it does
not claim numerical construction of the enormous final tuple.
