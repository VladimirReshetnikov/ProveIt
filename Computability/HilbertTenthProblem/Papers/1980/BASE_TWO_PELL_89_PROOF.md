# Base-two Pell proof for the 89-operation narrow binary system

This note proves both positive-domain directions at the changed packing
scale n=q^4 and the preliminary range n<=r<3n^3. The Pell equations are
those of the established 90-operation construction, with A=a+2 and theta=B-2.
The complete outer proof is `BINARY_PRODUCT_89_PROOF.md`; the source is
`../verification/round38_1980_binary_product_certificate.py`.

The wider preliminary range is essential: Tplus<n is recovered only
after the independent exponent argument proves q=B^L. Nothing below
assumes that range conclusion or canonical coefficient decoding.

## 1. Definitions and initial hypotheses

The binary compiler supplies, before any exponent or coefficient test,

    n=q^4, n>=64, n<=r<3n^3, 2<=L, 3L<=B<=n,
    C_code=x+g>=2,
    ell<q, e<q, 0<sigma<q, C_code^2<q,

These follow from the unchanged product bound and the new preliminary
estimates 0<S<n and 0<Tplus<2n, before any mask interpretation. In
particular the index is positive and at least n^2-1. Write the quantities as

    U=w*n^2, Y=s*n^2, E=U*Y, Q=U*Y^2, P=2Q+1,
    a=Y*(U+1), A=a+2, D=A^2-1, J=2r+1.

Keep the first norm, interval, and index congruence:

    tau*(tau+1)=(E^2+U)*(Y*k)^2,
    c=Y*k+eta, k=eta+zeta,
    k=r+1+h*E,

with all supplied unknowns positive. Keep the main norm, relaxed
auxiliary norm, and half-parameter block:

    d^2=1+D*c^2,
    R=i*c^2, K=R^2=D*(f^2-1),
    u=J+j*c=c+o*f,
    K*(u^2-y_aux^2)=1-y_aux^2.

Use the first exponential congruence

    d=U+a*c+gamma*(4a+3),                         (1)

and the fixed third index

    Tindex=psi_2(L), kappa=Tindex+Delta*a.         (2)

The second Pell norm, positive gap, and exponent congruence remain

    c=kappa+phi,
    mu^2=1+D*kappa^2,
    mu=q+kappa*(A-B)+rho*(D-(A-B)^2).             (3)

The coefficient construction chooses H=H0-1 and theta=H+b=B-2,
so the actual radix remains B=H0+1+b. Its support and mask arguments
are established separately in the binary compiler proof.

## 2. Exact indices before exponent decoding

The purely preliminary inequalities give

    U,Y>=n^2>=4096,
    a>n^4>6n^3>J, E>=n^4>3n^3>=r+1.

Indeed n>=64>6, while J=2r+1<6n^3 because r is integral.
These comparisons replace the old 2n^3 range estimate.

The first norm is the same norm of parameter P as before, so
k=psi_P(t) for some positive t. Its congruence modulo E gives

    t=r+1+vE, v>=0.

Before assuming v=0, this implies t>=r+1. Since P>A and c>Yk>k,
comparison with the main norm c=psi_A(p), d=chi_A(p) gives

    p>=t+1>=r+2>=66, c>AD^2, c>J>1.

These are exactly the hypotheses used by the retained relaxed auxiliary
rank lemma and the half-parameter proof. They therefore recover

    p=J, c=psi_A(J), d=chi_A(J).

The argument is generic in A>1; it uses neither A=a+4 nor even r.

If v>=1, standard Pell growth and E>r imply

    c/k <= (2A)^(2r)/(2P-1)^(r+E)
        <= (2A/(2P-1))^(2r)<1/2,

because the changed exact difference is

    (2P-1)-4A=4Y*(U*(Y-1)-1)-7>0.

This contradicts c/k>Y. Consequently

    k=psi_P(r+1).

No exponent relation or decoded circuit equation has entered this step.

## 3. Ratio estimates and growth before exponent decoding

Put xi=(U+1)^(2r)/U^r. The standard lower and upper Pell bounds give

    c/k >= xi*(1+3/(2a))^(2r)*(1+1/(2Q))^(-r)
        > xi,                                     (4)

since (1+3/(2a))^2>1+3/a>1+1/(2Q), using 6Q>a.
For the upper estimate,

    c/k < xi*(1+2/a)^(2r).

Here

    4r/a < 12/n <= 3/16 < 1/2.

The elementary bound (1+t)^m<=1/(1-mt)<1+2mt therefore gives

    c/k < xi*(1+8r/a).                           (5)

The interval and (4) imply xi<Y+1. Since xi>U^r and Y is an
integer, this yields

    Y>=U^r, a=Y*(U+1)>U^(r+1).                    (6)

Using xi<Y+1<2Y in (5),

    0<c/k-xi<16r/(U+1).                          (7)

The right side is not yet claimed to be small. Its eventual smallness
will follow from the first exponent equation, after (6) has justified
that equation's interpretation.

## 4. Recover both exponentials

The source chi-congruence exponent criterion is the version of Jones's
Lemma 2.22 stated after the indexed-Pell construction in
`../1982/jones1982_corrected.tex`. Equation (1) has base 2 because

    A-2=a, 2*A*2-2^2-1=4A-5=4a+3.

The criterion's required growth hypotheses follow before its use:

    2^(3J)=8*64^r< U^(r+1)<a<A,
    U^3<=U^r<a<A.

Thus (1) proves U=2^J. Since U=w*n^2, n and q are powers of two.
No assertion that b or H is a power of two is needed.

For the second index, the norm and gap in (3) give
kappa=psi_A(t0), mu=chi_A(t0), with 0<t0<J. We also have
0<L<J from 3L<=B<=n<=r. Reducing (2) modulo a, and using
A=2 mod a, gives

    psi_2(t0)=psi_2(L) mod a.

Both positive quantities are strictly smaller than a: for any
0<t<J, psi_2(t)<=4^(t-1)<2^(3J)<a. Hence the congruence is an
integer equality, and strict growth of psi_2 implies t0=L.

The same original size bounds justify the second exponent criterion:

    B^(3L)<=B^B<=n^n<=U^r<a<A,
    q^3<=n^n<=U^r<a<A.

The last equation of (3) therefore gives q=B^L. Since q is a power
of two, B is also a power of two.

## 5. Exact rounding with base two

After U=2^J=2*4^r, (7) is strictly less than 1/2 because U>32r
for r>=64. Write the binomial expansion as xi=F+T, where

    F=sum_(j=r)^(2r) binom(2r,j)*U^(j-r),
    T=sum_(j=1)^r binom(2r,r-j)/U^j.

The exact symmetry of the binomial coefficients gives

    0<T <= (4^r-binom(2r,r))/(2U)<1/4.           (8)

Thus F is the integer part of xi, and F=binom(2r,r) modulo U.
The positive interval, (4), (7), and (8) give

    F<xi<c/k<Y+1,
    Y<c/k<xi+1/2<F+3/4.

Integrality forces Y=F. Since n^2 divides both Y and U, it divides
binom(2r,r). This recovers all conditions needed by the retained
binary packed-mask mechanism.

## 6. Necessity and positivity

Start with the canonical coding witnesses in `BINARY_PRODUCT_89_PROOF.md`.
They have B and q powers of two, q=B^L, n=q^4, even r>=n, and
n^2 dividing binom(2r,r). Choose

    J=2r+1, U=2^J, w=U/n^2,
    Y=floor((U+1)^(2r)/U^r), s=Y/n^2,
    a=Y*(U+1), A=a+2, E=UY, Q=UY^2, P=2Q+1,
    c=psi_A(J), d=chi_A(J), k=psi_P(r+1).

The quotient w is positive integral: n^2 and U are powers of two
and n^2<=r^2<2^(2r+1)=U. Equation (8) and central-binomial
divisibility give positive integral s. The same ratio estimates, now
applied to the chosen indices, yield

    Y<xi<c/k<Y+3/4.

Therefore eta=c-kY and zeta=k-eta are positive integers. Set

    tau=(chi_P(r+1)-1)/2,
    h=(k-r-1)/E.

The odd base P makes tau integral; its positivity and that of h
follow from strict Pell growth. Congruence modulo P-1=2Q gives the
integrality of h.

Choose the relaxed auxiliary and half-parameter witnesses at this new
generic A exactly as in `HALF_PARAMETER_PELL_92_PROOF.md`. Even r
gives J=1 mod 4, so both normalized-root congruences have the required
positive sign and the newly chosen o,j,y_aux are positive.

Choose kappa=psi_A(L), mu=chi_A(L), phi=c-kappa, and

    Delta=(psi_A(L)-psi_2(L))/a.

Polynomial congruence gives integrality of Delta; strict monotonicity
in the base, A>2 and L>=2 give its positivity. The gap phi is
positive because L<J.

The exponent congruences give integer quotients gamma and rho. Their
positivity is explicit:

    d-a*c=2c-psi_A(J-1)>c>U,
    mu-(A-B)*kappa=B*kappa-psi_A(L-1)
                         >(B-1)*kappa>q.

Here c,kappa>=A and A>U^3,q^3. Both moduli are positive. Thus
every changed supplied Pell witness is positive, with no claim that
the previous base-four witnesses remain unchanged.

## 7. The changed scale and the full-system proof order

The retained 43-operation first-index, ratio, main, relaxed and
half-parameter kernel and 14-operation second-exponent interface are
unchanged. The complete 89-operation source saves one multiplication in the radix
power chain: q^2,q^4,n^2=q^8 replace q^2,q^4,q^8,n^2=q^16. All source
equations use the new actual n and r; necessity constructs fresh
w,s,a,c,d,k and every other auxiliary by the formulas above.

Only after Section 4 has independently proved q=B^L does the outer proof
recover Tplus<n. The normal packed-binomial lemma then applies at the
new n=q^4. The middle mask must still be decoded and its possible
low-digit perturbation excluded; these are obligations of the outer
proof, not assumptions in this Pell argument.

## 8. Verification and scope

The existing exact base-two Pell regression checks the unchanged
canonical norm, ratio, rounding and exponent identities. The new
certificate checker compares all 22 fresh source residuals with the
changed 89-instruction schedule. The general inequalities in Sections 2
and 3 explicitly cover the enlarged range before either exponential is
decoded.

The proof does not claim to numerically materialize the enormous
complete Pell witnesses for a packed universal instance. That
existence follows from Section 6 and the complete canonical coding
construction. Review status: author and independent complete scoped proof reviews pass.
Fresh exact source and finite regression runs match their saved receipts.
The independent Pell review also reran the eight exact canonical cases
and checked thirty endpoints in the widened preliminary range.
