# Binary narrow packing: accounting and conditional canonicality

This bounded exploration concerns the 90-operation binary product
system. It establishes no smaller count and no soundness theorem for
the proposed narrow packing. The correct bound
`ell+sigma+alpha=q` and product `sigma=(e-ell)C^2>0` are retained.

## 1. The direct arrangement still costs 90

Consider

    S2=ell+eq,
    S=g+q*(S2+q^2 sigma),
    Tplus=q*Tcoef+ell*(theta*q^3-b),
    Tcoef=1+theta*lambda, theta=B-2, n=q^4.

Relative to round37, change exactly these instructions:

    q8=q4*q4             -> q3=q2*q,
    Sq4=Sin*q2           -> Sq4=Sin*q,
    Tq4=Tcoef*q2         -> Tq4=Tcoef*q,
    theta_q4=theta*q4    -> theta_q4=theta*q3.

Change the free equality n=q8 to n=q4. All other instructions remain
as written. There are still three multiplications for radix powers:
q^2,q^3,q^4 replace q^2,q^4,q^8. The complete schedule remains
**90=48 multiplications+42 additions**.
`../../tmp/check_binary_short_packing.py` verifies its exact symbolic
S,Tplus,packed-r expressions and full instruction histogram. This
is not a universality certificate for the changed system.

The alternate order

    S=g+q*sigma+q^2*S2,
    Tplus=q+q^2*theta*lambda+ell*(theta*q-b)

uses only q^2,q^4 and saves one power multiplication. However, the
shared Tcoef=1+theta*lambda no longer supplies the constant term of
Tplus: that term is q instead of q^2. Its direct factored construction
therefore adds one addition. It gives 47 multiplications and 43
additions, again 90 operations. These counts concern the specified
schedules and are not lower bounds on every possible schedule.

## 2. Binary canonicality can clear a first-block borrow conditionally

Assume q=B^L and that S and T=Tplus-1 from the first arrangement
have already been shown to have no intersecting binary bits. This
is an explicit hypothesis, not a consequence of the narrow binomial
condition proved here. Retain

    0<ell<e<q, sigma<q, g<q,
    lambda=(q^2-1)/(B-1), theta=B-2.

Write b ell=kq+r_b, where 0<=r_b<q. Then

    T=(q-1-r_b)+q*(theta lambda-k)+q^3 theta ell.

Here 0<=k<=b-1<theta. The first base-B digit of the middle mask is
B-2-k; the remaining 2L-1 digits are B-2. Nonintersection makes
every digit of S2 binary except possibly its unit digit d0, with

    d0<=k+1<=b=B-H0-1.

Let F(T) be the actual digit polynomial of S2, of degree below 2L.
The fixed-index congruence and binary canonical index say

    F(2)=V modulo B-2,
    V=ell0(2)+2^L e0(2)<2^(L+K), K+1<L.

The fixed H0 threshold makes

    0<=F(2)<=B-H0-1+sum_(j=1)^(2L-1)2^j
              =B-H0+2^(2L)-3<B-2,

and 0<V<B-2. Thus F(2)=V as integers. This does not yet permit
binary uniqueness because d0 may exceed one. Instead, nonnegativity
shows that e has no digit of degree K or higher: any such digit
would contribute at least 2^(L+K)>V. Thus e<B^K, and ell<e gives
ell<B^K. Consequently b ell<B^(K+1)<q, so k=0. Now every digit
is binary and uniqueness recovers ell=ell0(B),e=e0(B).

In particular theta ell<q, supplying Tplus<q^4 after decoding. This
does not justify using the packing lemma to obtain nonintersection
before decoding. The range dependency remains explicit.

## 3. The alphabet-four obstruction does not transfer unchanged

The family in `EXPLORATION_SHORT_FIRST_BLOCK.md` has

    B=s^2, H0=2^h, s=2^k,
    ell=1+2B^(L-1), e=ell+1, x=1, g=s-1, sigma=B.

With theta=B-4 it passes central-binomial divisibility despite T>=n
and a nonzero binary intersection. Substituting theta=B-2 does not
preserve that acceptance. The focused checker verifies ten such
substituted cases, with L=4,8,16,32,64 and k=h+4 or h+8, h=4L+8.
Each retains the product bound and floor(T/n)=1, but its central-
binomial valuation is strictly below 2 log2(n). Those candidates
fail the narrow binary binomial test.

The finite search `../../tmp/search_binary_short_packing.py` also
considered ell=a q/B+d0 with a=2..12,d0=0..8,e-ell=1..4, several
small power-of-two radices, C up to four times sqrt(B), and selected
positive x<C. It found no instance with the product bound, T>=n,
binary overlap, and the required binomial valuation. These toy
thresholds and finite searches prove no general rigidity claim.

The narrow binary packing may behave differently from its alphabet-
four predecessor. Its complete range argument is unresolved here.
Independently, both direct schedules above still cost 90, so neither
improves the current bound even if that range argument can be supplied.
