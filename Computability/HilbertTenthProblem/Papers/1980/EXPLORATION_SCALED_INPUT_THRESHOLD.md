# A scaled input threshold keeps the input bound but admits false codes

Review status: author and two independent complete proof/source reviews and
fresh verification runs passed without findings. The arithmetic and proof
are frozen; the published90 predecessor is unchanged.

The redesign considered here retains the positive numerical input bound
`b=x+beta` and every mask of the published binary90 construction. It
changes the radix to `B=M(b+1)`, where M is a fixed power of two. The
cheapest member, M=2, still costs **90 operations,48M+42A**, with34
positive unknowns and22 equations. It is unsound: one fixed genuine
empty coefficient code admits the false input x=2, with a complete
positive Pell extension.

For the explicit large-M implementation below, the threshold costs one
more multiplication and the total is91. This is a scoped ledger and
counterexample to this redesign, not a lower bound for all possible
compiler constants. The published90 sources are unchanged.

## 1. The redesign preserves the unit representation

Keep the product, input bound, packing, fixed code congruence, and Pell
blocks from [BINARY_PRODUCT_90_PROOF.md](BINARY_PRODUCT_90_PROOF.md).
Replace only the old affine threshold

    theta=H+b, B=H+b+2

by

    B=M(b+1), theta=M*b+(M-2).                    (1)

After B is decoded as a power of two, b+1 is a power of two. At each
indicator, the unchanged first mask has digit

    B-1-b=(M-1)(b+1).

Thus its allowed physical-coordinate digits are precisely those below
b+1. This is compatible with the logical unit delta=1. Given any finite
assignment, increasing b+1 allows the ordinary three-piece representation
to use `(z,0,0)` for every logical value z. Unlike setting the old forbidden
bit to1, this proposal does not force every physical coordinate to be even.

The fixed code polynomials can therefore retain their coefficient layout
and binary alphabet. What is lost for small M is the old independently
large fixed threshold on B. The example below shows why this matters even
though x<b<B is still enforced.

For general fixed M>2, the displayed implementation of (1) is

    threshold_product=M*b, theta_sum=threshold_product+(M-2),
    theta=theta_sum.

Both M and M-2 are fixed free numerals. These two operations replace the
old single addition H+b, giving91=49M+42A. No claim of optimality is made
for this implementation. For M=2 the zero offset disappears and one may
use `theta_sum=b+b`, giving the same90=48M+42A as before. The input
addition `bx=x+beta` and its comparison with b remain intact.

## 2. The actual fixed empty coefficient code

Apply the published binary coefficient compiler to an inconsistent
finite system, for example its ordinary added constraint

    2 delta delta_copy=0.

The compiler's unit and copy constraints make this system impossible
for every positive input. Let ell0,e0 be its actual binary indicator and
coefficient polynomials. Choose its fixed power-of-two L larger than the
published support bounds and at least16. The retained fixed indices are

    V=ell0(2)+2^L e0(2), Tindex=psi_2(L).          (2)

Their actual numerical values need not be materialized. Because both
code polynomials have zero constant coefficient and degree below L,

    0<V<2^(2L), V is even, L is even.             (3)

These facts hold for the genuine empty compiler code, not merely for an
illustrative polynomial with convenient residues. The redesign keeps
these two indices; the original fixed H is replaced by the fixed M=2.
The construction in the next section works for every V satisfying (3),
so it applies in particular to the actual value (2). The selected input
x=2 is not in the represented empty set.

## 3. Exact positive coding coordinates at B=8

Set

    B=8, b=3, theta=6, x=2, beta=1,
    q=8^L, n=q^8, lambda=(q^2-1)/7.

Choose the following fixed small exponents using the residue of the
actual V:

| V modulo6 | v | s |
|---:|---:|---:|
| 0 | 1 | 5 |
| 2 | 1 | 6 |
| 4 | 2 | 5 |

Define

    ell=g=8^v, e=ell+8^s, C=x+g,
    sigma=8^s C^2, alpha=q-ell-sigma,
    S2=ell+e*q, t=(S2-V)/6.                     (4)

Since L is even, q is4 modulo6. Substituting the three exponent pairs
shows that S2 has exactly the indicated residue modulo6. Also
S2>q>2^(2L)>V. Hence t is a positive integer and

    ell+e*q=V+t*theta

holds for the actual fixed V. Every other coding coordinate in (4) is
positive. Indeed v<=2, s<=6, s+2v<=9, and

    C<2*8^v, sigma<4*8^9<8^10.

With L>=16 this gives alpha>0, ell<q, e<q, C^2<q, and sigma<q.
The unchanged product and original combined bound are exact:

    sigma=(e-ell)(x+g)^2, ell+sigma+alpha=q.

The numerical input constraint is also exact: b=x+beta=3. This is not
an input-gap deletion or an input spilled into a high coordinate.

## 4. All three complete masks and the packed bounds

Use the unchanged definitions

    S=g+q^2*S2+q^4*sigma,
    Tplus=q^2*(1+theta*lambda)+ell*(theta*q^4-b).

The exact normalized mask is

    Tplus-1=T1+q^2*T2+q^4*T3,
    T1=q^2-1-3ell, T2=6lambda, T3=6ell.          (5)

The first two mask blocks fit below q^2 and the third below q^4.
Likewise g<q^2, S2<q^2, and sigma<q^4. These are actual block ranges,
not assumptions about normalized carries.

The first mask passes because g has its only nonzero base-eight digit1
at position v, whereas T1 has digit `7-3=4` there. The middle mask has
the uniform base-eight digit6 in all2L positions. Both ell and e have
only digits0/1, so S2 has zero binary intersection with it. Finally,
sigma is divisible by8^s with s>v. The third mask is supported only at
position v, so its intersection with sigma is zero. Thus

    g&T1=0, S2&T2=0, sigma&T3=0,
    S&(Tplus-1)=0.                              (6)

The bounds above give S<q^5. Also (5) gives
Tplus<q^4*(1+6ell)<q^5. In particular both are strictly between0 and
n=q^8. Define

    r=S*(n^2-n)+Tplus*(n^2-1).                  (7)

Then n^2-1<=r<2n^3, and the retained bounded binary packing lemma
applied to (6) gives

    n^2 divides binom(2r,r).                    (8)

Both S and Tplus are even, so r is even. All eight coding/packing
equations of the complete source have now been satisfied by positive
coordinates, including the original strong product and input bounds.

## 5. Complete positive Pell extension

The small radix intentionally violates the old hypothesis3L<=B. That
hypothesis was needed in the old soundness order. It is not required
to construct the new positive Pell witnesses: here q=B^L is already
an exact identity and

    B^(3L)=q^3<n, n>=64, n<=r, 2<=L<2r+1.

Together with the powers of two, even r and (8), these are sufficient
for the explicit necessity construction in Section6 of
[BASE_TWO_PELL_90_PROOF.md](BASE_TWO_PELL_90_PROOF.md). In detail choose

    J=2r+1, U=2^J, w=U/n^2,
    Y=floor((U+1)^(2r)/U^r), sP=Y/n^2,
    a=Y(U+1), A=a+2, E=UY, P=2UY^2+1,
    c=psi_A(J), d=chi_A(J), k=psi_P(r+1).

The exact binomial tail and (8) make w,sP positive integers. The strict
ratio estimates give positive eta=c-kY and zeta=k-eta. The published
formulas give positive integral tau and h. Even r makes J equal to1
modulo4, so the retained relaxed and half-parameter construction gives
positive i,f,o,j,y_aux with its required signs.

Set kappa=psi_A(L), mu=chi_A(L), phi=c-kappa and
Delta=(psi_A(L)-psi_2(L))/a. Their integrality and positivity use L>=2,
A>2 and L<J, all available. The fixed index is exactly (2). The two
exponent congruences supply integral gamma and rho. Their positivity
follows from

    d-a*c>c>U,
    mu-(A-B)*kappa>(B-1)*kappa>q.

In particular A>q^3 and A>B, so the second modulus is positive and
the displayed estimate applies. No new decoding assertion is being
used here; these are canonical Pell choices at the already specified
B,q,L,r. Every remaining supplied unknown is positive. This constructs
a complete positive solution of all22 redesigned equations at the
false input x=2 for the genuine fixed empty code.

## 6. Source verification and the finite evidence boundary

[explore_scaled_input_threshold.py](../verification/explore_scaled_input_threshold.py)
builds the complete changed90 DAG. It states the22 new source polynomials
by the exact substitution `H=(M-1)b+M-2`, verifies every comparison and
all three inherited acyclic corrections, and checks that `b=x+beta`
has not changed. The M=2 histogram is48M+42A with34 positive unknowns
and the three supplied parameters x,V,Tindex. The separate explicit
large-M schedule is checked as91=49M+42A.

The numerical regression uses24 cases: four even exponents L and six
positive even V values per exponent, including all three residues modulo6
and values near the upper limit in (3). Each evaluates the actual prefix,
all eight coding equations, every complete mask, the exact packed index,
its central-binomial valuation via popcount, parity, and all stated
conditions needed by the positive Pell construction.

These finite V values illustrate the uniform construction. They are not
claimed to be the enormous actual empty compiler index in Section2.
That fixed-index application and the full positive Pell extension are
proved above; no enormous auxiliary tuple is materialized. The result
refutes this small-M threshold redesign while leaving other compiler
constants and the universal90-operation frontier open.
