# Independent challenge of unequal-scale doubling identity/decrement conditions

**PASS, with no mathematical correction requested.** I read the full
146-line frozen author note `/tmp/markov_distinct_scale_fourier_boundary.md`,
SHA-256 `23e5c13ca92ce1522489c6a54a6905f184daf0023d0a39ef421bd14f911941ee`.
Its exact degree constraints, top-frequency-rank corollary and common
Laurent factor bound follow by all-size algebra. The final Section 4
clarification correctly preserves the valid identity-only example while
excluding the requested second decrement action on that space.

This is a proof-only challenge. No supplied, frozen or predecessor program
or source array is executed or imported. The task is a necessary-condition
theorem, not an existence proof or an arithmetic compiler construction.

## 1. Independently derived elimination

Use the author's convention

    T_a f = lambda f,       T_a g = lambda g,
    T_b f = mu f,           T_b g = mu(g-f),

where f,g are independent real finite trigonometric polynomials, the
normalized doubling masks are continuous and strictly positive, and
lambda,mu are distinct positive real scales. Their difference can have
either sign; the degree and divisibility arguments do not assume its
positivity. Put z=exp(2 pi i x), and write F(z),G(z)
for the corresponding Laurent polynomials. Let E_F,O_F be their full
even and odd parts, and similarly for G; thus O_F contains the original
odd powers of z, without decimation. Put F2=F(z^2), G2=G(z^2).

Normalization gives the exact identity

    (T_a f)(2x) = E_F(z)+(a(x)-1)O_F(z).

Let c=mu/(lambda-mu), which is nonzero. Subtracting the two masks' actions
on F and G and cross-multiplying yields

    F2 O_G-G2 O_F = c F2 O_F.                       (1)

Eliminating the first mask instead gives

    E_F O_G-E_G O_F = lambda*c F2 O_F.              (2)

There is no division by a possibly vanishing circle value in either
identity. The operator equations imply them pointwise on the circle;
finite Laurent polynomials equal there are identical polynomials.
Only the scales' nonzero and unequal hypotheses are used in these
algebraic identities.

F is nonconstant. Otherwise normalization would force both lambda and
mu to be 1. G cannot be constant either: its nonzero constant value would
force lambda=1, while the positive normalized doubling maximum principle
makes every continuous real fixed function constant, contradicting the
independence of f,g. Finally O_F and O_G are nonzero. For any nonconstant
finite trigonometric eigenfunction at a nonzero eigenvalue, an identically
zero odd part would make the doubling operator halve the largest frequency,
contradicting that eigenfunction equation.

## 2. Degree cancellation checked explicitly

Let Fdeg,Gdeg be the largest positive Fourier exponents of F,G, and let
p,q be their largest positive odd exponents. Realness makes the negative
support endpoints exactly -Fdeg,-Gdeg and -p,-q. In particular p,q>=1;
one-sided complex Laurent functions are not being silently included.

The right side of (2) has largest exponent 2Fdeg+p, with nonzero leading
coefficient. The left side has largest exponent at most Fdeg+Gdeg.
Consequently Gdeg>Fdeg.

In (1), the term G2 O_F has degree 2Gdeg+p, strictly greater than the
right side's degree 2Fdeg+p. Therefore it must cancel against the leading
term of F2 O_G, and necessarily

    2Fdeg+q = 2Gdeg+p.

Since q<=Gdeg, this gives Gdeg<=2Fdeg-p<2Fdeg. Fdeg cannot be odd:
then p=Fdeg and the same inequality would contradict Gdeg>Fdeg.
Thus Fdeg is even and E_F has that exact degree.

Now E_G O_F has degree at most Gdeg+p<2Fdeg+p. In (2) it cannot cancel
the nonzero leading term on the right. Hence E_F O_G has exact degree
2Fdeg+p, forcing Fdeg+q=2Fdeg+p. Combining the two displayed equalities,

    Fdeg=2m,  Gdeg=3m,  q=p+2m,  1<=p<=m,

for some integer m>=1. Since p is odd, when m is odd the odd top degree
Gdeg=3m forces q=3m and p=m. When m is even, p<m and q<3m.

Every leading-term comparison above either uses a strict degree inequality
or explicitly requires cancellation of two equal top degrees. No generic
noncancellation assumption is used. The negative endpoints are supplied
by realness; the possibly negative constant c cannot make any stated
nonzero product coefficient vanish.

## 3. Laurent divisibility and support width

Factor F=H P and G=H Q in C[z,z^-1], with P,Q coprime. Substitution
z->z^2 preserves coprimality: a Laurent Bezout identity for P,Q remains
one after that substitution. Equation (1) therefore implies

    P(z^2) divides O_F(z).

For a nonzero Laurent polynomial, define its width as the largest
exponent minus the smallest. Widths add under multiplication, because
the top and bottom coefficients of a product cannot cancel. Substitution
z->z^2 doubles width, and realness gives width(O_F)=2p. Thus

    width(P)<=p,
    width(H)=width(F)-width(P)>=4m-p>=3m.

The author's odd-decimation convention gives the same conclusion directly.
For `O f(w)=sum_j f_(2j+1) w^j`, one has
`O_F(z)=z O f(z^2)`. Its endpoints are (-p-1)/2 and (p-1)/2,
so width(O f)=p. This decimated polynomial need not itself be real-valued
on the circle; it inherits a symmetry centered at exponent -1/2, not 0.
Cancelling the common H in the decimated version of (1) shows that the
reduced numerator of f/g divides O f.

Laurent units are nonzero constants times integral powers of z. They
do not affect widths or the asserted lower bound. The gcd need not be
chosen as a real-valued circle function for the argument to work.

## 4. Limits

These conditions exclude small degrees and Laurent-coprime coordinate
pairs. They do not prove that the surviving degree patterns and large
common factors admit continuous strictly positive masks. Conversely they
do not exclude every independently scaled pair. Mask positivity and
continuity remain necessary, particularly at circle zeros when a mask
is recovered from a quotient.

This does not contradict the existing mixed sine/cosine identity-only
example, or the common-scale identity/decrement exclusion. It concerns
the full actions on a common two-dimensional finite trigonometric space;
an action imposed only on a single state line is a different interface.
No finite arithmetic test is used as evidence for an all-size conclusion,
and no paid integer operation or universal-bound saving follows.

I also checked the author note's additional assertion 0<lambda,mu<1:
normalization and positive averaging make each operator a contraction in
the supremum norm, and the shared nonconstant eigenfunction excludes
eigenvalue 1 by the maximum principle. In the fixed-function proof, all
2^n preimages of a maximizer are maximizers because every averaging weight
is strictly positive; their union is dense. No unproved irreducibility
claim is being substituted for this argument.

For Corollary 1, a rank-two top-frequency projection from the
two-dimensional real space is injective. It would force every nonzero
vector, including the common eigenvector, to have the largest space
frequency, contradicting M_f<M_g. Since the space has a nonzero top
frequency, its projection cannot have rank zero. Thus the surviving rank
is exactly one, independently of the presentation of the space.

The author note's rational-mask argument is also valid: the two rational
expressions for a-1 agree away from finite zero sets on the circle and
therefore agree as rational functions. Cancelling a common numerator/
denominator factor does not change their orders at infinity. My separate
derivation in Section 2 obtains the same degree relation directly from
(1), and does not rely on that division.

The previously read common-scale note is pinned at
`baf4667547145049a6e2a842f6c337e25b4a075a7ea18c81bfa22ebd07b7e063`;
the earlier pure-harmonic note is pinned at
`6f370b742f1fb5126a17677fb8ef7eb05a61f8cd0ebbcbb8b42f53bb2915c731`.
Their roles are limited to the operator interface and the explicitly
retained scope boundaries; the new algebra is given here. No external
literature or finite computational evidence is needed for this review.
No repository or Git mutation occurred. This review is proof-only and
has no executable or numerical receipt.
