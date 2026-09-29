# One-sided bound after the affine radix: a bounded alias counterfamily

This note concerns the 94-operation shifted-affine system, equivalently
the actual-radix encoding in `AFFINE_RADIX_95_PROOF.md`. It tests the
specific proposed replacement

    ell+e+alpha=q   -->   ell+alpha=q.

That replacement would save one addition. It does not preserve the
encoding: the newly permitted high part of e becomes an arbitrary
correction to the tested third block. The construction below retains
bounded packed blocks; it is distinct from the older counterfamily
obtained by letting the entire packed integer grow without bound.
This note establishes the failure of the coding and binomial filters.
It does not claim a separately audited instantiation of every auxiliary
Pell witness for this changed system.

## Fixed canonical code and a short correction

Fix an admissible affine index and a positive input x. Choose a physical
code whose normalization coordinates have their intended values

    delta=delta'=1, X=Y=Z=x, u=x^2-1,

using the three-way forbidden-bit decomposition. Other logical circuit
values may be arbitrary nonnegative integers; no ordinary row equation
is assumed. Choose the power-of-two radix B sufficiently large for these
fixed values, the first mask, all raw-coefficient bounds, and both unit
padding tests. In particular, choose 7x^2<B. Write

    theta=B-4, q=B^L, n=q^8,
    lambda=(q^2-1)/(B-1), ell=ell_0(B), e0=e_0(B).

The canonical code has ell,e0<B^K, where K is one more than the last
tested position, and L>3K+2. Its packed residue is

    ell+e0*q=V+t0*theta,  t0>0.

The low coefficients of the canonical third block

    sigma0=(lambda-e0)(q-C^2)

agree with D(T)C(T)^2 throughout the tested positions. Every ordinary
three-digit window starts with carry zero, by the exact x^2 reset.
Write G_j for its integer raw target. We have |G_j|<B^3/64. At each
ordinary target t_j, including both signs of every zero equation, put

    a_j=(-G_j) mod B^3,  0<=a_j<B^3,
    M0=sum_j a_j B^(t_j).

The windows are disjoint, and M0<B^K. Adding M0 makes every ordinary
three-digit window zero: G_j+a_j is either zero or B^3. The outgoing
carry is therefore zero or one. In base-B coefficient form, the added
digits are at most B-1 and occur only in the three tested positions.
They do not fill either of the two empty positions immediately before
any later x^2 reset. The same reset argument therefore continues to give
zero incoming carry at the next target. The three unit targets need no
correction: their reset remains exact, and 7x^2<B makes both padding
carries zero. Their windows are (1,0,0). All low variable tests are also
unchanged because M0 has no support there.

We can impose the required congruence on this short correction without
altering any tested digit. Since B is a power of two greater than four,

    theta=4r0,  r0=B/4-1 odd,  gcd(B,r0)=1.

Choose k in {0,...,r0-1} so that

    m=M0+k B^(K+1) == 0 mod r0.

If a positive m is desired when this expression is zero, replace k by
k+r0. This changes only positions above all tests. We then have

    0<m<B^(K+3)<q/(4B).

The final inequality follows from L>3K+2, K>=2, and B>16. Because
4 divides q^2, this choice gives theta | m q^2.

## The alias is carried into the third block

Set

    e=e0+m q,
    t=t0+m q^2/theta,
    alpha=q-ell,
    Omega=lambda-e,
    sigma=Omega(q-C^2).

All these values are positive. For Omega, use

    e<q+q^2/(4B)<q^2/B<lambda,

where the middle inequality holds once q>2B, as it does here. The
coordinate code still has C^2<q. The weakened bound and the packed
congruence both hold exactly.

The second packed coordinate is now

    ell+e q=(ell+e0 q)+m q^2.

Thus normalization of the packed S gives

    S=g+q^2(ell+e0 q)+q^4(sigma+m).

The effective third coordinate is sigma+m. Its low tested digits are
those of sigma0+m, since

    sigma-sigma0=-m q(q-C^2)

has no contribution below position L. The high correction in m is above
all tests, and the preceding construction makes every ordinary target
window pass even if its original equation G_j=0 was false. Unit and
variable tests still pass. The first and second packed masks see their
original, valid canonical codes.

The range argument also survives this alias. In particular

    0<sigma<lambda*q<q^3,  0<m<q,
    0<sigma+m<2q^3<q^4.

The normalized first, second and third coordinates therefore still fit
their widths q^2,q^2,q^4. Tplus is unchanged, lies between zero and n,
and has the original three masks. Consequently the retained packed
coding conditions imply the same no-carry condition and central-binomial
divisibility for the newly computed, bounded integer r. This is not the
unbounded-r phenomenon in the earlier deleted-bound note.

## Consequence for the search

The operation saved by deleting e from the combined bound cannot be
claimed using the existing coefficient proof. The high part of e is
literally a free additive mask correction after block normalization.
The fixed-index congruence does not remove it: an untested high part of
m enforces that congruence while leaving every repaired target intact.
A valid shorter bound would have to exclude this specific alias or make
its block carry observable at lower arithmetic cost.
