# A spectral restriction on every carry-free scalar convolution layout

The finite-period obstruction in
[the guarded-layout note](native_controller_single_field_guard.md) extends
to layouts that allow within-cell wrap, provided the actual arithmetic
equation is still proved to hold coefficient by coefficient without carry
terms. The only exceptional fixed multipliers give affine wire equations.
This supplies a precise boundary for the proposed one-field compiler; it
does not exclude deliberate carries or another equation with an additional
variable field.

## 1. Statement

Fix L>=1 and a polynomial K(Z) with integer coefficients. For arbitrary
N>=1 put T=L*N, and let S denote cyclic shift of a real vector u of
length T. The entries of u may in particular be digits constrained by
any fixed mask of period L. Fix an L-periodic forcing vector lambda.
Suppose, for an arbitrary integer h, that

    (K(S)+S^(L*h)-I)u=lambda.                            (1)

The equation here is coefficientwise. For an integer source
(K(R)+R^(L*h)-1)U=lambda_word*J_B modulo(R^T-1), this premise must be
proved by actual coefficient bounds or another valid argument. Integer
equality by itself does not assert(1).

Let A(Z)=1-K(Z), and form the Laurent polynomial

    G(Z)=A(Z)A(Z^-1)-1.                                 (2)

If G is nonzero, there is an effectively computable positive multiple P
of L, depending only on K and L, such that every solution of(1) has bit-
or digit-position period dividing gcd(P,T). In particular it has a cell
period dividing gcd(P,T)/L, bounded by P/L independently of N and h.

If G is zero, then necessarily

    1-K(Z)=epsilon*Z^a, epsilon in{1,-1}, a>=0.           (3)

In this exceptional case(1) is exactly a system of affine wire equations

    S^(L*h-a)u=epsilon*u+S^(-a)lambda.                  (4)

Each position has one predecessor and one successor. The equation does
not impose a multi-input local gate. This is a structural description,
not a separate general decidability or universality theorem for every
possible input and endpoint extension of the wire family.

## 2. Fourier proof and an explicit uniform bound

For every T-th root of unity zeta, cyclic shift has a one-dimensional
complex eigenspace with eigenvalue zeta. On this mode(1) reads

    (K(zeta)+zeta^(L*h)-1)*u_hat(zeta)=lambda_hat(zeta).

Because lambda has period L, its Fourier coefficient is zero whenever
zeta^L!=1. If such a mode occurs in u, its multiplier must vanish, so

    zeta^(L*h)=1-K(zeta)=A(zeta).

The left side has modulus1. The coefficients of A are real and
conjugate(zeta)=zeta^-1, hence G(zeta)=0. This necessary condition is
independent of h. Thus every mode of u has either order dividing L or
is a root-of-unity zero of the fixed polynomial G.

Multiply G by a sufficient power of Z to make it an ordinary nonzero
integer polynomial g, and let D be its degree. If D=0, there are no
zeros and take P=L. Otherwise every root of unity of order n that is
a zero of g has cyclotomic degree phi(n)<=D. The elementary bound

    phi(n)^2>=n/2

therefore gives n<=2D^2. To check that bound, use the multiplicative
identity phi(n)^2/n=product_(p^a||n) p^(a-2)(p-1)^2. Every odd-prime
factor is at least1; the only factor below1 can be p=2,a=1, contributing
1/2. Consequently a valid, deliberately coarse bound is

    P=lcm(L,1,2,...,2D^2).                              (5)

Alternatively factor g cyclotomically and take the lcm of L and the
orders that actually occur. All frequencies of u have order dividing
both P and T, so u has period gcd(P,T). Since P and T are multiples
of L, this period consists of an integral number of cells. The claim
also covers repeated polynomial roots: cyclic shift itself is
diagonalizable, so no generalized-eigenvector issue arises.

Finally, to prove(3), suppose a and b are the smallest and largest
exponents of a nonzero A. If b>a, the coefficient of Z^(b-a) in
A(Z)A(Z^-1) is the nonzero product of its extreme coefficients. Thus
G cannot vanish identically. If a=b, write A=cZ^a; then G=c^2-1,
which vanishes precisely for c=1 or c=-1. The case A=0 gives G=-1
and belongs to the nonexceptional theorem. This proves the complete
classification of the exceptional multipliers.

## 3. Compiler consequence and boundary

In the nonexceptional case any local property of a cell repeats with
the bounded cell period. A unique Start cell therefore forces

    N<=P/L.

The ordinary bridge W=2^b*B^(2x)<B^N then bounds x as well. Neither a
larger finite digit alphabet nor a different periodic bit mask changes
the spectral argument. It requires only the coefficientwise linear
equation and the periodic fixed forcing.

Actual carries are a substantive escape from this theorem. If an
integer equality yields coefficients of the form

    (K(S)+S^(L*h)-I)u=lambda+(R*S-I)c,

with a variable carry stream c, the right side need not be L-periodic.
Its Fourier coefficients cannot be discarded, and the proof above no
longer applies. A successful one-field construction of this form must
either prove the needed computation using such carry states or change
another stated premise. Treating carry coefficients as uncharged or
unconstrained garbage would not establish soundness.

## 4. Evidence

The [checker](native_controller_single_field_spectrum.py) constructs G
exactly, audits the exceptional classification, identifies all possible
root-of-unity orders up to the proved bound, and exhausts small bounded
digit words. It compares actual modular integer equations to all
coefficient equations under a verified residual bound and checks the
fixed spectral period on every nonexceptional admitted tuple. The
exceptional cases are checked against their exact affine wire relation.
The [receipt](native_controller_single_field_spectrum.json) is replayed
by default. Independent full proof, source, and default-replay review passed.
This is an obstruction
packet and does not improve the complete universal bound76.
