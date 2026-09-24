# Composition of the two 100-operation reductions

The system checked by `../verification/round26_1980_composed_certificate.py`
combines the coefficient construction of `HALF_CENTER_ENCODING_PROOF.md`
with the doubled-index Pell construction of `PELL_DOUBLED_INDEX_PROOF.md`.
It has 99 arithmetic operations: 55 multiplications and 44 additions,
with 34 positive unknowns and 22 equations. Fixed numerals are free.
The supplied inputs are `(x,V,H,Tindex)`, where the three fixed index
components satisfy `Tindex=psi_4(L)` for an underlying exponent L.
This is an existential representation theorem; it asserts no optimality.

The two changes affect distinct parts of the arithmetic circuit, but
their composition also needs a positive-domain proof: the new coding
bootstrap must supply every hypothesis of the new Pell argument, and
the resulting exponent and binary radix must justify the new decoding.
This note verifies that order in both directions.

## The combined admissible index

Use the entire index construction in `HALF_CENTER_ENCODING_PROOF.md`.
Compile the represented system into primitive arithmetic gates with
distinct copied operands and fresh outputs. Pair the multiplication,
addition, copy, final-equality, and zero rows with their negatives.
For each unit coordinate X use the two unpaired rows

    X*delta-delta^2,       X*delta-X^2.

Include the unpaired guard `u*delta-x^2`. For every ordinary row F
take the coefficient target `2F+delta^2`. Put the special target
`delta^2` FIRST. All divided target coefficients belong to
`{-2,-1,0,1}`.

With m positive-weight coordinates, give them weights `3^i` for
`0<=i<m`, putting delta at weight one. The input x has weight zero.
If s is the number of targets, put

    M=3^(m-1), d_0=4M+1,
    t_j=(s+1)d_0+2M+j*d_0,       0<=j<s,
    t_last=2s*d_0+2M, K=t_last+1,
    c_*=m+s+1.

The last count includes the dummy row coordinates and input. Choose
an underlying power of two `L>3K+2`, form the complementary coefficient
polynomial D(T), and define

    ell_0(T)=sum_i T^(3^i)+sum_j T^t_j,
    e_0(T)=2*sum_(0<=j<K) T^j+D(T),
    V=ell_0(4)+e_0(4)*4^L.

Choose a power of two

    H>max(2*4^(2L+1),4^(t_last+3)*4*c_*^2,3L,16).

Finally supply `Tindex=psi_4(L)` instead of L. These rules define the
admissible triple `(V,H,Tindex)`. They use the revised, paired target
list throughout: V and H are not inherited from an earlier unpaired
index. All choices depend on the represented set and are independent
of the queried positive input x. The underlying L is needed to define
admissibility and prove the theorem, not as an additional system input.

## Combined equations

Keep the coding equations and packing of the half-center construction:

    B=H*b^2, C=x+g, b=x+beta,
    lambda*(B-1)=q^2-1, theta+4=B,
    S2=ell+e*q=V+t*theta, S2+alpha=q^2,
    Omega=2lambda-e>0,
    sigma=theta*lambda*q-Omega*C^2>0,
    n=q^8,
    S=g+q^2*(S2+q^2*sigma),
    Tplus=q^2*(1+theta*lambda)-(b-1)*ell+theta*ell*q^4,
    r=S*(n^2-n)+Tplus*(n^2-1).                 (1)

These capitalized expressions are charged abbreviations. Omega and
sigma are the existing positive unknowns with equality tests.

Use the common Pell definitions

    U=w*n^2, Y=s*n^2, a=Y*(U+1), A=a+4,
    D=A^2-1, Q=U*Y^2, P=2Q+1, J=2r+1.

The first Pell norm and interval remain

    tau*(tau+1)=Q*(Q+1)*k^2,
    c=k*Y+eta, k=eta+zeta,
    k=r+1+h*U*Y.

The norm is computed using the already shared product Yk and the
identity `Q(Q+1)k^2=((UY)^2+U)(Yk)^2`. Retain the main norms,
the common exponent equation, and the gap:

    d^2=1+D*c^2, f^2=1+D*(i*c^2)^2,
    d=U+a*c+gamma*(8a+15),
    c=kappa+phi,
    mu^2=1+D*kappa^2,
    mu=q+kappa*(A-B)+rho*(2AB-B^2-1).

Use the two changed equations of the doubled-index construction:

    v=o*f-d^2, K_aux=D*(f^2-1),
    v*(v+1)=K_aux*(K_aux-1)*(J+j*c)^2,
    kappa=Tindex+Delta*a.                      (2)

The register v may be signed; it is not a positive unknown. Every
supplied unknown, including o, remains positive.

## Bootstrap before either code or exponent is decoded

From (1), `e<q` and `ell<q^2`. Positive lambda and the geometric
equation give `B<=q^2`. The admissible bound on H gives

    q>4b>=8,       3L<=B<=n.

Positive Omega and sigma imply

    C^2<theta*lambda*q<B*lambda*q<3q^3<q^4,
    0<g<C<q^2,       0<sigma<q^4.

The possible first-block borrow is fewer than b, whereas the middle
block has `theta*lambda>=B-4>b`. The half-center proof therefore gives
the width-(2,2,4) ranges, without using any coefficient condition:

    0<S<n,       0<Tplus<=n,
    n<=r<=2n^3-2n^2<2n^3.                      (3)

In particular `n>=64`, `U,Y>=n^2`, and `UY>=n^4>r+1`.
The first-index equation and interval give `k>r+1` and `c>J`.
Also `A>n^4>J`. Thus `A>1`, `1<J<c`, and odd J are available before
the new auxiliary norm is used. This supplies every initial hypothesis
of `PELL_DOUBLED_INDEX_PROOF.md`.

## Main Pell index and the underlying exponent

The unchanged main and auxiliary norms classify
`c=psi_A(p)` and `f=chi_A(m_aux)`. The doubled-index proof applies
to (2): `c|m_aux`, `0<2p<=c<=m_aux`, and its signed chi step-down
gives `J=+/-p mod c`. The minus case is excluded by odd J and
`psi_A(p)=p mod2`. Consequently

    c=psi_A(J),       d=chi_A(J).               (4)

Nothing in that proof uses the coefficient target values, the old
factor `4lambda-2e`, or an already decoded value of q.

The first Pell norm, its unchanged congruence modulo UY, and (3)
now identify `k=psi_P(r+1)` by the same growth argument as in
`PELL_SHARED_RATIO_PRODUCT_PROOF.md`. For

    xi=(U+1)^(2r)/U^r,

the unchanged lower ratio bound gives

    xi<c/k<Y+1,       Y>=U^r,
    a=Y(U+1)>U^(r+1).                         (5)

These facts justify the first chi-congruence criterion and yield
`U=4^J`. Since `n^2|U`, both n and q are powers of two. Moreover
`r+1>3`, so (5) proves the stronger bound on the actual new modulus:

    a>4^(3J).                                 (6)

The gap and second main Pell norm give
`kappa=psi_A(t_0)` with `0<t_0<J`. Admissibility and (3) give
`3L<=B<=n<=r`, hence `L<J`. Reducing the last equation of (2)
modulo a, using `A=a+4`, gives

    psi_4(t_0)=psi_4(L) mod a.

For `1<=t<J`, both positive values are bounded by
`psi_4(t)<=8^(t-1)<4^(3J)<a`. They are therefore equal as integers,
and strict Pell growth gives `t_0=L`.

The second exponent criterion has the same bounds as before:

    B^(3L)<=B^B<=n^n<=U^r<A,
    q^3<=n^n<=U^r<A.

It follows that `q=B^L`. Thus B and b are powers of two. The upper
ratio estimate remains valid because it uses U,Y and (3), which have
not changed. After `U=4^J`, its error is below one-half; the binomial
expansion therefore identifies `Y=floor(xi)` and gives

    n^2 | binom(2r,r).                         (7)

This completes both exponent decodings and the Kummer hypothesis
before any internal circuit residual is tested.

## The half-center decoding hypotheses are all restored

Now `lambda>q` and `e<q`, so `Omega=2lambda-e>lambda`.
Equation (1) gives `C^2<theta*q<Bq<q^2`, hence `g<C<q`.
Together with the binary radix and (7), these are precisely the
post-Pell hypotheses of `HALF_CENTER_ENCODING_PROOF.md`.

That proof first removes the first-block borrow and applies the
base-four evaluation lemma, obtaining

    ell=ell_0(B)+a_alias*q,
    e=e_0(B)-a_alias,       0<=a_alias<e_0(B).

The first mask bounds all code coordinates by b. Since x and g are
positive, `C(1)>=2` before delta has been recovered. With
`A_C=C(1)^2<(c_*b)^2`, the modified high window bounds each digit
of `(B-4)*a_alias` by `2A_C+4<=4A_C`. The displayed admissible H
bound removes this alias by evaluation at four. This step uses only
the new paired-layout values of c_*, K, and L; their required
inequalities were explicitly included in the combined index.

The special target is first, so its incoming carry is zero and its
raw coefficient delta^2 forces delta in {0,1}. The guard excludes
delta=0 because x>0. At delta=1, each ordinary row tests
`F in {0,1}`. Paired F,-F force F=0, and the two unit rows force
the unit coordinate to be one. The original circuit therefore holds
at the queried input. This proves sufficiency of the combined system.

## Necessity in an order preserving every positive unknown

Start with a solution of the represented system. Use its circuit
values, delta=1, u=x^2, and zero dummy coordinates. Choose b a power
of two larger than all coordinates and set B=Hb^2, q=B^L, n=q^8,
with the canonical e and ell. Then theta=B-4, beta=b-x,
lambda=(q^2-1)/(B-1), and alpha=q^2-(ell+eq) are positive integers.
The packed-congruence quotient t is integral by evaluation at four
and is positive because B>4 and the fixed digit polynomial has
positive degree. The half-center proof gives positive Omega and
sigma; in particular `Omega<2lambda` and `2C^2<theta*q`.

Every paired circuit target has F=0. The first special digit is one,
and all ordinary target digits are zero or one, so the three masks
hold. Define r by (1). Its ranges (3) hold and the Kummer criterion
gives (7).

Choose `J=2r+1`, `U=4^J`, and `w=U/n^2`, a positive integer since
n is a power of two and `n^2<=r^2<4^J`. Set
`Y=floor((U+1)^(2r)/U^r)` and `s=Y/n^2`. The binomial congruence
and (7) make s integral and positive. Define `a=Y(U+1)`, `A=a+4`,
`P=2UY^2+1`, and choose

    k=psi_P(r+1), c=psi_A(J), d=chi_A(J),
    tau=(chi_P(r+1)-1)/2,
    h=(k-r-1)/(UY), eta=c-kY, zeta=k-eta.

The unchanged common-witness estimates and congruences make all these
quantities positive integers. Choose

    kappa=psi_A(L), mu=chi_A(L), phi=c-kappa,
    Delta=(psi_A(L)-psi_4(L))/a.

Here `L<J`, so phi is positive; Delta is a positive integer by
`A=a+4>4` and `L>=2`. The two exponential congruences have their
positive quotients gamma and rho by the same common-witness necessity
proof. These choices depend only on the main Pell coordinates.

Finally choose the auxiliary coordinates anew, as permitted by the
doubled-index proof:

    m_aux=2cJ, f=chi_A(m_aux), i=psi_A(m_aux)/c^2,
    K_aux=(A^2-1)(f^2-1), G=2K_aux-1,
    I=chi_G(J), H_aux=psi_G(J),
    o=(I+2d^2-1)/(2f), j=(H_aux-J)/c.

The binomial Pell expansion gives `c^2|psi_A(m_aux)`, and even m_aux
makes f odd. The doubled-index congruences then make i,o,j positive
integers and prove (2). This final auxiliary choice changes none of
the preceding coding, interval, gap, or exponential witnesses.
Every one of the 34 unknowns has now received a positive integer
value satisfying the combined system.

## Arithmetic and source-level composition

The half-center replacement removes eight coding registers and inserts
seven, saving one multiplication. It changes only the packed equation,
positive-sigma equation, and positive-Omega equation; its geometric
test is an equivalent test using theta+4=B.

The doubled-index replacement changes the auxiliary norm and fixed
index congruence, and removes the unused affine Pell parameters. It
saves one addition. It touches none of the seven new coding registers
or their equation tests. The renaming from L to Tindex changes no
coefficient arithmetic: L occurs as an input only in the fixed Pell
index equation, which this replacement changes explicitly.

After renaming the input L to Tindex, only the zero-based source rows
6, 16, 19, 20, and 21 change. The two sets of changed rows are disjoint.
The arithmetic certificate verifies both orders of substitution, every
primitive, all 22 source residuals, and their three exact triangular
corrections. The changed geometric test depends on the equation
theta+4=B; that equation is used first in the mathematical proof, so
the fact that its equality test is listed later creates no dependency
cycle. Thus
the 101-operation fixed-four certificate loses one multiplication and
one addition, giving exactly `55+44=99` operations with unchanged
arity. The preceding proof establishes the positive-domain and index
claims separately from that symbolic arithmetic verification.
