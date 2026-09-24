# Single offset and a common exponent witness: 102 operations

This note proves that two changes to the verified 104-operation system
compose: the coefficient encoding in `SINGLE_OFFSET_ENCODING_PROOF.md`
saves one addition, and the exponent-target change in
`PELL_COMMON_WITNESS_PROOF.md` saves one multiplication. Together they
give 102 arithmetic instructions: 56 multiplications and 46 additions,
with 34 positive unknowns and 22 equality tests. Fixed numerals and
admissible supplied parameters are free.

The common-witness construction retains U=wN^2 and the first index
modulus UY from the 104-operation system. It does not use the distinct
U=Bw construction in `PELL_SHARED_EXPONENT_PROOF.md`. Neither parity
of R nor the modulus U(Q+1) is needed here.

## The two changes and the fixed index

Use the rebuilt fixed coefficient index of
`SINGLE_OFFSET_ENCODING_PROOF.md`, with the same modular Sidon support,
1832 row positions, K=t_*+1, L=2^32 and H bound. At each ordinary
row, including the guard u*delta-x^2, prescribe

    [T^(t_i)] D(T) C(T)^2=4F_i^h+delta^2;

retain delta^2 at the special row. Rebuild e0, Z and V from these
targets. No fixed index depends on the queried positive input x.

Replace the third block by

    S3=B*lambda*q-(Z*lambda-2e)*C^2,
    Omega=Z*lambda-2e>0, sigma=S3>0,

in place of its old offset B*lambda*(1+q). Retain C=x+g, B=Hb^2,
Y_code=ell+e*q, the geometric equation, Y_code+alpha=q^2 and
Y_code=V+t*theta. The packing remains

    S=g+q^2*(Y_code+q^2*S3),
    Tplus=q^2*(1+theta*lambda)-(b-1)*ell+(B-4)*ell*q^4,
    N=n=q^8,
    R=r=S*(N^2-N)+Tplus*(N^2-1).

Retain all unit-scale Pell definitions and equations:

    U=w*N^2, Y=s*N^2, a0=Y*(U+1), A=a0+4,
    Q=UY^2, P=2Q+1, J=2R+1,
    tau*(tau+1)=((UY)^2+U)*(Y*k)^2,
    k=R+1+h*(UY), c=kY+eta, k=eta+zeta.

Only the supplied-coordinate Pell equation E14 changes. Replace its
old exponent target bw by the already calculated U:

    d=U+c*(A-4)+gamma*(8A-17).                  (1)

## Sufficiency: preliminary bounds, then the common-witness Pell proof

The single-offset proof supplies, before using any Pell equation,

    B<=q^2, q>4b>=8,
    C^2<B*lambda*q<3q^3<q^4,
    0<S3<B*lambda*q<q^4,
    0<S<N, 0<Tplus<=N,
    N<=R<=2N^3-2N^2<2N^3.

These imply N,R>=64, U,Y>=N^2 and 3L<=B<=N<=R, exactly the
preliminary assumptions used by the common-witness proof. They do not
depend on E14 or on the old low offset. The exact-index arguments in
`PELL_UNIT_SCALE_PROOF.md` and `PELL_SHARED_RATIO_PRODUCT_PROOF.md`
therefore still give

    c=psi_A(J), d=chi_A(J), k=psi_P(R+1).

They use the signed block with c>J and the congruence modulo UY,
whose modulus exceeds R+1; they require no exponent relation.

Put xi=(U+1)^(2R)/U^R. The lower ratio estimate gives xi<c/k.
The interval then gives Y>=U^R and A>U^(R+1). The upper estimate
is justified by R<2N^3 and a0>N^4, and gives

    0<c/k-xi<32R/(U+1).

The changed first exponent has the required size bounds

    4^(3J)<=64*N^(2R)<=64*U^R<U^(R+1)<A,
    U^3<=U^R<A.

Thus (1) proves U=4^J. Only now is the ratio error bounded by 1/2.
Since N^2 is a positive divisor of U=wN^2, N is a power of two;
N=q^8 then makes q a power of two. This step does not yet assert
that b is a power of two.

The unchanged second index and exponent argument uses

    B^(3L)<=B^B<=N^N<=U^R<A,
    q^3<=N<=R<U^R<A

and gives q=B^L. Consequently B, and then b from B=Hb^2, are
powers of two. No first-mask binary decoding has been used before
this point. The binomial expansion has integer part F with

    0<xi-F<1/4, F=binom(2R,R) modulo U.

The interval and 0<c/k-xi<1/2 imply Y=F by integrality. Since
N^2 divides U by its unchanged definition and Y=sN^2, this gives
N^2 dividing binom(2R,R). All hypotheses for no-carry decoding
have now been established with the changed exponent target.

## Sufficiency: the changed coefficient decoding

After q=B^L, positivity of the new S3 gives

    Omega>Z*lambda/2, C^2<2Bq/Z<=Bq/2<q^2.

The first two masks and congruence recover

    ell=ell0+m*q, e=e0-m, 0<=m<e0,
    C<B^K, 2e*C^2<q.

They do not use E14 internally. The independent high-mask proof in
`HIGH_MASK_SINGLE_OFFSET_PROOF.md` therefore applies and forces
m=0 under the unchanged H bound. With e and ell canonical, the
raw coefficients below K are those of 2D*C^2 and have magnitude
less than B/4. Every incoming normalization carry is -1 or zero.

The special target has raw value 2delta^2 and mask digit B-4,
which allows exactly digits 0,1,2,3; hence delta is zero or one.
The guard excludes delta zero because x>0. With delta=1, each
ordinary target has raw value 8F_i^h+2. After adding the incoming
carry, the unnormalized value is 8F_i^h+1 or 8F_i^h+2. As proved
in the single-offset argument, the mask permits this value exactly
when it lies in [0,3], forcing F_i^h=0. This
recovers the represented system and proves sufficiency.

## Necessity: new code first, then new Pell witnesses

Start from a solution of the represented system. Use the canonical
single-offset construction, with delta=1, u=x^2 and zero dummy
coordinates, choosing b a sufficiently large power of two. Its
sigma is positive because

    S3=lambda(Bq-Z*C^2)+2e*C^2>0.

Every ordinary and special row has raw coefficient two and digit
one or two, so all third-mask tests pass. The first two masks pass
as before. Form the resulting S,T,R; they satisfy the packed
bounds and N^2 dividing binom(2R,R). The old R need not be preserved.

Now choose

    J=2R+1, U=4^J, w=U/N^2,
    Y=floor((U+1)^(2R)/U^R), s=Y/N^2,
    a0=Y(U+1), A=a0+4,
    Q=UY^2, P=2Q+1,
    c=psi_A(J), d=chi_A(J), k=psi_P(R+1).

The quotient w is positive integral: canonical N is a power of two,
and N^2<=R^2<=4^R<4^J=U. The binomial expansion and divisibility
make s positive integral. The same ratio estimates give
Y<c/k<Y+3/4, so eta=c-kY and zeta=k-eta are positive integers.
Choose tau=(chi_P(R+1)-1)/2 and h=(k-R-1)/(UY). Odd P gives
the positive integrality of tau. The Pell congruence modulo
P-1=2UY^2 and strict growth give that of h. No parity of R is
required.

All remaining dependent Pell witnesses are supplied by the generic
constructions in `PELL_COMMON_WITNESS_PROOF.md` at this A: positive
f,i for E16, G=1+(A+1)(f^2-1),

    o=(chi_G(J)+d)/f, j=(psi_G(J)-J)/c,
    kappa=psi_A(L), mu=chi_A(L),
    Delta=(kappa-L)/(A-1), phi=c-kappa.

Their congruences and strict growth give positive integers. The
exponent quotients are positive because d-(A-4)c>3c>U and
mu-(A-B)kappa>(B-1)kappa>q, using A>U^3,q^3 and J,L>=2.
Both moduli are positive. Thus every required positive witness is
constructed after the new packed R is formed, proving necessity.

## Exact arithmetic composition

The offset change deletes q+1 and uses P2=(B*lambda)*q. The
common-witness change deletes the separate product b*w and uses
the existing U=wN^2 in E14. It changes no other arithmetic
instruction or supplied-coordinate Pell equation.

These edits affect disjoint register definitions. They remove one
addition and one multiplication from the 104-operation schedule,
leaving 56 multiplications and 46 additions, or 102 total. The same
34 positive unknowns and 22 equality tests remain. The rebuilt
coefficient code affects only the fixed supplied parameters. The
complete composed schedule is checked independently of the
positive-domain proof given here.
