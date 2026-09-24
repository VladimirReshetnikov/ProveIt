# A smaller auxiliary Pell parameter: 92 operations

The universal system with the fixed index and encoding of
`FACTORED_MASK_93_PROOF.md` admits a 92-operation variant. The new
certificate has 49 multiplications and 43 additions, 35 positive
unknowns, and 23 equations. Its supplied inputs remain
`(x,V,H,Tindex)`, with three fixed index components besides the
queried positive input. Fixed numerals and equality tests are free.

Only the auxiliary signed-index block changes. Its old ten-operation
check is replaced by a nine-operation block with one additional
positive unknown `y_aux` and one additional equality. The change is
not an identity map on auxiliary witnesses: `o` and `j` are chosen
anew, and `y_aux` is added. The remaining canonical witnesses and
every fixed index component can be kept.

## 1. The new equations

Retain the definitions

    J=2r+1, A=a+4, D=A^2-1,
    R=i*c^2, K=R^2.

In particular retain the relaxed auxiliary equation

    R^2=D*(f^2-1).                                      (1)

The old signed equation was

    v*(v+1)=K*(K-1)*(J+j*c)^2, v=o*f-d^2.

Replace it by

    u=J+j*c,
    u=c+o*f,                                           (2)
    K*(u^2-y_aux^2)=1-y_aux^2.                          (3)

Here `u` is an arithmetic register, not another supplied unknown.
The old unknowns `o,j` and the new unknown `y_aux` are positive
integers. The last equation is equivalently

    (R*u)^2-(R^2-1)*y_aux^2=1.                          (4)

Thus its ordinary Pell parameter is R, whereas the old signed
equation used the doubled parameter 2R^2-1. Neither R*u nor that
larger parameter has to be constructed by the new certificate.

## 2. The preliminary bounds do not use this block

The full preliminary argument in `AFFINE_RADIX_95_PROOF.md`, carried
unchanged through the two later arithmetic improvements, gives

    n=q^8, n>=64, n<=r<2n^3, 3L<=B<=n,
    U=w*n^2, Y=s*n^2, a=Y*(U+1), P=2U*Y^2+1,
    U,Y>=n^2, U*Y>r+1, a>J, c>J>1.                     (5)

It uses positivity, the combined gap ell+e+alpha=q, and the geometric
and packing equations, before coefficient decoding or either
auxiliary signed norm is used. Classification of the retained main
and first Pell norms gives positive indices p and t with

    c=psi_A(p), d=chi_A(p), k=psi_P(t).

The retained first-index equation yields t>=r+1. Since P>A and the
positive interval gives c>Y*k>k, Pell growth forces

    p>=r+2>=66, c>A*D^2.                                (6)

These are precisely the independent hypotheses of
`PELL_RELAXED_AUXILIARY_PROOF.md`. Applying that result to (1) gives
a positive auxiliary index m such that

    f=chi_A(m), p divides m, c divides m,
    R=D*psi_A(m).                                       (7)

The relaxed-norm proof uses neither the old nor the new signed-index
equation. It follows from (6), elementary Pell growth, and (7) that

    0<2p<=c<=m, R=i*c^2>=c^2>A>1.                      (8)

In particular, R is an integer Pell parameter greater than one.
No exact value of p, no conclusion q=B^L, no parity of r, and no
decoded circuit equation has been assumed at this stage.

## 3. An odd-index polynomial identity

Use the standard Pell sequences defined by

    chi_X(0)=1, chi_X(1)=X,
    psi_X(0)=0, psi_X(1)=1,
    z(n+2)=2X*z(n+1)-z(n).

For every h>=0 there is an integer polynomial Q_h(T) such that

    chi_X(2h+1)=X*Q_h(X^2).                             (9)

The doubled-step recurrence and its initial values are

    Q_0(T)=1, Q_1(T)=4T-3,
    Q_(h+2)(T)=(4T-2)*Q_(h+1)(T)-Q_h(T).                (10)

For clarity, the doubled-step recurrence follows by applying the
ordinary recurrence twice, or by using
chi_X(2)=2X^2-1 in the addition identities. Thus (9)--(10) prove
polynomial divisibility by X; they do not require division modulo
any integer.

The odd subsequence psi_A(2h+1) has the recurrence with coefficient
4A^2-2 and initial values 1 and 4A^2-1. Consequently the sequence
(-1)^h*psi_A(2h+1) has recurrence coefficient 2-4A^2 and initial
values 1 and 1-4A^2. Substituting T=1-A^2 in (10) gives exactly
these same data. Induction proves the integer-polynomial identity

    Q_h(1-A^2)=(-1)^h*psi_A(2h+1).                     (11)

Setting T=0 in (10) similarly gives

    Q_h(0)=(-1)^h*(2h+1).                              (12)

Both identities are valid for every nonnegative h. They will be
used with two different moduli.

## 4. Sufficiency: recover the exact main index

Suppose all new source equations have positive integer witnesses.
By (4), positivity of R,u,y_aux, and R>1, the ordinary Pell
classification gives a positive index s with

    R*u=chi_R(s), y_aux=psi_R(s).                       (13)

The index s must be odd. Indeed, the ordinary chi recurrence at
R=0 gives chi_R(2h)=(-1)^h modulo R. An even s would make the
integer R>1 divide 1, contrary to R dividing the left side of (13).
Write s=2h+1. Equation (9) then gives the exact integer equality

    u=Q_h(R^2).                                        (14)

From (1),

    R^2=D*(f^2-1)=1-A^2 modulo f.

Equations (11), (14), and the new congruence in (2) therefore give

    (-1)^h*psi_A(s)=u=c=psi_A(p) modulo f.

Squaring this congruence and using the doubling identity

    chi_A(2z)=1+2D*psi_A(z)^2

gives

    chi_A(2s)=chi_A(2p) modulo chi_A(m).                (15)

We use the same chi step-down lemma as
`PELL_SIGNED_PROOF.md`: if A>1, 0<k<=m, and
chi_A(n)=+/-chi_A(k) modulo chi_A(m), then
n=+/-k modulo 2m. The plus-sign version also follows from the
ordinary step-down statement with its stronger modulus 4m.
Its comparison-index hypothesis here is exactly 0<2p<=m from (8).
Applying it to (15) yields

    2s=+/-2p modulo 2m,
    s=+/-p modulo m,
    s=+/-p modulo c.                                   (16)

The division by two is an integer operation on the equality
2s=+/-2p+2m*z; no division in an even residue ring is assumed.

Independently, c divides R because R=i*c^2. Equations (12) and
(14) imply

    u=(-1)^h*s modulo c.

The first equality in (2) now combines with (16) to give

    J=+/-p modulo c.                                   (17)

Both J and p lie strictly between zero and c: this holds for J by
(5) and for p by Pell growth. Thus either J=p or J+p=c. The latter
is impossible. The psi recurrence gives psi_A(p)=p modulo 2 for
every integer A, while J=2r+1 is odd. Therefore J+p has parity
opposite to c=psi_A(p). We have proved

    p=J, c=psi_A(J), d=chi_A(J).                        (18)

This argument did not assume r even. In particular it does not
depend circularly on the later binary decoding.

## 5. The remaining sufficiency argument and index are unchanged

Once (18) is known, the retained first-index and ratio argument
recovers the first index r+1, proves Y>=U^r and a>U^(r+1), and
uses the common-witness exponent equation to obtain U=4^J.
The fixed value Tindex=psi_4(L), together with the unchanged gap
and second Pell equations, recovers the second index L and q=B^L.
The same bounds give n^2 dividing binomial(2r,r).

These steps use exactly the hypotheses and conclusions listed in
`AFFINE_RADIX_95_PROOF.md`; the replaced auxiliary variables o,j
occur nowhere in them. In particular n^2 divides U, hence q and
then B are powers of two. Neither b nor H is required to be a
power of two. The unchanged masks recover the canonical codes,
the three-way physical coordinates, exact paired rows, and the
unit delta=1. They therefore recover the represented system at
the actual positive input x.

The supplied fixed index remains exactly the 93-operation index:

    H=H0-3, V=ell_0(4)+e_0(4)*4^L,
    Tindex=psi_4(L), B=H+b+4.

There is no new index parameter, compiler convention, or support
condition in the 92-operation construction.

## 6. Necessity: parity and positive auxiliary witnesses

Start with any solution of the represented Diophantine system.
Choose its canonical physical encoding and all positive coding
and Pell witnesses as in `AFFINE_RADIX_95_PROOF.md`, translating
the fixed index and retaining the factored packed mask as in the
94- and 93-operation proofs. All these choices are unchanged.

The canonical indicator ell has zero unit digit, so B divides ell.
The coordinate integer g also has zero unit digit, so B divides g.
Since B and q=B^L are even, the packed integers

    S=g+q^2*(ell+e*q+q^2*sigma),
    Tplus=q^2*(1+theta*lambda)+ell*(theta*q^4-b)

are both even. Their combination

    r=S*(n^2-n)+Tplus*(n^2-1)

is therefore even. It follows that

    J=2r+1=1 modulo 4.                                 (19)

Choose the same canonical relaxed auxiliary witnesses as before:

    m=2cJ, f=chi_A(m),
    i_old=psi_A(m)/c^2>0, i=D*i_old,
    R=i*c^2=D*psi_A(m), K=R^2.

Their integrality, positivity, and equation (1) are part of the
retained relaxed-auxiliary necessity proof. Keep these i,f and all
other canonical witnesses except o,j. Put

    y_aux=psi_R(J),
    u=chi_R(J)/R=Q_((J-1)/2)(R^2),
    o=(u-c)/f, j=(u-J)/c.                              (20)

The division defining u is exact because J is odd, by (9). Since
(J-1)/2 is even by (19), equations (11)--(12) give

    u=psi_A(J)=c modulo f,
    u=J modulo c.

Thus both quotients in (20) are integers. They are strictly
positive, as the following elementary growth estimate shows.

For R>1, the positive chi sequence is strictly increasing. Its
recurrence gives

    chi_R(k+1)>(2R-1)*chi_R(k) for every k>=1.

Since chi_R(1)=R and J>=3,

    u=chi_R(J)/R>(2R-1)^(J-1).

We have R>=c^2>A, and these are integers, so 2R-1>2A. The
ordinary psi upper bound now yields

    u>(2R-1)^(J-1)>(2A)^(J-1)>psi_A(J)=c>J.            (21)

Consequently o>0 and j>0. The new y_aux is positive as well.
The Pell equation for (chi_R(J),psi_R(J)) is precisely (4),
and hence (3), while the definitions in (20) give both equalities
in (2). Every other source equation is retained and uses none of
the replaced auxiliary values. All 35 supplied unknowns are thus
positive integers.

This proves necessity without asserting an identity map for the
old and new auxiliary coordinates. It also explains exactly why
the congruence J=1 modulo 4 is used only in this direction.

## 7. Exact arithmetic count

The former signed block used ten operations:

    of=o*f, v=of-d^2, vplus1=v+1, lhs=v*vplus1,
    Km1=K-1, Kprod=K*Km1,
    jc=j*c, u=J+jc, u2=u*u, rhs=Kprod*u2.

All four values d^2, K, c, and J already exist outside that block.
Replace it by these nine operations:

    jc=j*c,
    u=J+jc,
    of=o*f,
    u_rhs=c+of,
    u2=u*u,
    y2=y_aux*y_aux,
    difference=u2-y2,
    lhs=K*difference,
    rhs=1-y2.

The free equality tests are `u=u_rhs` and `lhs=rhs`.
The old block has six multiplications and four additions or
subtractions; the new block has five multiplications and four
additions or subtractions. No other primitive is changed. Thus

    93-1=92=49 multiplications+43 additions.

The variable d and its squared register remain in the main norm;
there is no further uncounted saving from their disappearance in
the auxiliary block. All new intermediates are ordinary integer
registers. In fact both `difference` and `rhs` are negative on
solutions: u=J+j*c>1 excludes Pell index one in (13), so y_aux>1,
and (3) gives u^2-y_aux^2=(1-y_aux^2)/K<0. Their subtractions
are represented by reversed addition equations.
No positivity assumption on those arithmetic intermediates is
introduced. The supplied variable y_aux itself is positive.

The checker writes the new source norm with
K_source=D*(f^2-1), and uses the already computed K=(i*c^2)^2
in the primitive product. Its residual difference is exactly

    (K-K_source)*(u^2-y_aux^2).

Here K-K_source is the independently exact retained auxiliary
equation (1). This is an acyclic correction, linear in that
equation, replacing the previous signed norm's quadratic-factor
correction. The new linear congruence check is exact without any
correction. The geometric and second-exponent corrections remain
exactly as before.

The complete checker is
`../verification/round35_1980_half_parameter_pell_certificate.py`.
Its adjacent JSON receipt records the full primitive schedule,
all 23 equalities, domains, source residuals, and remaining
corrections. Arithmetic verification is separate from the
universal argument and positive-witness construction above.

This proves an upper bound of 92. No optimality assertion or new
compiled Lean theorem is claimed.
