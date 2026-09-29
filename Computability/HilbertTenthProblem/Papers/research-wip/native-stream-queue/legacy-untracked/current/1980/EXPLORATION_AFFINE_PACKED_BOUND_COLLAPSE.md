# Returning to the packed bound discards every encoded equation

This note audits a specific attempted reduction from 94 operations to 93.
It replaces the combined bound

    ell+e+alpha=q

by the one-addition equation

    S2+alpha=q^2,  S2=ell+e*q.

The proposed operation saving is real, because S2 is already computed.
The resulting system is not universal in the intended sense: every
admissible index accepts every positive input. The construction below
preserves the bounded packing and gives all positive supplied witnesses.
It concerns this particular replacement, not all possible shorter bounds.
The frozen 94-operation system and article are unchanged.

## 1. Fixed index and code coordinates

Use the complete coefficient and support construction of
`AFFINE_RADIX_95_PROOF.md`. Its 94-operation fixed-index translation is
`SHIFTED_AFFINE_94_PROOF.md`. Write the actual radix as

    B=H+b+4=H0+1+b,

where the supplied H is H0-3 and H0 is the fixed power of two. Define

    P_j=(B^j-1)/(B-1), q=B^L, n=q^8,
    lambda=P_(2L), theta=B-4,
    e0=P_K+D(B), ell0=ell_0(B).

The fixed layout has K=t_max+3 and L>3K+2. The highest term of D is
the positive padding term B^(t_max-1). All other terms have smaller
degree: the last unit target involves delta at positive weight, its
reset is at t_max-3, and all other target intervals precede it. Hence

    m=D(B)>0, deg D=K-4, m<B^(K-3), theta*m<B^(K-2).       (1)

These bounds use the proved coefficients in {-1,0,1}, and B>16.

Fix any positive queried input x, without assuming membership in the
represented set. Choose B to be a sufficiently large power of two with
B>H0+1+x. Then b=B-H0-1 and beta=b-x are positive. Choose any logical
coordinate with its three distinct physical positions, and put

    z=B-1-x.

Assign those positions the three-way bit-clear decomposition of z from
the affine proof. Set all other encoded coordinates, including delta
and all dummy coordinates, to zero. These internal coordinates are
allowed to be nonnegative. The 34 supplied unknowns will still all be
positive. The coordinate polynomial now has

    C(1)=x+z=B-1,

so its actual value C=C(B)=x+g satisfies

    (B-1)|C,  (B-1)|C^2.                                  (2)

Every physical digit is below B and has its H0 bit clear; the input
satisfies x<b<B. The sum z is positive, so g>0. The true positions are
below K, giving C<B^K and C^2<B^(2K)<q. There is no requirement that
any internal equation, copy, guard, or unit row be true.

## 2. An exact quotient alias with unchanged middle coordinate

Supply instead of the canonical pair

    e=P_K, ell=ell0+m*q.                                   (3)

Both are positive, and

    ell+e*q=ell0+(P_K+m)q=ell0+e0*q.                       (4)

Thus the middle coordinate S2 is exactly canonical. In particular it
has base-B digits at most three, S2<q^2, and

    t=(S2-V)/theta>0

is the same positive integer as for the canonical code. Set
alpha=q^2-S2>0, Omega=lambda-e>0, and

    sigma=Omega(q-C^2)>0.                                 (5)

This satisfies the proposed packed bound and both retained positivity
equations. The fixed code e0 and all index parameters are unchanged.

## 3. Both parts of the third mask vanish against sigma

The entire low interval is now invisible. Since lambda-P_K is divisible
by B^K, equation (5) gives

    B^K | sigma.                                         (6)

The low mask theta*ell0 is below B^K: each indicator digit is one and
multiplication by theta=B-4 gives that same digit B-4 without carries.
It therefore has no binary intersection with sigma.

The high alias mask vanishes against sigma as well. Put

    A=C^2/(B-1),

an integer by (2). Since lambda*C^2=A(q^2-1), exact expansion gives

    sigma=q(lambda-P_K-Aq)+(A+P_K*C^2).                    (7)

The remainder is strictly between zero and q. Indeed A<C^2, P_K+1<B^K,
and C^2<B^(2K), so

    0<A+P_K*C^2<(P_K+1)C^2<B^(3K)<q.

Consequently

    floor(sigma/q)=lambda-P_K-Aq
                  =q(P_L-A)+(P_L-P_K).                   (8)

The residue modulo q in (8) is P_L-P_K, which has zero digits in
positions 0 through K-1. By (1), X=theta*m<B^(K-2). Hence

    floor(sigma/q) & X=0.

Finally theta*ell=theta*ell0+qX has disjoint low and high q-blocks.
Together with (6), this proves the exact third-mask condition

    sigma & (theta*ell)=0.                               (9)

Every ordinary row, every normalization equation, and all three unit
tests pass the mask because their tested digits are zero. In particular
the mask admits the deliberately chosen delta=0.

## 4. The other masks and bounded packing remain valid

The first mask also survives. Both b*ell0 and b*m are below q by the
support margin, so

    q^2-1-b*ell=(q-1-b*ell0)+q(q-1-b*m),                  (10)

with both parts nonnegative. Since g<q, only the low part matters.
Its digits at indicator positions are B-1-b=H0. All encoded digits
have that bit clear, and every other digit of g is zero. Therefore

    g & (q^2-1-b*ell)=0.

The middle mask holds because (4) is the unchanged canonical code.
Its mask theta*lambda has every relevant digit equal to B-4.

There is no unbounded-r escape in this example. Define S and T+1 by
the unchanged arithmetic expressions. We have

    0<g<q, 0<S2<q^2, 0<sigma<lambda*q<q^3,
    0<S=g+q^2*S2+q^4*sigma<q^7<n.

The first T-block in (10) lies below q^2, its middle block
theta*lambda lies below q^2, and its third block theta*ell is below
q^2, using (1) and L>3K+2. Thus

    0<T+1<q^6+q^4+q^2<q^7<n.

All three exact no-carry masks hold. The unchanged packing lemma gives

    n^2 | binomial(2r,r),
    n^2-1<=r<2n^3,
    r=S(n^2-n)+(T+1)(n^2-1).                              (11)

The inequalities 3L<=B<=n and B,q,n being powers of two hold as in the
canonical necessity construction. None depends on the internal rows.

## 5. All positive auxiliary Pell witnesses exist

For clarity, the remaining witnesses can be constructed after the r in
(11) has been determined. This is exactly the common-witness necessity
construction retained by Sections 27 and 29 of the article; its required
inputs are the ranges and divisibility in (11), the power-of-two data,
and 3L<=B<=n. It does not require the coefficient rows separately.

Write J=2r+1 and choose

    U=4^J, Y=floor((U+1)^(2r)/U^r),
    w=U/n^2, s=Y/n^2, a=Y(U+1), A_main=a+4,
    D_main=A_main^2-1, P=2UY^2+1.

The common-witness argument gives positive integral w and s from (11).
Take

    c=psi_(A_main)(J), d=chi_(A_main)(J),
    k=psi_P(r+1), tau=(chi_P(r+1)-1)/2,
    eta=c-Yk, zeta=k-eta, h=(k-r-1)/(UY).

The proved ratio and congruence estimates give eta,zeta,h positive
integers. Take the second main-base coordinates at L:

    kappa=psi_(A_main)(L), mu=chi_(A_main)(L),
    phi=c-kappa, Delta=(kappa-T_L)/a.

They are positive in these ranges. The two exponential congruences give
the positive integer quotients

    gamma=(d-U-ac)/(8a+15),
    rho=(mu-q-kappa*(A_main-B))
         /(D_main-(A_main-B)^2).

These are precisely the base-four and second-exponent necessity
estimates used for the unmodified system; their data satisfy every
original size hypothesis by (11).

Finally choose m_aux=2cJ, set f=chi_(A_main)(m_aux),
i_old=psi_(A_main)(m_aux)/c^2 and i=D_main*i_old. These are positive
integers by the doubled-index divisibility construction, and

    (ic^2)^2=D_main(f^2-1).

Put K_aux=D_main(f^2-1), G=2K_aux-1,
H_aux=psi_G(J), I=chi_G(J), and v=(I-1)/2. The same doubled-index
congruences give

    j=(H_aux-J)/c>0, o=(v+d^2)/f>0

as integers, with v(v+1)=K_aux(K_aux-1)H_aux^2. This supplies every
remaining positive unknown and every retained source equation. The
three exact triangular residual corrections in the certificate still
apply, because their source equations were retained without change.

Therefore every admissible fixed index and every positive x has a
positive solution after this proposed replacement, even for an index
representing the empty set. The proposed 93-operation count cannot be
accepted. A shorter bound must preserve more information than the
unchanged middle packed value alone.
