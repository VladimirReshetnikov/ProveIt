# Optional eleven-variable degree 1140 companion

This is a separate Pareto companion to the main degree 1154/123-operation
construction. It has eleven strictly positive unknowns, product degree 1140
and 129 operations, or a shifted two-equation system with residual degrees
2,1138 and 124 operations. The main construction and its generator are
unchanged. The optional circuit adds six gates and uses the same four fixed
compiler payloads.

Retain every definition in `ELEVEN_POSITIVE_PROOF.md`, and replace only the
carrier by

    sigma=M(ell+2c-X)-b,
    W=L b0+H(E(t+sigma)+k-R-1).

In other words this is the main polynomial after the substitution
t_old=t+sigma. It is a polynomial substitution without division. Positivity
of the new supplied carrier needs both directions of proof, supplied below.

## 1. Positivity of sigma for soundness

The final mod4 unit guard is unchanged by the carrier substitution. Thus
any new product root gives Nt=1 and all outer bounds of the main proof. In
particular X=wq>=16, Y>3q^4, k=eta+zeta>=2, c=kY+eta, and q>=16.
Write C=Cstar, Z=s0 q^2=Y/q, and B=ell+2c-X. Certainly B>0, since
ell=XkY^2>X.

The exact identities E=XY and X/q=w>=1 give

    C ell-Delta c
      =[2EX+(w-1)Y^2-4E-4Y-3]c-EC eta
      =EY[eta(X-6-1/q)+zeta(2X-4)]-4E eta
        +(w-1)Y^2 c-(4Y+3)c
      >=EY[eta(X-7-1/q)+zeta(2X-4)]-(4Y+3)c.

Here the last step uses Y>=4 and w>=1. Since X>=16 and q>=16, both
coefficients in the square brackets are at least X/2.
Also c<k(Y+1) and (4Y+3)(Y+1)<8Y^2 for Y>=3. Therefore

    C ell-Delta c
      >kY^2(X^2/2-8) >=(k/3)X^2Y^2.

The bound C=XY+2X+2Y+Y/q<3XY/2 holds for X,Y>=16. Hence

    C B-Delta c > C ell-Delta c-CX
      >X^2Y(kY/3-3/2)>X^2Y>1.

Finally, expanding M and b gives

    sigma=2TI B+R i^2 c^3(C B-Delta c)-c-R>0.

For the last strict inequality it suffices to use c>=2,R>=1 and
R(c^3-1)>c. Every prospective new solution therefore supplies a positive
old carrier t_old=t+sigma. The main eleven-variable soundness theorem
applies verbatim. In particular no new assumption about k>E is inserted.

## 2. Completeness of the positive translation

For a canonical compiler witness the main construction chose

    t_old=L0 gamma+M tau+y-h.

Subtract sigma. With A0=a+2 and g=b0+Hgamma, the result is

    t=gamma+M[(tau-ell)-(A0 c-g)]+y+b-h.

The two square-root differences satisfy

    tau-ell=(ell k+1)/(tau+ell)>ell k/(2ell+k)>k/3,
    A0 c-g=(c^2-1)/(A0 c+g)<c/A0<2k/(X+1)<k/3.

Here tau<ell+k, ell>k, X>=16, and c<k(Y+1) justify each inequality.
Thus the bracket is positive. Also b>c>k>h for the canonical witness, so
t>0. The substituted carrier still gives exactly the same coherent zero
factor. This proves existence equivalence for both the product and system;
the inherited positive z shift is unchanged.

## 3. Exact degree and leading form

Use the predecessor's sixteen-linear-factor expansion, scaling all supplied
variables by lambda. It is

    N_old=d^8 H^16 product(t_old-y-M tau-L0 gamma),
    gamma=(g-b0)/H.

Before the eleven-variable absorption the sharp predecessor had degree 1056.
Define its homogeneous leaders

    B0=R0 E0^2 i^2 c0^4                 (degree 38),
    D0=R0 E0 Y0 i^2 c0^4               (degree 36),
    C0=R0 E0(s00 q0^2)i^2 c0^4         (degree 35),
    M0=R0 E0 i^2 c0^3                  (degree 27).

Here q0=beta J, k0=eta+zeta, s00=s+3q0,
X0=wq0, Y0=s00 q0^3, E0=X0Y0, and c0=k0Y0.
The predecessor factor degrees were four 35, two 36, and ten 38, with its
prefactor of degree 464. The correction sigma has degree 35 and leader C0.

Exactly two of the four degree 35 factors are improved: the branch with
g=+sqrt(G), tau=+sqrt(A), and y=-(b-vf)+O(lambda^-8), for each sign of f.
For these, after the substitution, the linear factor is

    t+M[ell-sqrt(A)+A0 c-sqrt(G)]-gamma-vf+O(lambda^-8).

The estimates in the Laurent field are

    sqrt(A)-ell=k/2+O(lambda^-9),
    A0 c-sqrt(G) has degree -1,
    gamma has degree -1, vf has degree 23.

Hence each of the two factors now has degree 28 and leading coefficient
-M0 k0/2. The opposite two degree 35 factors now have leader 2C0 and
retain their degree. The two degree 36 and ten degree 38 factors are
unaffected in highest degree because sigma has degree 35. Therefore

    degree(N_old translated)=464+2*28+2*35+2*36+10*38=1042.

Multiplying the nonzero leaders replaces the predecessor's C0^4 by
M0^2 k0^2 C0^2. Thus its new highest form is

    2^46 i^48 k0^96 w^74 s00^172 q0^636(q0-F)^16.

The eleven-variable carrier still introduces the factor E^16 and the
additional rational shift (k-R-1)/E of degree -2. That shift is below every
factor degree just listed and cannot alter these leaders. Thus

    degree(N)=1042+96=1138,
    N_1138=2^46 i^48 k0^96 w^90 s00^188 q0^700(q0-F)^16.

Multiplying by the unchanged degree2 transport factor proves exact product
degree 1140. These forms are nonzero for every authentic beta>0. The optional
checker verifies both complete univariate coefficient arrays over two
finite fields, obtaining degree 1138 for the norm and 1140 for the product,
and checks 60 independent formal conjugate products.

The new contribution here is only the displayed carrier translation, its
positive-domain proof, and the new degree certificate. All inherited
compiler and logical dependencies are the same as for the main equation.
