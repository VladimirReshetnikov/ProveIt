# Two centered equations in twelve unrestricted integers

## Status and provenance

These are exact polynomial coordinate changes of the two scalar-carrier12
equations at ProveIt commit `84e16e43092614bae262ca59651cb9d77e31a255`.
The new theorem is an explicit bijection of the entire integer zero sets.
The unchanged ordinary native/compiler/refutation theorem of those parents
therefore transfers. No new encoded derivation inside object-ZFC, Lean
endpoint, or global minimality result is claimed.

Centering itself is already used elsewhere in the repository. The new
contribution here is its application to the current scalar four-root
carrier, together with complete circuits and exact degree certificates.
This is an incremental improvement, not a claim of a new general method.

The unknowns, all in Z, are j,C,z,h,r,v,w,T,c,n,t,s. The fixed six-port tuple
is exactly `mixed-parity-unrounded-1064921`; its complete gzip payloads are
included. In particular beta=2^1064921-1, cone_A=2^1113 and
cone_B=2^666104. MF is already shifted by beta. The supplied source34 recipe,
943 tiles and exact K215 seed reconstruct and compare every coefficient.
No port is borrowed from a different tuple.

## 1. Complete polynomial specification

The prefix abbreviations are the following polynomials. They introduce no
additional unknowns.

    J=6j+1, q=beta*J+1, W=12w+4, X=qW, Y=(2v+1)q^3,
    E=XY, a=E+Y, H=4a+3, Delta=a^2+H,
    F=(K0+W)C-z(q-1),
    R=(q(q-F)-C)(q^2-1)+(MC+qMF)J,
    k=R+1+hE, eta=c-Yk, zeta=k-eta,
    G=(cone_A F)(cone_B C)-(q-cone_A F-cone_B C)^2,
    Pair=G eta zeta-(t^2-G-eta zeta+1)^2,
    Dg=(3Pair-4)s^2+1,
    I=src^2, Df=1+Delta I^2, Q=Delta^2 I^2, delta=Q-1,
    V=Df(c-R+4IT)-c, Cy=QV^2-1,
    ell=XY^2, Dt=1+ell(ell+1)k^2,
    K=X(X+2ac)-1, S=IH^5,
    zc=HT+K, Ac=(zc^2+3H^2)(zc^3-19H^3).

Write F16(z;u1,u2,u3,u4) for the product, over all sixteen sign choices,
of z-epsilon1*sqrt(u1)-epsilon2*sqrt(u2)-epsilon3*sqrt(u3)-epsilon4*sqrt(u4).
Sign invariance makes this an ordinary integer polynomial in its five
arguments. Each radicand has exponent at most eight. Define

    ra=9S^2 Df, rb=81S^2 Dt, re=729S^2 Dg.

The two new equations are

    P_R=delta^8 F16(S(n+V)-Ac; ra,rb,re,S^2 Cy/delta)=0,
    P_I=F16(S(n+delta V)-Ac; ra,rb,re,S^2 delta Cy)=0.

P_R is defined by symbolic denominator clearing as a polynomial, including
at delta=0; it is not evaluated by division. The complete literal DAGs in
`rational_centered.json` and `integral_centered.json` use only integer
constants, addition, subtraction and multiplication. Their norm tail is
specified below as another entirely polynomial definition.

For a center Z, arguments ra,rb,re, numerator cn, and d=delta (P_R) or d=1
(P_I), form

    t20=Z^2+re, t21=-2Z, ab=ra+rb,
    q0=d(t20-ab)-cn, q1=d*t21,
    tn=d^2*ra*rb, rn=d*cn,
    v0=q0^2+re*q1^2-4(tn+rn*ab), v1=2q0*q1,
    z64=64tn*rn,
    n0=v0^2+re*v1^2-z64*t20,
    n1=2v0*v1-z64*t21,
    P=n0^2-re*n1^2.

Here cn=S^2 Cy for P_R and cn=S^2 delta Cy for P_I. Expanding the
sixteen conjugates independently verifies all 495 coefficients of each
generic norm identity, before substituting any arithmetic prefix.

## 2. Exact zero-set bijections

Let P_R_old and P_I_old be the pinned parents with center S*n-Ac.
Every prefix polynomial is independent of n. Define triangular maps on Z^12
which fix eleven coordinates and change only n:

    T_R: n_old=n+V,             U_R: n=n_old-V,
    T_I: n_old=n+delta*V,       U_I: n=n_old-delta*V.

The unchanged values V and delta show that U_R T_R=T_R U_R=id, and likewise
for I, on every integer tuple. Direct substitution gives the universal
identities

    P_R(x)=P_R_old(T_R(x)),     P_I(x)=P_I_old(T_I(x)).

Thus each pair has bijective complete integer zero sets. There is no
positivity, nonzero, parity, divisibility, or polynomial-zero premise in
this argument. In particular it also covers all formally exceptional
values of delta and S; those branches remain whatever the parent proves
them to be. The nontrivial semantic work remains the parent's theorem,
retained in `parent/PROOF.md` and its named sources. Once that theorem is
composed, ZFC proves that absence of integer zeros of either new equation
is equivalent to syntactic Con(ZFC), with the same ordinary formalizability
scope as the parent. This is not a proof that either side is true.

## 3. Exact degree of P_R

All degrees in this section count only the twelve quantified coordinates;
the six fixed ports have degree zero. The prefix gives

    deg(S)=34, deg(V)=25, deg(delta)=32,
    deg(ra)=88, deg(rb)=102, deg(re)=114, deg(Ac)=45.

Set z0=S*n-Ac, so deg(z0)=45 and Z=SV+z0. Since
Cy=(delta+1)V^2-1, the crucial exact cancellation is

    delta Z^2-S^2 Cy
       =delta z0^2+2delta S V z0-S^2(V^2-1).

Its right side has degree at most 136. Therefore q0 has unique top part
delta_0 re_0 of degree 146; its other summands have degrees at most
136,134,122,120,118,68. Meanwhile q1 has degree 91 and top part
-2delta_0 S_0 V_0. Subsequent unique leading degrees are

| Register | q0 | q1 | tn | rn | v0 | v1 | n0 | n1 | P_R |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Degree |146|91|254|182|296|237|592|533|1184|

In particular v0 is led by re*q1^2, n0 by v0^2, and P_R by n0^2.
The entire highest homogeneous component is

    2^8 * 3^24 * S_0^16 * delta_0^8 * V_0^8 * Dg_0^4.

The prefix leading forms are

    q_0=6beta*j, X_0=12q_0*w, Y_0=2q_0^3*v,
    a_0=X_0Y_0, I_0=src^2, k_0=h*a_0,
    S_0=2^10*a_0^5*I_0, delta_0=a_0^4*I_0^2,
    R_0=-q_0^3*(12w*C-q_0*z), b_0=4I_0*T-R_0,
    V_0=a_0^2*I_0^2*b_0,
    Dg_0=-3s^2*Y_0^4*h^4*a_0^4.

Selecting the T^8 term in b_0^8 yields the following nonzero top monomial

    2^1256*3^796*beta^624
      *j^624*w^144*v^160*s^64*r^56*c^112*h^16*T^8.

Its exponent sum is 1184, and beta is the specified positive integer.
Hence the degree is exactly 1184 after fixing the actual coefficients.

## 4. Exact degree of P_I

Now Z=S*delta*V+z0, cn=S^2*delta*((delta+1)V^2-1), and d=1. The exact
cancellation is

    Z^2-cn=z0^2+2S delta V z0-S^2 delta V^2+S^2 delta.

Its unique leading term is -S_0^2 delta_0 V_0^2, of degree 150.
It dominates re,ra,rb in q0. Subsequent leading degrees are

| Register | q0 | q1 | tn | rn | v0 | v1 | n0 | n1 | P_I |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Degree |150|91|190|182|300|241|600|541|1200|

Here v0 is led by q0^2, n0 by v0^2, and P_I by n0^2. Its highest
homogeneous part is S_0^16 delta_0^8 V_0^16. Selecting the T^16 term
in b_0^16 gives the nonzero monomial

    2^1200*3^720*beta^576
      *j^576*w^144*v^144*s^80*r^80*c^160*T^16.

Its exponent sum is 1200 and its coefficient is positive for the actual
fixed beta. Thus deg(P_I)=1200.

## 5. Arithmetic cost and verification scope

Both domains have twelve unrestricted integer variables. In the declared
binary circuit model, fixed numeral leaves and shared registers are free;
each +,-,* gate, including scalar products and squares, costs one.

| Equation | Multiplications | Additions | Subtractions | Total | Exact degree |
|---|---:|---:|---:|---:|---:|
| Old rational parent |93|26|26|145|1200|
| New P_R |93|27|26|146|1184|
| Old integral parent |89|26|26|141|1456|
| New P_I |90|27|26|143|1200|

The rational shear adds one addition. The integral shear adds one
multiplication and one addition. P_I consequently evaluates a degree-1200
integer equation in two fewer operations than the old rational parent.
Within this historical four-equation comparison, the old 141/1456 point
has the fewest operations. The separate saturated 123/1084 equation in
`../integer12_saturated/` now improves both metrics of all four rows.

The independent verifier does not import the new producer. It checks the
entire parent-to-child output identity as a canonical expression DAG,
triangularity of the inverse maps, all live nodes and operands, separate
free-ring prefix formulas, all 495 generic norm coefficients, and the
literal q0 formula. The proved cancellation licenses a graded-lex exact
leading induction at every node, with the final coefficients shown above.
Every coefficient payload is authenticated and rebuilt from the complete
recipe. Deliberately corrupted center and final-norm signs are rejected.
Both ordinary and optimized Python checks pass. These computations verify
transcription and exact polynomial algebra; the unbounded semantic argument
is the coordinate-bijection proof and the inherited ordinary theorem.
