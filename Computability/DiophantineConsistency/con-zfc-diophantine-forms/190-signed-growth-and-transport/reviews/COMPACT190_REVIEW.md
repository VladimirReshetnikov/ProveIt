# Independent mathematical review of the degree-190 companion

Reviewed `agent_compact/result/PROOF.md`. Scope: the new transport, signed
polynomial center, positivity restoration, and exact degree decomposition.
The explicitly stated source-172 root, index, projector, and logical
calibration interfaces were treated as inherited hypotheses. I did not rerun
the exhaustive circuit checker, which the parent had already run.

**Conclusion: no mathematical defect found in the new reduction.**

## Transport

The auxiliary index-3 bound gives

    |b| >= 4 Delta f - (c+c3)/f > 4 Delta f - 1 > 3 Delta f,

because c3<=c and 2c<f. This calculation uses
Q=Delta(f^2-1), so the displayed correction is exactly c+c3, not an
unjustified asymptotic remainder. The identity

    (AUE)^2-G = E(U^2 E-1)>0

proves g<AUE directly. Combining y<(3/2)|V|,
|V|<(3/2)f|b|, and the signed center estimate gives

    4gy+|Omega| < (33/2)AUE f|b|
                < [11A/(2Delta)] UE b^2 < L/4.

The final comparison is exactly 22A<Delta=A^2-1, valid under the stated
A>1024. The argument therefore genuinely covers auxiliary index 3 and does
not import an index-5 or positive-B assumption.

## Signed center

Solving A=Yp(X+1)+1 for X in the polynomial identity reproduces the given
coefficients e2,e1,e0 of E. The bounds on e1 and e0 imply
E#<2E for delta=(Yp+1)/A<1/16. Applying the coefficient majorant to

    calF=(b-c)E+2U^2 b(A^2-1)E^2

gives the displayed bound on calF# even when b is negative. The inequalities
c+1<2U^2 E and |V|>Delta U^2 E|b| then yield

    calF#/|EV| < 8+20/Delta < 10.

The formal quotient by A^3 has even coefficients because the degree-two term
(b-c)E contributes nothing, while the remaining term has a factor 2. Thus
the center is an integer polynomial. The bound

    |Omega-4AUEV| < AUE|V|

follows from 20+5/A^2<A^2. It proves both the asserted sign of Omega and
its magnitude bound without assuming B,C,R,b, or V positive. Formal
polynomial quotients are not being confused with numerical floor division.

## Soundness and positive completeness

The estimate rho<|b|/q^7 is valid for either sign of R and b, since
b-(k-R-1)=cT-k+1>0. If B<=-1, then Wt<-L. The established transport bound,
positive kappa and sigma, and |b|/q^7<L/2 force n<0. Therefore B>=0 before
the source-172 arithmetic handoff. Integral Omega and W=1 modulo h preserve
the fractional carrier; multiplying the center by H also preserves its
reduction modulo H.

In completeness, the canonical source witnesses already satisfy the strong
and auxiliary norm equations, so the signed-center estimate applies before
constructing n. It gives Omega>0. The stated inherited bound
g>kappa+sigma+|rho|, together with y>=1 and t>=0, makes

    n=4gy+Omega+(1+hL)t+rho-kappa-sigma

strictly positive and integral. This is a fresh witness construction, not a
claim that the coordinate shear preserves positivity on arbitrary tuples.

## Degree

Expanding Z=Z0-M Omega gives exactly the stated five-term decomposition.
The component degrees independently agree:

    deg(Q,M,G,V,Z0,Omega,L)=(72,12,46,36,41,59,27).

Hence only Q M^2 Dnorm can contribute degree 190. Substituting the actual
highest homogeneous parts into the supplied free-ring defect identity gives

    [P]_190 = 9*2^11 q0^74 w^18 s^52 i^10 k0^32
              (q0-F)^2(w^2-6s^2).

In particular the coefficient of J^74 w^20 s^52 i^10 eta^32 F^2 is
9*2^11 beta^74, which is nonzero. This independently checks the composition
of the formal weighted leading part with the ten actual input coordinates;
it does not substitute a gate-degree upper bound for an exact degree proof.

This review is an independent AI-assisted mathematical check of the new
steps, not a human endorsement or a replacement for the inherited calibration.
