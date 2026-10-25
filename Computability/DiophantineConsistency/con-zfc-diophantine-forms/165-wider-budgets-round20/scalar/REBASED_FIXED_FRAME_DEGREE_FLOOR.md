# Exact restricted degree-298 minimum in the rebased frame

Fix the eleven coordinates, authentic numerical tuple, rebased front
k=R+1+h XY^2 and Budget6=Y^2 B0-k^2q^6, and all other scalar registers.
For any nonzero constant integer radical weight L and any integer polynomial
center Psi in the ten coordinates other than n, set

    Z=S(n+Psi)-Ac,
    pa=delta Z^2, pb=delta S^2 P, pc=L^2 S^2 B Df Cy,
    N=(pa+pb-pc)^2-4pa pb.

Then deg N>=298. The displayed L=32 compressed center attains298 in147
gates. This is not an operation-count minimum and is not a bound for other
carriers, guards, radical architectures, polynomial weights, coordinate
charts or arbitrary eleven-variable consistency equations. The old fixed
frame with q^8 still has its distinct restricted minimum300.

Let subscript0 denote the COMPLETE highest homogeneous form. Put

    q0=6 beta j, W0=12w, X0=q0 W0, a0=X0 v,
    F0=W0 C-q0 z, R0=-q0^3 F0,
    ell0=X0 v^2, k0=R0+h ell0,
    G0=(cone_A v F0)^2+(2q0 v^2)^2+(q0^3)^2,
    qstar=r a0^7 c^6,
    sstar=128s r a0 q0^15,
    pstar=s ell0^2 k0^3.

The old assertion k0=R0 is NOT used in this frame: both terms have degree5.
Direct highest-form propagation gives

    (Budget6)0=-k0^2 G0,        degree16,
    Dt0=ell0^2 k0^2,           degree18,
    P0=-pstar^2 G0,            degree54,
    delta0=qstar,              degree28,
    S0=sstar,                  degree20,
    deg Ac=35, deg(B Df Cy)=136.

All forms named as nonzero are indeed nonzero in the actual polynomial ring.
In particular G0 is a nonzero sum of three real polynomial squares because
q0 is nonzero (the authentic beta is positive). The separate independent
highest-form checker verifies all23 full forms against the actual graph;
its rebased Budget support has24 monomials and P support has98.

Let d=deg Psi, with the zero center handled as d=-infinity. If d<54, then
deg Z<=73, deg pa<=174, deg pb=122, whereas deg pc=176. Therefore the
inner sum has degree176 and the cross term has degree at most296, giving
deg N=352. If d>54, then deg pa=68+2d>176 dominates, and

    deg N=136+4d>352,

because deg(4pa pb)=190+2d is strictly smaller.

For d=54 let psi0 be Psi's nonzero degree54 homogeneous part. Then

    pa0=qstar sstar^2 psi0^2,
    pb0=-qstar sstar^2 pstar^2 G0,
    (-4pa pb)0=(2qstar sstar^2 psi0 pstar)^2 G0.

The last expression is a NONZERO SUM OF REAL POLYNOMIAL SQUARES of degree298.
Put Hnorm=pa+pb-pc. If deg Hnorm<149, the cross term gives exact298; if
it exceeds149, its square gives a larger degree. At equality the degree298
part of N is

    (Hnorm0)^2+(2qstar sstar^2 psi0 pstar)^2 G0,

again a nonzero sum of real polynomial squares. It cannot vanish identically.
Thus in all cases deg N>=298. No zero of N, consistency assumption or
logical calibration is used in this finite polynomial lower-bound argument.
The degree298 proof and actual attained coefficient in PROOF.md establish
the matching upper bound.
