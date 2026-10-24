# Signed-power bootstrap and transport absorption

Status: independently reviewed ordinary mathematical proof relative to the stated inherited results; not a kernel certificate. See review/MATHEMATICAL_REVIEW.md.
This contribution uses the complete source34 coefficient binding of incoming
structural-reductions integer41, not arbitrary coefficients satisfying its bounds.

## The candidate

Start with the literal Q41 residuals. Delete w_scale and its defining row
X=4q w_scale. Replace the global square row X=2u_old² by X=4q u².
Replace z by a new coordinate Z and its transport row by

    (K0 q+X)(q-F-alpha)-qF-Z(q-1)=0.

All other rows are unchanged, with q=beta J+1. This leaves 40 integer
variables and 25 residuals, one cubic and all others quadratic. The single
polynomial is their sum of squares. Its existence is equivalent to Q41
existence, though there is not a same-coordinate bijection of all witnesses.

## Preliminary estimates without a sign assumption on X

Retain the two F/alpha/C product guards and the eta*zeta guard. Write
C=q-F-alpha, Q=|q|, k=eta+zeta, s=2v_scale+1, Y=sq³,
a=(X+1)Y, E=XY, A=a+2, H=4a+3, Delta=A²-1.
The unchanged signed-radix packing proof gives Q>=16 and

    Q(Q²-1)<R<Q⁴-2.

It uses only the F/alpha/C guards and the actual source34 mask inequalities,
not X, eta or the transport. The two signs eta,zeta agree and are nonzero.
Thus k!=0 and 0<|eta|<|k|. Also |Y|>=Q³. If u=0 then X=0,
a=Y and D=ac+gamma H. The main norm modulo H gives H|1, contradicted by
|H|>=4Q³-3>1. Consequently u!=0, X!=0, sign X=sign q and

    x=|X|>=4Q, Z0=|Y|>=Q³, |E|>=4Q⁴>3R+1.

Let c0=|c|, k0=|k|. The row c=kY+eta gives
k0(Z0-1)<c0<k0(Z0+1), hence c0>k0.
Set B=|A|. In either sign of X, B>= (x-1)Z0-2>R and B>=2.
Let P0=|2XY²+1|. Then P0>B.

## Recovering the ranks before the power sign

The ordinary consecutive-product Pell classification gives

    |tau|=chi_P0(n), k0=2 psi_P0(n), n>=1,
    |D|=chi_B(p), c0=psi_B(p), p>=1.

For X<0 apply the usual classification with positive consecutive-product
parameter -XY²-1, since XY²(XY²+1)=(-XY²-1)(-XY²).
Since P0>B and c0>k0, monotonicity implies p>n.

Put eps=sign(k) if X>0, and eps=sign(k)(-1)^(n-1) if X<0.
The recurrence psi_b(n) equals n modulo |E| for b=1 modulo |E|,
and equals (-1)^(n-1)n for b=-1 modulo |E|. Therefore the index row
k=R+1+hE gives

    2n = eps(R+1) modulo |E|.

For eps=+1, n>=(R+1)/2. For eps=-1,
2n>=|E|-R-1>2R, hence n>R. In either case p>n>=24.
Pell growth gives c0>B(B²-1)², c0>2p and c0>2R.

The unchanged ordinary strong-rank lemma now applies to
(i c²)²=Delta(f²-1), i=2r+1!=0. It gives |f|=chi_B(m),
p|m, c0|m and m>2p. The unchanged signed auxiliary step-down applies to
V=of-c=jc-R and its norm. Its proof uses c² and congruences modulo c0,
so neither sign c nor sign A enters. It gives R=+p or -p modulo c0.
Since 0<p,R<c0/2, p=R.

Thus eps=-1 is impossible, because that branch had p>n>R. For eps=+1,
p>n and |E|>3R+1 show both 2n and R+1 are positive and less than |E|.
They are equal. Hence R=2n-1 is odd. This derivation does not assume X>0.

## Excluding the negative X branch

Assume X=-x<0. Write r0=n-1=(R-1)/2>=1, Z0=|Y|.
Now P0=2xZ0²-1 and B>= (x-1)Z0-2. The elementary recurrence estimates

    psi_B(2r0+1)>=(2B-1)^(2r0),
    psi_P0(r0+1)<=(2P0)^r0

imply c0/k0 > (x-3)^r0/2. The needed base inequality is explicit:

    (2(x-1)Z0-5)²-(x-3)(4xZ0²-2)
      =4(x+1)Z0²-20(x-1)Z0+25+2(x-3)>0

for x>=64, Z0>=5. Since c0/k0<Z0+1,
Z0>(x-3)^r0/2-1>2^(2r0+1)=2^R. The last inequality follows already
from x-3>=61 and r0>=1. In particular

    |H|>=4(x-1)Z0-3 > x 2^R+1,
    x+2^R<|H|.

Use the Pell polynomial identities modulo the odd integer H=4a+3:

    chi_A(R)-a psi_A(R)=2^R modulo H,
    chi_A(R)+a psi_A(R)=2^(-R) modulo H.

The inverse exists since H is odd. The second identity follows from the
first and chi_A(R)²-Delta psi_A(R)²=1, with Delta=a² modulo H.
As R is odd, psi_A(R)=psi_B(R) and chi_A(R)=theta chi_B(R),
where theta=sign A. Put sigma=sign c and delta=sign D.
Multiplying D-ac=X modulo H by sigma gives either

    sigma X=2^R modulo H, or sigma X 2^R=-1 modulo H,

according as sigma delta theta is +1 or -1. The inverse case is impossible:
its left side has absolute value x 2^R strictly between 1 and |H|-1.
The direct case, using x+2^R<|H|, forces sigma X=2^R literally, so
x=2^R. But q divides X, and sign q=sign X<0, hence q=-2^t for some t>=0.
The fixed q=1 modulo 2^d-1, d=1064921>=3, forbids this: reducing t modulo d
shows the residue of 2^t is among 1,2,...,2^(d-1), never -1 modulo 2^d-1.
Contradiction. Therefore X>0 and q>0.

## Soundness and completeness

For X>0 the eps sign above is sign k, so eps=+1 gives k>0 and consequently
eta,zeta>0. We have X>=4q, |Y|>=q³, the original main/strong/auxiliary
norms, and the required index gap. The existing positive-X signed-Y proof
(PROOF44 sections 5--7, or Q41 restored positive-eta branch) therefore
recovers Y>0 and X=2^R. That proof used X=2u_old² only to establish X>0;
its subsequent Pell and compiler reasoning uses exactly the displayed
inequalities and equations. Alternatively, after recovering X=2^R and
odd R, restore a literal Q41 witness by setting

    w_scale_old=u², u_old=2^((R-1)/2), z_old=Z/q.

The last quotient is integral: the cleared transport modulo q gives
Z=0 modulo q because q|X and gcd(q,q-1)=1. Dividing the transport by q
restores the original row. All other Q41 rows are unchanged. Q41 soundness
then supplies a finite ZFC refutation.

Conversely canonical Q41 witnesses have q=2^t, t odd, R odd,
R>3q and X=2^R. Thus R-t-2 is a nonnegative even integer. Choose
u=2^((R-t-2)/2), and Z=q z_old. Then X=4qu² and the cleared transport
holds. Keep the other canonical coordinates. This proves completeness.

The source coefficients and no consistency assumption enter these recipes.
The stated equivalence is formalizable in ZFC using the same explicitly
inherited native compiler/calibration and Pell lemmas as Q41.

## The 34-integer sextic

First change the Pell root coordinate by tau_old=tau_tail+P-k.
Then eliminate these six coordinates by monic equations:

    P=k+E(c-eta), F2=f², g=y²-V²,
    N=q(L+1), C2=c², X=D-ac-gamma(4a+3).

The first norm becomes tau_tail²+(2tau_tail-k)E(c-eta)-1.
Every surviving residual has degree at most 3. There are 34 integer
variables and 19 residuals. The row I-(2r+1)c² is the only row involving r;
its square has coefficient 4 at r²c⁴. Hence the sum of squares has exact
degree 6 after the authentic coefficient specialization. Every elimination
has an integer-polynomial inverse, so it preserves integer solvability.

The new mechanism is not merely monic projection: signed-power bootstrap
and modular transport recovery first remove a genuine quantified scale.
The subsequent projection is routine. The standard octic projection yields
30 integers, matching rather than improving the incoming octic30.
