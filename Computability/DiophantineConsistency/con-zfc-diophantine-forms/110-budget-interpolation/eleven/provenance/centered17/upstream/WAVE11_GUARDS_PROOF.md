# Commuting native positivity and residue orientation

## Result and status

The explicitly bound polynomial packets in this directory give the following
ordinary mathematical reductions, relative to the named inherited unbounded
Pell, native compiler, and syntactic calibration results:

| Primary packet | Domain | Variables | Residuals | Exact degree |
|---|---|---:|---:|---:|
| determinant37_quartic_direct.json | all integers | 37 | 24 | 4 |
| determinant37_quartic_affine.json | all integers | 37 | 24 | 4 |
| determinant31_sextic.json | all integers | 31 | 18 | 6 |
| determinant26_octic.json | all integers | 26 | 13 | 8 |

Each polynomial is the sum of the squares of its listed residuals, with all
listed ports specialized to their actual fixed integer bytes. Integer-zero
existence is equivalent to the existence of a finite syntactic ZFC refutation
under those inherited results. Negating gives the corresponding
unsolvability/consistency statement. This is not a new kernel-checked theorem,
not a derivation in the repository's internal ZFC calculus, and not a claim
that the final internal consistency biconditional or native calibration has
been formalized. The latest repository pin is
2605669a532342f153b13eb6b4a0af4b54f5fa37.

The new contribution is the compatibility proof and exact composition of two
independent wave-10 restrictions, not a claim of discovering either restriction:
source 70's delayed residue orientation and source 71's determinant guard.
Source 69's weighted cone gives an independently checked alternative family at
the same counts. The inspected prior frontier was 38/4, 32/6, and 27/8, so
these compositions save one variable in each slice. No global minimum is claimed.

The determinant family is preferred because its six fixed integers occupy
615,883 minimal raw bytes, compared with 881,696 for the weighted-cone family.
This is only a coefficient-payload comparison, not a circuit-size or maximum
expanded-coefficient comparison.

## 1. Literal parent and coefficient binding

The literal parent is source 64's Q41 at
upstream/residue/dependencies/quartic41.json. Its four fixed ports are exactly
source 34's mixed-parity-unrounded-1064921 tuple. Set

    d=1064921, beta=2^d-1, q=beta J+1, C=q-F-alpha,
    Pos(x,y,z)=1+x^2+y^2+z(z+1).

MF is already shifted by beta. It must not be shifted again or replaced with
another tuple having similar numerical bounds. The authentic tuple obeys
beta>=17, 0<MC<beta<MF<2beta, K0>=0. The complete source34 builder, its literal
943 ordered tiles and K215 machine input are retained; build_coefficients.py
reconstructs all bytes and checks their inherited raw SHA256 values. No machine
halt or consistency oracle is used to construct the coefficients.

Every value of Pos is a strictly positive integer. Conversely every positive
integer n is Pos: Legendre's three-square theorem applied to 4n-3 yields one
odd and two even squares, giving that representation after division by four.

## 2. The joint modification

First delete the two rows F alpha=Pos and F C=Pos, and their six private
coordinates. Insert one row

    U V-(q-U-V)^2 = Pos(cone1,cone2,cone3),
    U=2^1113 F, V=2^666104 C.

These two new scales are fixed numerals, not quantified variables.
Keep eta zeta=Pos with its original three private coordinates.

Next delete X=2u^2 and its private variable u. For the direct quartic make
only the affine substitution

    X_old=3X3-1.

This leaves 41-6+3-1=37 variables and 26-2+1-1=24 quadratic residuals.
For a second quartic use instead

    J_old=3J3+1, w_scale_old=3w3+1,

with X retained. It has the same counts, and preserves a monic definition
of X for the sextic and octic projections. Since beta=1 modulo 3, this
form has q=2 modulo 3 and W=4(3w3+1)=1 modulo 3, so X=qW=2 modulo 3.
The direct form has X=2 modulo 3 by definition and does not need beta's
residue for its soundness.

## 3. Soundness of the determinant on arbitrary signed assignments

This step must precede all uses of canonical bounds. Write A0=2^1113 and
B0=2^666104, both at least two. At any new zero, UV>(q-U-V)^2>=0.
Thus U,V are nonzero and have the same sign. With W0=q-U-V,

    |W0|<sqrt(UV)<=(|U|+|V|)/2.

Consequently q has that same sign and

    |q|>(|U|+|V|)/2
         =(A0|F|+B0|C|)/2 >= |F|+|C|.

Since F,C have q's sign, alpha=q-F-C has that same strict nonzero sign.
Therefore F alpha>0 and F C>0. Both old Pos triples can be restored.
No positivity of q, X, or any particular source witness was assumed.

At this point the new zero has all arithmetic rows and common-sign
hypotheses required by source70's signed power-recovery lemma. The square
row is still absent: it must be recovered by the argument below, not used.

## 4. Signed power recovery before choosing an orientation

For completeness the unbounded argument is stated here. Detailed inherited
interfaces and the original derivation are retained in upstream/residue/PROOF.md.
Put

    Q=|q|, s=2v_scale+1, i=2r+1,
    Y=s q^3, X=qW, E=XY, k=eta+zeta,
    c=kY+eta, a=(X+1)Y, A=a+2, H=4a+3,
    Delta=A^2-1, D=X+ac+gamma H,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J_old.

The unchanged low-degree lift implies these identities and

    k=R+1+hE, V=of-c=jc-R.

The sign-free packing estimates from Q41 give

    Q>=16, Q(Q^2-1)<R<Q^4-2.

These estimates require only common signs of F,alpha,C and the authentic
mask inequalities, not X's sign. In the affine form W=12w3+4 never
vanishes and |W|>=4. In the direct form X=3X3-1 never vanishes; X=qW
therefore implies W=4w_scale is nonzero, again |W|>=4. Since s is odd,

    U0=|X|>=4Q>=64, Z0=|Y|>=Q^3>=4096,
    M=|E|=U0 Z0>=4Q^4>3R+1.

The retained eta*zeta guard gives one common nonzero sign. Let
K=|k|, eta0=|eta|, delta=sign(Y), sigma=sign(k), xi=sign(X).
Then 0<eta0<K and

    c0=|c|=K Z0+delta eta0,
    K(Z0-1)<c0<K(Z0+1), sign(c)=sigma delta.

Let B=|A| and P0=|2XY^2+1|. They satisfy

    B>=(U0-1)Z0-2>Q^4>R,
    P0=2U0 Z0^2+xi>B>=2, c0>K.

### Pell classification and rank bootstrap

The first and main norms are

    tau^2-XY^2(XY^2+1)k^2=1,
    D^2-(B^2-1)c^2=1.

Ordinary consecutive-product Pell classification supplies n,p>=1 with

    K=2 psi_P0(n), c0=psi_B(p).

For X<0 the first coefficient is m(m-1), m=U0 Z0^2>1; its positive
parameter is 2m-1=P0. Thus classification has not used X>0. Since P0>B
and c0>K, monotonicity forces p>n.

Modulo M the Pell recurrence gives psi_P0(n)=xi^(n-1)n. Hence

    sigma xi^(n-1) 2n = R+1 modulo M.

If the sign is positive, n>=(R+1)/2. If negative, 2n>=M-R-1>2R,
so n>R. In either case p>n>=24. Standard Pell growth now establishes
c0>B(B^2-1)^2, c0>2p, and c0>2R, which are precisely the size
hypotheses of the inherited ordinary strong-rank lemma.

The retained equation (i c^2)^2=(B^2-1)(f^2-1), with i odd and nonzero,
therefore gives |f|=chi_B(m), p|m, c0|m, m>2p. The signed auxiliary
step-down uses

    rho^2 V^2-(rho^2-1)y^2=1, rho=|i|c0^2,
    V=-c modulo |f|, V=-R modulo c0.

Its odd index ell is +/-p modulo m and +/-R modulo c0. The first
congruence is squared and therefore does not assume a sign for c.
Because c0|m, R=+/-p modulo c0. The strict bounds 0<R,p<c0/2 imply p=R.
The negative first-index branch, which would require n>R, is impossible.
In the positive branch 2n and R+1 lie below M, so

    2n=R+1; in particular R is odd.

### The sign-uniform ratio and the main root

Write r0=(R-1)/2>=2. Elementary Pell growth implies

    c0/K >= (1/2)*((2B-1)^2/(2P0))^r0.

For U0>=64,Z0>=6 the ratio inside the power exceeds U0-3: the
cleared difference is bounded below by

    (2(U0-1)Z0-5)^2-(U0-3)(4U0 Z0^2+2)
     =4(U0+1)Z0^2-20(U0-1)Z0+31-2U0 >0.

After U0=64+u,Z0=6+z the exact expression is
4uz^2+28uz+22u+260z^2+1860z+1703, positive for u,z>=0.
Together with c0/K<Z0+1 this yields
Z0>61^r0/2-1>2^(2r0+1)=2^R. The final elementary inequality follows
from r0=2 and induction, since 61>4.

For odd R, psi_A(R)=psi_B(R). Put e=sign(c) and D=lambda chi_A(R),
lambda in {+1,-1}. The signed Pell polynomial identities modulo the
odd H are

    chi_A(R)-a psi_A(R)=2^R,
    chi_A(R)+a psi_A(R)=2^(-R).

If lambda=-e, the root equation implies X 2^R=-e modulo H, impossible
because 1<|X|2^R<U0 Z0<|H|-1. If lambda=e, it gives X=e2^R modulo H.
The bound |X-e2^R|<=U0+2^R<U0+Z0<|H| turns that congruence into equality.
Thus the universal conclusion is

    X=e 2^R, R odd.

Only now use X=2 modulo 3. Since 2^R=2 and -2^R=1 modulo 3, e=+1.
Set u_old=2^((R-1)/2). It is an integer and restores X=2u_old^2.
Together with the two restored product Pos triples and the affine
coordinate restorations, all Q41 rows vanish. Q41's inherited native
compiler and syntactic calibration give a finite ZFC refutation.

## 5. Simultaneous canonical completeness: the compatibility point

An arbitrary Q41 zero need not satisfy the determinant, nor either affine
restriction. Such a stronger claim is unnecessary and is not made.
A finite refutation instead supplies the common canonical source34 family.
Source64's construction has

    q=2^t with t odd, R=3 modulo 4, X=2^R,
    w_scale=2^(R-t-2), R-t>=2 and R-t even.

Thus X3=(X+1)/3 is integral in the direct form. In the affine form,
beta=1 modulo 3 and q=2 modulo 3 give J_old=1 modulo 3, while
w_scale=1 modulo 3 because its exponent is even and nonnegative. Thus
J3=(J_old-1)/3 and w3=(w_scale-1)/3 are integral.

The determinant estimates hold for this *same* canonical family, including
all allowed rank-tuning dummy changes. Here is why. Let rho=2^121 and
Bnative=rho^8801. Every occupied cell has a fixed top C digit of 1 at
position3296, with all lower support below2196; hence

    rho^3296 <= C_j < (1+1/rho) rho^3296.

The top coefficient of D_C is
c0=105534389824824194647382298625 at position5495, verified from literal
tile0=(2,435,3,1). The canonical convolution is carry-free and gives

    c0 rho^8791 <= F_j < (c0+1) rho^8791.

The temporal transport is a whole-cell cyclic rotation because the actual
rank controller gives R=d*width modulo d*N. Spatial and temporal additions
have degrees at most3297 and3296. They do not alter the top8791 digit.
The allowed dummy changes are below2195, also preserving both top bounds.
The coefficient bound 6S+18<991(2S+6), together with the authentic source34
bound4*991(2S+6)+8<rho, prevents carries in the convolution.

Using 2^96<=c0 and c0+1<=3*2^95, the exact scale exponent identities
121*8791+1113=d-97 and121*3296+666104=d-1 imply, after summing the N cells,

    q/2 <= U < 4q/5, q/2 <= V < 3q/5.

These inequalities are independent of tableau size and unchanged by the
rank-tuning that arranged the parity restrictions above. Put q=2s,
U=s+x,V=s+y. Then 0<=x<3s/5, 0<=y<s/5, and

    UV-(q-U-V)^2
      =s^2+s(x+y)-x^2-xy-y^2 > (12/25)s^2>0.

Represent this positive integer by Pos, retaining the same canonical
source witnesses. The residue coordinate changes and this new private
Pos triple can therefore be made simultaneously. All24 rows vanish.
This proves completeness without a false equality of old and new zero sets.

## 6. Weighted-cone alternatives

The alternative JSON files use the same orientation and replace only the
new determinant row by

    2(xy+xz+yz)-x^2-y^2-z^2=Pos(cone1,cone2,cone3),
    x=beta F, y=Walpha alpha, z=WC C,
    Walpha=2T rho^3296, WC=T beta, T=K0-beta*rho+1.

All weights are positive. A mixed or zero sign gives, after a permutation
and overall sign reversal, x,y>=0,z<=0. Then the left side equals
-(x-y)^2+2z(x+y)-z^2<=0. Thus common nonzero signs are recovered for
arbitrary signed assignments, with no canonical assumptions.

Canonical completeness uses the same rank controller and fixed anchors.
Source69 proves A J<=C<(A+H)J, TAJ<=F<2TAJ, and
beta J/2<alpha<=beta J, with A=rho^3296,H=rho^2196,
and the actual finite bound2(T+1)(A+H)<beta. Hence x,y,z are each in
[L,2L], L=TA beta J>0. The quadratic form is at least3L^2 on this box
(by separate concavity and its eight vertices, or the identity
4xy-(z-x-y)^2 after ordering). Again the bound survives every permitted
dummy change. Thus the identical orientation compatibility proof applies.
These weights are larger, so these alternatives are not preferred.

## 7. Integer-polynomial projections

Use the affine quartic with q=beta(3J3+1)+1 and W=4(3w3+1).
For the sextic set tau_old=tau_tail+E(c-eta) and eliminate

    P=eta+zeta+E(c-eta), N=q(L+1), X=Wq,
    C2=c^2, F2=f^2, g=y^2-V^2.

The first norm becomes tau_tail^2+(2tau_tail-eta-zeta)E(c-eta)-1.
Six variables and six defining rows disappear, leaving31 variables and18
residuals of degree at most3. Their sum of squares has coefficient4 at
r^2 c^4; the only row involving r is I-(2r+1)c^2. Thus exact degree6
holds after all authentic numeral specialization.

For the octic put k0=1-V+jc+hE and eliminate

    L=q^2-1, N=q^3, X=Wq, C2=c^2, F2=f^2,
    g=y^2-V^2, Baux=I^2, D=Wq+ac+gamma(4a+3),
    Delta=a^2+4a+3, zeta=k0-eta, P=k0+E(c-eta).

Eleven variables and eleven rows disappear, leaving26 variables and13
residuals of degree at most4. The unique row containing both a and f is
I^2-(a^2+4a+3)(f^2-1), whose square gives a^4 f^4 with coefficient1.
Thus exact degree8 survives specialization.

These restorations are integral polynomials in retained variables, and
every dropped defining row becomes identically zero. Forgetting these
coordinates, with the stated inverse root shift for the sextic, and
restoring them are inverse maps of integer zero sets. No rational
division or unauthorized positivity convention is introduced.

## 8. Verification and inherited boundary

Run build_coefficients.py, build.py, and check.py, normally or under Python -O.
The checker does not import the builder. It compares every packet against
source70's literal corresponding packet with only the two old guards replaced,
checks all full-parent restoration identities, declared/live symbols,
dimensions and noncancelling degree witnesses, and verifies every copied
source and coefficient payload. The signed ratio's positive-coefficient
identity and the cone's box-vertex certificate are exact universal algebra.
An altered-guard negative control is rejected for each packet.

The standard-library source34 coefficient reconstruction is executed only
after its exact Git blob is authenticated. It checks all943 ordered tiles
and genuine coefficient bytes. These are finite checks, not tests pretending
to prove the universal Pell or compiler claims.

Inherited unbounded interfaces are the ordinary Pell classification,
strong-rank and signed auxiliary theorems in
upstream/residue/dependencies/{PELL_RELAXED_AUXILIARY_PROOF.md,
PELL_SIGNED_PROOF.md,SIGNED_DOMAIN_29.md,ODD_SCALE_27_PROOF.md};
the authentic native compiler and canonical witness construction in
COEFFICIENT_PROOF.md and WANG943_LANGUAGE_AND_COMPILER.md;
and the exact K215/refutation calibration used by PROOF41.md and PROOF44.md.
This contribution does not strengthen their proof-assistant status.
