# Weighted square transport with a whole-product center

This is an ordinary mathematical proof composition, not a newly compiled
Lean/Rocq theorem. The parent is the entire 87-operation, degree-214,
ten-positive-variable equation from package 172, frozen inside the incoming
Affine Horizons archive at repository snapshot
`cdfea7d90176775d74c1c30afbe49fa78ade9897`. Its graph is `parent87.json` and its
proof is `PARENT_PROOF.md`. The native/K215/refutation calibration of its
entire four-number tuple is retained. No arbitrary tuple satisfying scalar
inequalities may replace those four integers.

The main new equation has ten independent strictly positive integer inputs,
118 live binary arithmetic operations, and exact degree 190. The companion
has the same inputs and tuple, 99 operations, and exact degree 202.

## 1. Complete definitions

The independent positive inputs are

    J,F,alpha,i,T,w,s,n,eta,zeta.

Every other symbol is a polynomial abbreviation. Retain the full four-number
tuple beta,K0,MC,MF and put

    h=beta J, q=h+1, C=q-F-alpha, X=qw, Y=s, Ybar=qY,
    k=eta+zeta, c=kY+eta,
    A=Ybar(X+1)+1, Delta=A^2-1, H=4A-5,
    v=XYbar^2, ell=vk, E=1+ell(ell+k),
    R=[h(q-F)+alpha](q^2-1)+(MC+qMF)J,
    B=(K0+w)C-F, U=ic^2, a=Delta U^2 E,
    F0=1+a, G=E F0, f=1+2a, Q=4Delta aF0,
    b=cT-R, V=fb-c, K=X(3c-2X)+2,
    e6=6(k-R-1)-ell(k^2-4), D=6q^7, M=hDH.

The new weighted square transport is

    L=A U^3 b^2.

Define the integer polynomial center using only fixed integer coefficients:

    e2=(kYbar)^2,
    S=(kYbar)[ell+k-(kYbar)(Ybar+1)],
    theta=U^2 b,
    Rc=theta(3E+e2)-(b-c),
    Sc=4E^2+3S^2+e2^2,
    Omega=U[2S Rc+A(4EV-theta Sc)].

For a cheaper literal evaluator, replace Sc by Sc-bB inside that last
formula and call the result OmegaFold. Exactly,

    OmegaFold=Omega+LB.

The emitted circuit therefore uses `n-OmegaFold` in the carrier, saving two
operations relative to a standalone UE b^2 weight. This folding never assumes
that the shifted center itself is positive; all sign bounds below concern
the original Omega and the explicitly positive effective transport L.

Finally set

    Z0=hD[H(n-LB)+K]-H[DB+h(e6-6q^4s)],
    Z=Z0-M Omega,
    P190=Q[Z^2-16M^2GV^2]+16M^2G-Z^2.

The requested ordinary Diophantine equation is `P190=0` in the ten positive
inputs. No exponent is variable. No division, floor, recurrence, new witness,
or unstated coefficient appears in this definition. The supplied JSON fixes
every arithmetic operation and every numerical port.

## 2. Root extraction before sign recovery

The parent's root extraction depends on the final norm equation and the
unchanged definitions of E,F0,G,Q,V; it does not depend on the old carrier.
Multiplying G by the fixed square 16 preserves all valuation parity steps.
At a zero, those steps give positive integers tau,f0,g,y with

    E=tau^2, F0=f0^2, G=g^2, g=tau f0,
    QV^2-(Q-1)y^2=1, Z/M=epsilon*4gy, epsilon in {1,-1}.

The rational adjacent-Pell descent used in the parent makes y integral;
this does not presume that Z/M was integral before root extraction.
The main signed-index folding then gives c=psi_A(p), with positive odd p.
Since c>=3, p>=3 and c>=4Delta+3. All of this holds when Y=1 and when
the auxiliary index is three. Neither q|Y nor an index-five exclusion is used.

The parent proves before recovering signs of B,C,R,b,V that b and V are
nonzero and have the same sign, and

    |b|>4Delta f-1>3Delta f,
    y<(3/2)|V|, |V|<(3/2)f|b|, f>6g.

The second displayed V inequality follows directly from V=fb-c and f>2c.
Also G=E+Delta(UE)^2 gives

    0<AUE<(3/2)g.

The base has A>=32*(32+1)+1=1057, independently of every recovered sign.

## 3. A signed bound for the whole center

This is the polynomial-quotient argument of package 178, with its old formal
Y replaced by Ybar=qY. It is rechecked here because applying only a positive
V bound before the bootstrap would be circular.

Temporarily use a formal indeterminate t in place of A. Write

    E(t)=e2 t^2+e1 t+e0,
    e1=k^2 Ybar(1-2Ybar-2Ybar^2),
    e0=1+k^2Ybar(Ybar+1)[Ybar(Ybar+1)-1],
    V(t)=[1+2(t^2-1)U^2 E(t)]b-c,
    F(t)=E(t)V(t).

Let Qj be the ordinary polynomial quotient of F(t) by t^j, evaluated at A.
Because E has degree two in t, Q3 is coefficientwise even. Direct algebra
proves

    Omega=U[4AEV-2Q1-Q3/2].

This quotient notation is only proof notation; the division-free definition
in section 1 is the equation. Let # denote evaluation of coefficient absolute
values at positive A. As delta=(Ybar+1)/A<1/16,

    E#<2E,
    F#<2E(|b|+c)+8(A^2+1)U^2 E^2 |b|.

Using c+1<2U^2E and |V|>Delta U^2 E|b| gives

    F#/|EV| < 8+20/Delta < 10.

Deleting low coefficients bounds |Qj|<=F#/A^j. Therefore

    |Omega-4AUEV|
      < 10U|EV|[2/A+1/(2A^3)]
      < AUE|V|.

In particular Omega has the sign of V and

    3AUE|V|<|Omega|<5AUE|V|.

All these are absolute estimates at an arbitrary zero; B,C,R,b,V have not
yet been assumed positive.

## 4. Why the new transport works

The old square weight b^2 need not dominate the Pell root when auxiliary
index three is allowed. A polynomial weight repairs this while keeping
much lower degree than bV and fitting a factor already used by the center.
First, at every zero, E<U^2. Indeed v+1<A^2<c and k<c, with integer c>=3.
Therefore

    E=1+k^2v(v+1)<=1+(c-1)^4<c^4<=U^2.

Let L=A U^3 b^2. The preceding bounds give

    4gy+|Omega|
       < 6g|V|+5AUE|V|
       < 11AUE|V|
       < (33/2)AUE f|b|
       < [11E/(2Delta U^2)]L
       < [11/(2Delta)]L
       < L/2.

The step g<AUE used in the third line needs care: in fact
`(AUE)^2-G=U^2E^2-E=E(U^2E-1)>0`, so g<AUE holds on this domain.
The final inequality is Delta>11, valid here since A>=1057.
This proves the needed bound without an auxiliary-index-five assumption.

For proof only put e*=e6/6, rho=e*/q^7, sigma=s/q^3,
t=B/h, kappa=K/H, z=Z/M, W=1+hL. The exact rational identity is

    z=n+kappa+sigma-Wt-rho-Omega.

The inherited first-index argument gives K>0, so kappa,sigma>0. The inverse
Lucas correction is valid for every integer R, including negative R:

    e*<=k-R-1<b, hence rho<|b|/q^7.

If B<=-1 then Wt<-L. Since UE>=1 and nonzero integer b imply L>=|b|,

    n=epsilon*4gy+Omega-kappa-sigma+Wt+rho
      < L/2-L+|b|/q^7 <0.

This contradicts the independently stipulated n>0. Thus B>=0 and C>0.

## 5. Arithmetic and logical recovery

After B>=0,C>0 the calibrated mask gives 3q<R<q^4-2. The parent then
recovers b,V>0, the main index p=R, R odd, q even and J odd. The unchanged
residues are V=-c mod f and V=-R mod c; the transport and center do not
enter them.

The integer shift M Omega is divisible by D and H. Also L is an integer
polynomial, so W=1 mod h. Thus every fractional-part step of the parent
applies unchanged to the new carrier. In the necessary order these are:

1. The first Pell pair gives k=2psi_(1+2v)(m), and clearing the literal
   denominator gives q^4|e*.
2. The cubic-difference identity, including its prime-3 valuation argument,
   gives m=(R+1)/2, without prematurely asserting q^7|e*.
3. Reducing modulo H yields H|6hK. The lambda=q ratio theorem and universal
   projection then imply X=2^R; q is therefore a power of two.
4. The stronger resulting valuation of v supplies q^7|e*. Now rho and kappa
   are integral. The remaining carrier gives q^3|Y and h|B.

These are exactly the parent native outer endpoint conditions. Its fresh
native reconstruction with the whole fixed tuple gives a finite syntactic
ZFC refutation through its retained native/K215/refutation calibration.
No substitution of an unrelated coefficient tuple is made.

## 6. Positive completeness

A finite refutation gives the parent's canonical positive outer witnesses,
Pell pairs and trace-linear auxiliary coordinate T, with b,V,y>0,
t=B/h>=0 integral, and integral rho,kappa,sigma. Section 6 of PARENT_PROOF.md
proves the bound

    |rho|+kappa+sigma<g

independently of the carrier weight. For these witnesses Omega>0 and L>0.
Define the new integer coordinate

    n=4gy+Omega+(1+hL)t+rho-kappa-sigma.

The displayed bound, y>=1, t>=0, and Omega>0 prove n>0. The resulting
carrier is z=4gy, so the final polynomial vanishes. This constructs positive
witnesses; it does not assume a polynomial shear preserves positivity for
arbitrary tuples.

Therefore, by ordinary reasoning formalizable in ZFC, a positive zero exists
if and only if a finite syntactic ZFC refutation exists. Negating both sides
proves the required equivalence with Con(ZFC). Neither consistency nor a zero
is asserted.

## 7. Exact degree 190

Treat A,Ybar,k,U,b,c as free polynomial variables with weights
(4,2,1,5,4,2). Exact collection verifies that the norm defect

    Dcenter=Omega^2-16GV^2

has 594 nonzero terms, weighted degree 94, and complete top part

    8A^6 Ybar^8 k^8 U^6 b^2(A^2-6Ybar^4).

The corresponding degrees in the ten actual inputs are

    deg(Q,M,G,V,Omega,Z0)=(72,12,46,36,59,41).

Decompose the complete output as

    P190=Q[Z0^2-2MZ0 Omega+M^2 Dcenter]
         +16M^2G-(Z0-M Omega)^2.

The five degrees are bounded by 154,184,190,70,142. Only the norm defect
can contribute degree 190. With q0=beta J and k0=eta+zeta, substitution of
the actual leading forms yields

    [P190]_190 = 9*2^11*q0^74*w^18*s^52*i^10*k0^32
                 *(q0-F)^2*(w^2-6s^2).

This is nonzero for the actual fixed positive beta. Thus the degree is
exactly 190, not merely the naive graph bound 214. Every one of the ten
independent inputs and every fixed coefficient port remains live.

## 8. The 99-operation, degree-202 companion

Retain the free-chart parent, choose L=bV, and replace the center by

    C2=2AUE-US,
    Z=Z0-M C2 V,
    P202=Q[Z^2-4M^2GV^2]+4M^2G-Z^2.

Here S is the same quotient of E(t) by t as above. The positive remainder

    R_E=1+k^2Ybar(Ybar+1)[Ybar(Ybar+1)-1]

gives E=AS+R_E. The explicit expression
`S=k^2Ybar[(X-1)Ybar^2-Ybar+1]` is positive since X>=32 and Ybar>=32.
Thus 0<S<E/A, and hence 0<C2<2AUE<3g. The inherited
|b|>4Delta f-1>24Delta g-1>16g gives

    2gy+C2|V|<6g|V|<L/2.

The sign bootstrap and recovery follow as above, with scale 2. Completeness
uses n=2gy+C2V+(1+hL)t+rho-kappa-sigma, which is positive by the same bound.
The defect identity is

    C2^2-4G=4U^2E R_E+U^2S^2-4E.

Its exact degree is 34. The complete output has exact degree
72+24+34+72=202. Its entire highest homogeneous form is

    [P202]_202=9*2^12*q0^80*w^22*s^56*i^10*k0^32*(q0-F)^2.

The companion is a measured tradeoff: degree 202 at 99 operations, against
the incoming degree 206 at 90 operations and the principal degree 190 at
118 operations. No global minimality or worldwide novelty is claimed.

## 9. Attribution and boundaries

Package 172 supplies the free-quotient chart and signed index-three analysis.
The incoming Affine Horizons package supplies its centered degree-206
composition. Package 178 supplies the whole-product quotient center and its
signed coefficient-majorant argument. The new step is the weighted square
transport and its folding into the existing center, together with the
noncircular bound in the free chart,
the compositions, literal equations and exact degree certificates.

Finite checks authenticate formulas, degrees, input occurrence and coefficient
bytes. They do not establish unbounded Pell or logical theorems by sampling,
and they do not constitute a freshly compiled end-to-end formal proof.
