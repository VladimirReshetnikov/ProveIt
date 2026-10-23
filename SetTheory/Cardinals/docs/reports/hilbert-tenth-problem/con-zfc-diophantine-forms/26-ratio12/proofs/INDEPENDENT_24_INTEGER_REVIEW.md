# Independent review of the 24-integer synthesis

Reviewed source: `research/root24/PROOF24.md`, 22 October 2026.
Repository source snapshot: `a477d0fc8b6feda53796835564a988015e744d4d`.

## Verdict

The new domain extension is sound, subject to the explicitly inherited
inputless K215 compiler, signed Pell-core, and canonical completeness
theorems. It does not follow merely by composing the two old domain
statements: a new signed separation argument is necessary. The draft supplies
that argument correctly, including the zero square-scale and zero auxiliary
quotient boundaries. I found no mathematical gap in the new extension.

This review independently read the following source texts in the current
repository, rather than relying on the collection's intake summaries:

- `21-norm12/proofs/NORM12_PROOF.md`;
- `21-norm12/proofs/INTEGER26_PROOF.md`;
- `21-norm12/proofs/NORM12_INDEPENDENT_AUDIT.md`;
- `21-norm12/upstream/SIGNED_DOMAIN_29.md`;
- `23-separating12/proofs/ODD_SCALE_27_PROOF.md`.

All these paths are relative to
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/`.
This is an ordinary mathematical review, not a Lean/Rocq certificate and not
an independent reproof of the complete inherited compiler.

## 1. The decisive extra proof obligation

The old twelve-root proof assumes positive s, and its positive weights L,H
cannot simply be used unchanged in an argument about s<0. The *polynomial*
can remain unchanged, provided its automorphism proof uses absolute weights.
Here is an independent derivation of the requisite estimates.

Write Z=|Y| and a0=|a|=(X+1)Z. Then Z>=q^3, X>=0, k>=2, and

    k(Z-1)<|c|<k(Z+1)<=2kZ,
    |H|>=4a0-3>1,
    Delta=(a+2)^2-1 >= (q^3-1)(q^3-3)>q^4>R.

The lower bound for |c| uses 0<eta<k and is valid for either sign of Y.
Since i is nonzero and |c|>1,

    D=1+Delta*i^2*c^4 > Delta+|c|,
    b=RD+c >= D-|c|>1,
    Q-b=(Delta-R)D-Delta-c >= D-Delta-|c|>0.

Thus 1<b<Q and Bnd=v^2+D+2b is positive, including when T is signed or zero.
For every conjugate auxiliary root, with M=|v|sqrt(D)+b,

    |y'|^2 <= (Q M^2-1)/(Q-1)<2M^2<Bnd^2.

For a potentially negative right side of the auxiliary root equation, its
absolute value is at most 1; the displayed upper bound still applies since
Q M^2-1>1. This checks the complex-root case, which must not be omitted.

Set U=|H|Bnd>2. Since L=1+H Bnd, |L|>=U-1. Also sqrt(G)>2, so

    |L|sqrt(G)>U.

If X>0, then X>=q and ell=X k Z^2=kZ|E|. The estimates

    sqrt(A)>ell,
    sqrt(G)<(a0+2)|c|<2(a0+2)kZ

give

    |H|sqrt(A)-sqrt(G)
      > kZ[(4a0-3)|E|-2(a0+2)]
      >= kZ(2a0-7)>2.

Consequently

    |HL|sqrt(A)>|L|sqrt(G)+|H|Bnd.

These estimates supply exactly the two strict automorphism separations.
If X=0, A=1 and the first root is already rational, so its separation
inequality is neither needed nor asserted. The second separation still
holds. The argument therefore recovers rational t,u,y for every possible
root branch, without assuming s>0, X>0, or T!=0 prematurely.

## 2. Saturation and the exceptional boundaries

The auxiliary Pell saturation lemma in package21 is adequate. Its proof uses
the exact divisibility rule chi_j | chi_l iff l is an odd multiple of j,
obtained by index reduction modulo 2j and strict growth. It applies to the
integer-coordinate Pell group for any nonsquare positive discriminant;
squarefreeness is unnecessary.

When T!=0, Baux!=0, so f=(e-d*y^2)/Baux is rational and f^2=D forces
integrality. Then V=vf-b is integral and saturation proves y integral.
When T=0, apply saturation directly with the integer V=b. It proves y
integral without using f. In either case

    gamma=(u-X-ac)/H=r-Bnd*u-L*t-y

is integral. At X=0 the reconstructed main norm implies H divides 1,
contrary to |H|>1. At T=0 the identity

    y^2=b^2+(b^2-1)/(Q-1),    1<b<Q

puts y^2 strictly between b^2 and (b+1)^2. Thus both boundary exclusions
are justified in the correct order. There is no division by an unproved
nonzero T or Baux.

## 3. Applying the negative-scale exclusion

The recovered equations are exactly the normalized first, main, strong,
and auxiliary core equations of package23. The signs of t,f,y,gamma,h,T
are allowed there, and the two exterior factors have the same unit sign.
Replacing i by |i| changes none of the equations; the normalized rank
argument needs only nonzero i. Its positive ordinary multiplier is
Delta*|i|, not i itself.

I checked package23's negative-scale proof: with Z=-Y, B=(X+1)Z-2 and
c0=-c, normalized strong divisibility gives m divisible by p*c0. The
auxiliary congruences then recover p=R even though c<0, because the first
congruence is squared. Its no-wrap argument recovers R=2r0+1 and its
ratio bound gives Z>2^R. The two possible signs of the main root yield
X=-2^R or X*2^R=1 modulo H, both excluded by strict intervals inside |H|.
Thus s<0 is impossible. The odd substitution excludes s=0.

## 4. Canonical completeness and the two odd coordinates

Completeness must establish simultaneous odd i, odd s, and square w. These
properties are compatible, rather than separate existential choices.

For the same canonical tableau, odd power-of-five padding gives q=2^t
with t odd; the decoded R is odd, hence w=2^(R-t) is a positive square.
The exact source completeness proof then chooses m=cR and sets

    f=chi_A(m), i=psi_A(m)/c^2,
    rho=Delta*psi_A(m), V=chi_rho(R)/rho, y=psi_rho(R).

The binomial expansion gives c^2|psi_A(cR), and c,R,m are odd. Hence i is
odd. The source proof uses R=3 modulo4 to obtain V=-c modulo f and V=-R
modulo c. It restores positive integral o,j,T, including the nontrivial
integrality of T=(o+Rf)/c. Thus changing the strong index preserves the
entire auxiliary block, not only its strong Pell equation.

For odd s, the population calculation must use the **unshifted** high mask
in its explanatory Tmask, even though the polynomial's MF port is shifted.
Writing q=2^t, M=q^2,

    S=(C-1)+qF,
    Tmask=(MC*J+1)+q*(MF_native*J-1),

the native mask constraints give S AND Tmask=0 and both are below M.
MC=2 modulo4 yields pop(MC*J+1)=N*pop(MC)+1; MF_native=4 modulo8 yields
pop(MF_native*J-1)=N*pop(MF_native)+1. Their sum is t+2. Therefore

    R=(M-1-S)M+(S+Tmask),
    pop(R)=2t+pop(Tmask)=3t+2.

The exact half-binomial valuation gives v2(Y)=3t, so s=Y/q^3 is odd.
This modifies no previously chosen coordinate. The norm witness r is then
defined from these same canonical roots, establishing simultaneous
completeness for all three restrictions.

## 5. Independent exact-degree calculation

Give J,F,alpha,z,w,eta,zeta weight2, and h,i,T,s,r weight1. Coefficients
have weight0. The degrees of the decisive quantities are:

| Quantity | Weighted degree |
|---|---:|
| q,X,Y,E,k,c,a,H,Delta | 2,4,7,11,2,9,11,11,22 |
| ell,A,G,R,Nk,Nt | 20,40,40,8,12,4 |
| D,Q,d,v,b,Bnd,L,S | 60,82,82,10,68,68,79,20 |
| e,Baux | 218,160 |

For the pair-ring evaluation of the nested norms, put x=S+L*u and reduce
x^2=V0+V1*u modulo u^2=G. Then deg(V0)=198 and deg(V1)=99.
The scalar a0=H^2 L^2 A has degree220, so in

    C=d*(x^2+a0)-H^2 e

its coefficients C0,C1 have degrees302,181. Define K=4d^2 a0 x^2 and
Z0=H^4 Baux^2 D. Their coefficient degrees are 582,483 and424.
In the cheaper identity (C^2-K-Z0)^2-4KZ0, the even coefficient has
degree1208 with unique highest term C0_top^4, while the odd coefficient
has degree at most1087. The outer norm therefore has exact degree2416,
because its other term has degree at most40+2*1087=2214.

Consequently the product degree is 2416+12+4=2432; the SOS degree is4832.
This also verifies that changing s from weight2 to weight1 does not
silently invalidate package21's old dominance calculations.

The highest norm form is

    2^80 i^48 k^112 w^112 s^224 q0^832(q0-F)^16,

where q0=beta J and the symbols denote their top parts. The product top
form is this multiplied by -h*w*s*q0^4 and
w*(q0-F-alpha)-z*q0. After the actual substitutions, the monomial

    J_x^1706 h z_x^2 i0^48 eta_x^224 w0^226 s0^225

has coefficient +2^353 beta^853 and degree2432. It cannot cancel and is
nonzero for every authentic beta>0. The norm's analogous coefficient is
2^352 beta^848 at degree2416.

## 6. Arithmetic and scope

Six Pos maps cost42 binary gates, two odd maps cost4, and the square map
costs1. Thus the substitution overhead is47 gates and the unchanged
package21 source yields159/163/166 gates for system/product/SOS. The new
source has24 unrestricted integer variables.

The result improves the repository's stated 26-integer products on all
three metrics of variable count, operations, and degree. It does not
improve the 67-operation positive polynomial, the positive quartic
constructions, or the nine-natural-variable Jones specialization.
No global minimality or new proof-assistant verification is implied.

The only minor editorial correction suggested during review was to write
Q-b >= D-Delta-|c|>0. A strict first inequality can also be justified from
the stronger available Delta-R bound, but is unnecessary.
