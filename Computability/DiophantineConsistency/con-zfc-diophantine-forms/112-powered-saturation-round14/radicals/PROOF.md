# Fifth-power saturation and a decoupled strong Pell scale

## Result and scope

This note gives a new ordinary arithmetic transformation of the pinned
`scalar-carrier12` construction in VladimirReshetnikov/ProveIt, commit
`84e16e43092614bae262ca59651cb9d77e31a255`. It preserves twelve
**unrestricted integer** unknowns and the complete original six-coefficient
tuple. It is not a positive-variable construction or a natural-variable
construction. No minimum claim or new proof-assistant endpoint is made.

The mathematical advance is not a gate rewrite: the carrier now proves
only a fifth-power divisibility, and the enormous, fixed native base makes
that sufficient for exact main-Pell projection. A second independent
advance decouples the strong Pell scale from the positivity witness by
proving full auxiliary interpolation modulo every modulus supported on the
strong scale. Native/refutation calibration is inherited only after the
same complete signed source has been restored.

The primary integral equation, evaluated after the integral shear
n -> n+QV, has exact degree768 and141 live binary arithmetic operations.
The conservative companion has degree800 and141 operations. The complete
new literal circuits and independently recomputed metrics are supplied by
the accompanying norm-circuit work. This proof defines their polynomial
mathematically without relying on code execution.

## 1. Fixed tuple and complete definitions

The twelve coordinates are j,C,z,h,r,v,w,T,c,n,t,s, all in Z. The six fixed
ports beta,K0,MC,MF,cone_A,cone_B are exactly the original source34 tuple;
in particular beta=2^1064921-1 and MF is the already-shifted high mask.
No port is replaced individually or left as an additional unknown.

Define

    J=6j+1, q=beta J+1, W0=12w+4,
    X=qW0, Y=(2v+1)q^3, E=XY,
    a=E+Y, H=4a+3, Delta=a^2+H=(a+2)^2-1,
    F=(K0+W0)C-z(q-1),
    R=[q(q-F)-C](q^2-1)+(MC+q MF)J,
    k=R+1+hE, eta=c-Yk, zeta=k-eta,
    U=cone_A F, W=cone_B C,
    G=UW-(q-U-W)^2,
    Pair=G eta zeta-(t^2-G-eta zeta+1)^2,
    Dg=(3Pair-4)s^2+1,
    I=r c^2, Df=1+Delta I^2, Q=Delta^2 I^2, delta=Q-1,
    V=Df(c-R+4IT)-c, Cy=QV^2-1,
    ell=XY^2, Dt=1+ell(ell+1)k^2,
    Kred=X(2X-3c)-2,
    zc=HT+Kred,
    Ac=(zc^2+3H^2)(zc^3-19H^3),
    S=srH, Z=Sn-Ac.

Write F16(Z;a,b,e,d) for the product over all sixteen independent sign
choices of Z minus the signed sum of square roots of a,b,e,d. Sign
invariance makes this an integer polynomial. Two valid equations are

    P_rat=delta^8 F16(Z;9S^2 Df,81S^2 Dt,729S^2 Dg,S^2 Cy/delta)=0,
    P_int=F16(Z;9S^2 Df,81S^2 Dt,729S^2 Dg,S^2 delta Cy)=0.

The rational notation is only proof notation: multiplying by delta^8
clears every denominator, since the degree in the fourth radicand is eight.
The final evaluator contains only integer constants, +, -, and ×.
Polynomial changes n -> n+QV or other explicitly recorded integral shears
preserve integer-zero existence and may be applied to these equations.

For comparison, a conservative companion keeps I=src^2 while using the
same S=srH. Its proof below needs only the parent's original interpolation
theorem; the decoupled I=rc^2 variant uses Section 5.

## 2. Bootstrap: establish the guards before asserting I is nonzero

The parent's unconditional front-end facts are unchanged: q is even,
q=2 mod3, |q|>=beta-1, |X|>=4|q|, |Y|>=4096, H is odd and nonzero,
Delta>1, Df,Dt>=1, and delta is nonzero. Modulo3,

    H=Delta=0, Df=Dt=1, Q=0, delta=Cy=-1.

If S=0 all four scaled norm radicands vanish. The integral polynomial is
Ac^16, and the rational polynomial is delta^8 Ac^16. Neither vanishes:

    Ac=H^5 pi(T+Kred/H),  pi(x)=(x^2+3)(x^3-19),

and pi has no rational zero. Thus s,r are nonzero. This does NOT yet prove
c or I nonzero.

At a zero divide a vanishing norm factor by S. The squared 3-adic orders
of the normalized roots are 0,2,4,6+v3(Dg), in the order auxiliary,
3sqrt(Df),9sqrt(Dt),27sqrt(Dg); omit a zero guard term. The parent's full
prime-order separation lemma applies, including at I=0, where delta=Cy=-1.
The signed rational sum therefore forces all four roots rational. In
particular Dg=g^2>=0 for an integer g. Since s is nonzero, Pair<=0 would
give Dg<0. Thus Pair>0. The retained determinant guard lemma gives

    G>0 and eta*zeta>0.

If c=0 then eta*zeta=-Y(Y+1)k^2<=0, since integer Y(Y+1)>=0.
This contradiction proves c!=0, hence I=rc^2!=0 and Q>1. Only NOW apply
adjacent-coefficient Pell descent: the extracted rational auxiliary root
gives an integer y with

    QV^2-(Q-1)y^2=1.

For the integral version divide the extracted integer root of delta*Cy
by delta before descent. The other integral roots are f^2=Df and tau^2=Dt.
Every sign of I,V,c,a remains allowed.

The integral factor equation gives S|Ac (also in the rational variant,
after y's descent). Because H divides S, reducing Ac modulo H yields

    H | Kred^5.                                            (A)

We do not claim that (A) alone forces H|Kred.

## 3. Main-root folding and indices, before any projection

The scalar parent's main-root recovery and index bootstrap require
exactly the following hypotheses, all now satisfied:

* cubic Y=(2v+1)q^3 and the unchanged packing and first-norm definitions;
* G>0 and eta*zeta>0;
* I!=0, c^2|I, |I|>=|c|;
* f^2-Delta I^2=1 and QV^2-(Q-1)y^2=1;
* V=-c mod f and V=-R mod c.

The last congruences follow directly from

    V+R=Delta I^2(c-R)+4I Df T.

In particular the argument does not require s|I or an odd multiplier.
For completeness, with B0=|a+2|, C0=|c|, I0=|I|, write
f_abs=chi_B0(m0), I0=psi_B0(m0). Classify the auxiliary equation at
rho=Delta I0. Its index nu is odd; reduction modulo f_abs and folding
modulo2m0 produces C0=psi_B0(p), since 2I0<f_abs prevents wrapping.
The divisibility C0^2|I0 gives p|m0 and C0|m0 by the Lucas multiplication
formula. The auxiliary residue modulo C0 then gives R=±p modC0.
The retained first-index bounds 0<R,p<C0/2 force p=R. All this precedes
and is independent of (A).

Consequently, for x=|X|, m=|Y| and sigma=sign(c),

    R=2r0+1, r0>=24,
    c=sigma*psi_(a+2)(R),
    m>(x-3)^r0/2-1,
    |H|>x(x-3)^r0.                                       (B)

The last bound can also be checked directly: |H|>=4(x-1)m-3, so its
difference from x(x-3)^r0 is greater than
(x-2)(x-3)^r0-4x+1, positive at x>=64,r0>=1.

## 4. Fifth-power saturation replaces full divisibility

Put K=X(X+2ac)-1. The exact polynomial identity is

    2K=Kred+HcX.                                        (C)

H is odd, so (A) and (C) imply H|K^5. Let

    Pi=(sigma X-2^R)(2^R sigma X+1).

The parent's signed Pell projection is the exact congruence

    2^R K=Pi modulo H.                                  (D)

It follows by taking fifth powers in (D) that H|Pi^5. This deduction uses
the actual unit multiplier, not merely the weaker implication
H|K => H|Pi. No nonunit is cancelled modulo a composite H.

The authentic fixed tuple implies

    x>=4(beta-1)>=2^64.

Both factors of Pi have absolute value <2^(R+1)x, so

    |Pi|^5<2^(10R+10)x^10=2^(20r0+20)x^10.

Meanwhile (B) and x-3>x/2 give

    |H|>x^(r0+1)/2^r0.

For x>=2^64 and r0>=24,

    x^(r0-9)>=2^(64(r0-9))>2^(21r0+20),

because the difference of exponents is43r0-596>=436. Thus

    |Pi|^5<|H|.

The integer divisibility H|Pi^5 forces Pi=0. The second factor of Pi is
odd and nonzero, hence sigma X=2^R. Define d=sigma*chi_(a+2)(R). The
signed Pell projection then gives H|(d-X-ac), recovering the exact
integral main projection gamma=(d-X-ac)/H of the source.

All remaining source rows and guards are unchanged. Therefore the
generalized signed source theorem yields a finite syntactic ZFC
refutation, with precisely the same named native/compiler calibration as
the pinned scalar parent. Neither the huge-base bound nor the new carrier
changes that calibration.

More generally this is a powered-divisibility saturation lemma, not a
special property of fifth powers. If |H|>x^(r+1)/2^r,
|Pi|<2^(4r+4)x^2, x>=2^b, and

    b(r+1-2d)>(4d+1)r+4d,

then H|Pi^d implies Pi=0. For all r>=r_min it is enough that b>4d+1
and the inequality holds at r_min. Here b=64,d=5,r_min=24 gives a
margin436. This lemma makes no optimality or historical-priority claim.

## 5. Full interpolation beyond the original modulus

We strengthen the parent's fixed-strong-pair interpolation theorem.
Let A0>1 be even, Delta=A0^2-1, R=3 mod4, and
c=psi_A0(R)>0 with c=R mod4. Fix any positive s. Choose a positive
even index m0 with

    I=psi_A0(m0), f=chi_A0(m0), 4s c^2|I.

The parent's finite matrix-period argument supplies such a pair, and
its valuation lemma proves v_p(m0)<=v_p(I) for every p|I. Its exact
squared-modulus period is lambda=4m0 f, a period modulo f^2. Keep this
same pair fixed throughout all choices below.

Let rho=Delta I, D=rho^2-1, and for positive odd nu put
V_nu=chi_rho(nu)/rho, an integer. The original interpolation theorem
supplies one nu0=3 mod4 and an integer T0 such that

    V_nu0=f^2(c-R+4I T0)-c.

Set d=lcm(lambda,4I). For every prime p|I,

    v_p(d)=v_p(4I),

since gcd(f,I)=1 and v_p(m0)<=v_p(I). For nonnegative h, set

    nu(h)=nu0+d h,
    T(h)=[V_nu(h)+c-f^2(c-R)]/(4I f^2).

T(h) is integral. Indeed d preserves the index modulo lambda, hence
V_nu(h)=-c modf^2 by the same odd-index identity as the parent. Also
nu(h)=nu0 mod4I and the identity V_nu=-nu mod4rho^2 for nu=3 mod4
preserves the numerator's divisibility by4I. Since gcd(f^2,4I)=1,
the whole denominator divides it. Every nu(h) gives an integral
auxiliary Pell witness y=psi_rho(nu(h)).

We claim, for p|I and h1!=h2,

    v_p(T(h1)-T(h2))=v_p(h1-h2).                         (E)

To prove this, take positive odd nu and a nonzero increment D0 divisible
by4; negative increments follow by interchanging the two indices.
Pell addition gives

    V_(nu+D0)-V_nu
      =V_nu[chi_rho(D0)-1]
       +psi_rho(nu)(rho^2-1)psi_rho(D0)/rho.

For p|rho, psi_rho(nu) and rho^2-1 are p-adic units. Elementary Pell
lifting gives, when4|D0,

    v_p(psi_rho(D0)/rho)=v_p(D0).

For odd p, v_p(chi_rho(D0)-1)=2(v_p(rho)+v_p(D0));
for p=2 it is2(v2(rho)+v2(D0))-1. Both are strictly greater than
v_p(D0). Thus the second summand has strictly smaller valuation than
the first, proving

    v_p(V_(nu+D0)-V_nu)=v_p(D0).

Here are details of the lifting facts. Put U=chi_rho(4), B=psi_rho(4).
We have B=4rho(2rho^2-1) and U-1=8rho^2(rho^2-1). For an odd p|rho,
write v_p(B)=b>=1. In the second coordinate of
(U+B sqrt(rho^2-1))^k the linear term is kU^(k-1)B. If p does not
divide k, every other odd-power term has valuation at least3b>b.
For k=p, the intermediate odd-power terms have valuation at least3b+1,
while the last term has valuation pb>b+1 (also for p=3,b=1).
Thus multiplication of the index by p raises the second-coordinate
valuation exactly once; prime-to-p multiplication preserves it. This
proves v_p(psi_rho(4k))=v_p(rho)+v_p(k)=v_p(rho)+v_p(4k).
At p=2, U is odd; odd k preserves v2(B) by the same expansion, while
psi_rho(2n)=2chi_rho(n)psi_rho(n) raises it exactly once when4|n,
because chi_rho(n) is odd. Hence
v2(psi_rho(4k))=v2(rho)+2+v2(k).

Finally the norm identity
(chi_rho(D0)-1)(chi_rho(D0)+1)=(rho^2-1)psi_rho(D0)^2
gives the first-coordinate valuations: for odd p the second factor is
a unit, and for p=2 it has valuation1 because chi_rho(D0)=1 mod8.
Taking D0=d(h1-h2) and dividing by4I f^2 proves (E).

Now let M be ANY positive integer all of whose prime factors divide I.
Equation (E) says that h -> T(h) is well-defined and injective on each
residue ring Z/p^e Z for p^e|M, hence bijective there. CRT supplies h
attaining any prescribed residue modulo M; take a nonnegative representative.
Thus the same fixed strong pair admits every T residue modulo M.

This is stronger than extrapolating the parent's linear congruence
V_nu=-nu mod4rho^2: that congruence alone is not enough for arbitrary M.
The isometry proof is the missing higher-prime-power argument.

## 6. Completeness and quantifier order

Start with the canonical signed native witness supplied by a finite
refutation. Keep the seven outer coordinates j,C,z,h,v,w,c. Choose t
making Pair>0, then a nonzero positive Pell positivity witness s,g with
g^2=(3Pair-4)s^2+1. The parent proves this choice exists, including Pair=1.

Choose the single strong pair I,f with4s c^2|I as in Section5. Define
r=I/c^2, so r is positive and divisible by4s. This is exactly I=rc^2.
Now M=sr has all prime factors dividing I. The canonical main projection
implies H|K, hence H|Kred by (C). Put kappa=Kred/H in Z.

The parent's intersectivity theorem for pi(x)=(x^2+3)(x^3-19) supplies
an a modulo M with pi(a+kappa)=0 modM. Section5 supplies an auxiliary
T=a modM, keeping I and f fixed. Consequently

    Ac=H^5 pi(T+kappa),
    Ac/S=H^4 pi(T+kappa)/(sr) in Z.

Finally choose the unrestricted integer

    n=Ac/S+y+3f+9tau+27g

for P_rat, or replace y by delta*y for P_int. A norm factor vanishes.
For an integral shear n -> n+QV, subtract QV from this choice of n;
there is no positivity requirement on n.

The order is: native witness, t, s, one strong pair I/f/r, one intersective
residue, T/y, then n. No strong pair changes after choosing the residue.
For the conservative I=src^2 companion choose r=I/(s c^2); then
M=sr=I/c^2 divides I, so the original full-residue theorem suffices
without Section5's strengthening.

Thus each new polynomial has an integer zero exactly when the same
calibrated source has a finite refutation. Under the parent's named
ordinary calibration, ZFC proves its integer unsolvability equivalent to
Con(ZFC). As in that source, this is an ordinary mathematical proof,
not a newly checked internal-ZFC development.

## 7. Exact leading coefficient of the primary degree768 form

The authoritative literal evaluator uses the integral equation with
Z=S(n+QV)-Ac. Write B=Sn-Ac and L=SQV, so Z=L+B. The separate exact
norm identity used by the literal checker pairs the auxiliary root first.
Its reduced quadratics have a unique top term2LB: every competing term
has smaller total degree. Here deg(B)=35 and deg(L)=61. Thus the entire
degree768 leading form is (2L_top B_top)^8, not merely a syntactic bound.

Let q0=6beta*j, W00=12w,

    a0=2v*q0^4*W00=2^7*3^5*beta^4*j^4*w*v,
    H0=4a0, I0=rc^2, F0=12wC-6beta*j*z.

Then

    V_top=a0^2*I0^2*q0^3*F0,
    L_top=4s*r^5*c^8*a0^7*q0^3*F0,
    B_top=-4^5*a0^5*T^5,
    (2L_top B_top)^8
      =2^104*s^8*r^40*c^64*a0^96*q0^24*F0^8*T^40.

In particular the coefficient of

    j^408 w^104 v^96 C^8 s^8 r^40 c^64 T^40

is exactly2^816*3^512*beta^408>0; the exponents sum to768. This proof
uses the authentic positive beta and cannot be defeated by an accidental
relation among the other five fixed ports. The literal norm checker binds
the degree-revealing expression to the141-operation evaluation graph.

## 8. Precise dependencies and limitations

Pinned repository prefix:
https://github.com/VladimirReshetnikov/ProveIt/tree/84e16e43092614bae262ca59651cb9d77e31a255/Computability/DiophantineConsistency/candidates/scalar-carrier12

Read dependencies are PROOF.md; source/PRIME_TWELVE.md for prime-order
separation and intersectivity; source/INTERPOLATION12.md for the canonical
native restrictions, Pell period, index valuation, and full-residue base;
source/signed-quadratic-proof.md for signed folding, pre-projection ranks,
ratio bounds, and the exact projection congruence. The unchanged six-port
binding and their inherited ordinary calibration remain essential.

Finite tests check identities, modular isometries, circuits and degree
certificates. They do not prove Con(ZFC), search for a full zero, or replace
the unbounded arguments above. Any predecessor compiler caveat remains a
calibration dependency and must not be hidden by these arithmetic changes.
