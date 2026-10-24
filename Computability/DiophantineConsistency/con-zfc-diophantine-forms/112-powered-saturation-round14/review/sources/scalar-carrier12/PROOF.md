# Scalar intersective carrier after signed main-root recovery

This is a new ordinary arithmetic reduction with twelve unrestricted
integer unknowns. Its independent review and full literal checks pass.
No new Lean, internal-ZFC endpoint or global minimum is
claimed. The coefficient tuple and named native/refutation calibration
are exactly those of the reviewed valuation-separated twelve-integer
parent. All six coefficients remain unchanged, including shifted MF.

## 1. Complete equation

Use the twelve coordinates j,C,z,h,r,v,w,T,c,n,t,s and all polynomial
definitions through Dg,I,Df,Q,delta,V,Cy,Dt in the retained
`source/PRIME_TWELVE.md`, Section1. Thus

    J=6j+1, q=beta*J+1, W0=12w+4, X=qW0,
    Y=(2v+1)q^3, a=(X+1)Y, H=4a+3, Delta=(a+2)^2-1,
    I=s*r*c^2, Df=1+Delta*I^2, Q=Delta^2*I^2, delta=Q-1,
    V=Df*(c-R+4IT)-c, Cy=QV^2-1,
    Dg=(3Pair-4)s^2+1, Dt=1+XY^2(XY^2+1)k^2.

The literal files give every earlier definition too. Replace the entire
main-root/quadratic-algebra carrier by the scalar expressions

    K=X(X+2ac)-1, zc=HT+K,
    Phi_H(z)=(z^2+3H^2)(z^3-19H^3),
    Ac=Phi_H(zc), S=IH^5, Z=Sn-Ac.

Let F16(Z;a,b,e,d) be the product of Z minus all independent signed
square roots of its four arguments. Sign invariance gives an ordinary
integer polynomial. The two complete equations are

    P_rat=delta^8 F16(Z;9S^2 Df,81S^2 Dt,729S^2 Dg,S^2 Cy/delta)=0,
    P_int=F16(Z;9S^2 Df,81S^2 Dt,729S^2 Dg,S^2 delta Cy)=0.

The rational notation in P_rat is cleared symbolically in the literal
DAG; no division or radical operation occurs. The main radicand Dm
and both quadratic-algebra carrier coefficients have been removed.
The symbols above are abbreviations, not additional unknowns.

## 2. Nonzero bootstrap and separation

The parent's unconditional facts apply without any equation: q is even,
q=2 modulo3, |q|>=16, |X|>=64, |Y|>=4096, H is nonzero and odd,
Delta>1, Df,Dt>=1, and delta is nonzero. Modulo3 we have

    H=Delta=0, Df=Dt=1, Q=0, delta=Cy=-1.

First suppose I=0, so S=0. Every scaled radicand vanishes, delta=-1,
and each displayed polynomial becomes Ac^16. This is nonzero.
Indeed Ac=H^5*pi(T+K/H), with pi(x)=(x^2+3)(x^3-19). Its rational
argument cannot be a zero: x^2+3 has no real zero and x^3-19 has no
rational zero. Thus no zero has I=0. In particular s,r,c are nonzero.

At a zero divide a vanishing conjugate factor by the nonzero S. The
four normalized radical magnitudes have squared3-adic orders

    sqrt(Cy/delta):0, 3sqrt(Df):2, 9sqrt(Dt):4,
    27sqrt(Dg):6+v3(Dg).

For P_int the first root is sqrt(delta*Cy), again of order0. Omit a
zero guard term. Every subset of at least two remaining roots has a
unique minimum squared valuation, and that minimum is even. The full
prime-order separation lemma and its algebraic proof in the retained
PRIME_TWELVE Section3 therefore apply unchanged. A rational signed sum
forces all roots rational, even if Dg were initially negative. Integer
radicands give integer roots f,tau,g. The adjacent-coefficient descent
gives an integer y satisfying

    QV^2-(Q-1)y^2=1.

For P_int set y=sqrt(delta*Cy)/delta before that descent. All hypotheses
hold because Q>1. Thus Dg=g^2>=0. Since s is a nonzero integer, Pair<=0
would force Dg<=-3. Therefore Pair>0, which gives the original strict
G>0 and eta*zeta>0 guards. This order uses no main projection.

The signed factor is now integral:

    Sn-Ac=S(y+3f+9tau+27g)

in the rational case, with delta*y in place of y in the integral case.
Consequently S divides Ac and H^5 divides Phi_H(HT+K).

## 3. The scalar carrier recovers H|K

Expand

    Phi_H(z)=z^5+3H^2 z^3-19H^3 z^2-57H^5.

For any prime p with p^e exactly dividing H, if b=v_p(z)<e, the
leading term has order5b while every other displayed term has strictly
larger order. Hence H^5|Phi_H(z) implies H|z, also for negative H.
Applied to z=HT+K, this gives H|K. This is the whole scalar carrier;
no square root, selected quadratic branch or primewise cancellation
has been used.

## 4. Recover the omitted main root before signed orientation

Put B0=|a+2|, C0=|c|, I0=|I|. Then B0>=3,
0<C0<=I0 and f^2-(B0^2-1)I0^2=1, with |f|>2I0. Let
rho=(B0^2-1)I0, so Q=rho^2. Classifying

    rho^2 V^2-(rho^2-1)y^2=1

gives rho*|V|=chi_rho(nu), |y|=psi_rho(nu). Its index nu is odd
because an even-index chi is plus or minus1 modulo rho. Since
V=-c modulo |f|, the odd-index polynomial identity reduces to

    psi_B0(nu)=plus or minus C0 modulo |f|.

Writing |f|=chi_B0(m0), I0=psi_B0(m0), fold nu modulo2m0 and reflect
across m0. Some0<=p<=m0 then satisfies
psi_B0(p)=plus or minus C0 modulo |f|. The bound
psi_B0(p)+C0<=2I0<|f| excludes wrapping and the negative residue.
Thus C0=psi_B0(p), p>=1. This is exactly the absolute folding argument
of retained `source/signed-quadratic-proof.md`, Section2; it requires
I0>=C0 and no odd multiplier. All signs of a,c,I,V are allowed.

The cubic Y scale was present from the start. The strict guards give
the common-sign packing bounds and C0/|k| strip used by the signed
bootstrap. Its pre-projection rank proof now applies. For clarity the
only changed strong-multiplier point is licensed by retained
INTERPOLATION12 Section5: C0^2|I0 implies p|m0 and C0|m0 by the Lucas
multiplication formula, without an oddness premise. The auxiliary
residues are still V=-c modulo |f| and V=-R modulo C0. Indeed

    V+R=Delta I^2(c-R)+4I Df T,

which is divisible by c. More explicitly, write nu=2h+1 and
chi_rho(nu)/rho=Q_h(rho^2). Since C0 divides rho and
Q_h(0)=(-1)^h*nu, the auxiliary relation gives nu=plus or minus R
modulo C0. The preceding fold and strict monotonicity give
nu=plus or minus p modulo2m0. Since C0 divides m0, we obtain
R=plus or minus p modulo C0. The signed first-index bootstrap supplies
0<R,p<C0/2, so p=R. This directly proves the needed step-down without
any odd-multiplier normalization. The first norm then gives
R=2r0+1 with r0>=24. With x=|X|, m=|Y|, the
pre-projection ratio bound is m>(x-3)^r0/2-1. None of these facts
uses gamma or an assumed sign of X or H.

The whole-product argument in retained signed-quadratic-proof Section5
therefore applies unchanged:

    |H|>2^(2R+2)x^2,
    H | (sigma*X-2^R)(2^R*sigma*X+1), sigma=sign(c).

The product's absolute value is smaller than |H|, so it is zero; the
second factor is odd and nonzero. Hence sigma*X=2^R. Set
d=sigma*chi_(a+2)(R). Then d^2=1+Delta*c^2 and H|(d-X-ac).
This restores integral gamma=(d-X-ac)/H for the generalized signed
strong kernel. There is no false odd normalization r_old here.
All remaining kernel rows were unchanged. Its reviewed ordinary native
and refutation theorem now gives a finite syntactic ZFC refutation.

## 5. Completeness with the required quantifier order

Start with the same canonical native witness supplied by a finite
refutation. Choose the joint guard witness t and its nonzero Pell
positivity witness s. The retained interpolation theorem supplies a
single strong pair I,f with4s*c^2|I such that EVERY residue modulo I
can be attained by an auxiliary T. Set r=I/(s*c^2). This is the same
unbounded squared-period theorem as the parent; the period is4*m*f.

The canonical main projection gives H|K from

    (X+ac)^2-(1+Delta*c^2)=K-Hc^2.

Put kappa=K/H. The retained intersectivity theorem for pi gives a
residue a modulo |I| such that pi(a+kappa)=0 modulo I. Choose the
interpolated auxiliary T in that residue, keeping I fixed. Then

    Ac=H^5*pi(T+kappa), Ac/S=pi(T+kappa)/I in Z.

Finally choose n=Ac/S+y+3f+9tau+27g (or delta*y in the integral case).
This is an unrestricted integer and makes a conjugate factor vanish.
No coprimality between H and I or varying strong pair after choosing
the residue is assumed. This proves both existence directions with
the original finite-refutation endpoint, hence the ordinary ZFC-provable
unsolvability/Con(ZFC) equivalence under the same named calibration.

## 6. Exact degrees

The inherited front-end degrees give deg(S)=34, deg(Cy)=82,
deg(delta)=32. The new K has degree9, Ac and Z have degree45.
Thus deg(delta*Z^2)=122; competing cleared integer radicands have
degrees120,134,146. The unique maximal cleared argument is
cn=S^2 Cy of degree150. In the cleared four-root norm its eighth
power is the unique highest contribution, proving degree1200.
For the integral version cn=S^2 delta Cy has degree182 and its
eighth power proves degree1456.

Using the parent's leading notation a0,I0,b0=4I0*T-R0, the two top
forms are respectively

    2^160*a0^144*I0^64*b0^16,
    2^160*a0^176*I0^80*b0^16.

Selecting all T terms gives actual nonzero coefficients

    [j^576 w^144 v^144 s^80 r^80 c^160 T^16] P_rat
       =2^1200*3^720*beta^576,
    [j^704 w^176 v^176 s^96 r^96 c^192 T^16] P_int
       =2^1424*3^880*beta^704.

Their exponent sums are1200 and1456; authentic beta is positive.
These are unbounded degree proofs, supplemented by independent literal
leading calculations and finite line diagnostics when available.
