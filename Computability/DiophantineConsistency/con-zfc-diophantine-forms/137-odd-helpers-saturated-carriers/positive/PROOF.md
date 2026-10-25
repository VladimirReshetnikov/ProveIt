# Canonical saturation of the doubled Pell product square

## Result and source boundary

The complete literal circuits `equation_81.json` and `equation_82.json` each use ten strictly positive integer unknowns. Their respective live binary operation counts and exact total degrees are **81/750** and **82/560**. Both preserve the entire directly indexed BFS943 compact44 coefficient tuple of the pinned Staged Certificates source133 construction. No coefficient is taken from the differently calibrated q-cube source graph.

The new result combines two independently established mechanisms: the canonical q-cube normalization and Pell doubling before product-square elimination. Relative to source133's 84/436 and85/328 equations it saves three operations, at a degree cost. It is not a variable-count improvement, a global minimum, a claim that no solutions exist, or a new Lean/object-ZFC proof artifact. Its ordinary unbounded reduction composes with exactly source133's inherited native/source calibration. The comparison does not claim priority for either constituent mechanism.

## 1. Exact equations

Let beta,K0,MC,MF be the whole literal tuple specified by `coefficients/BINDING.json`. In particular beta is odd and at least31, K0>0, and 0<MC<beta<MF<2beta. The only unknowns are

    J,F,alpha,i,T,w,s,n,eta,zeta in Z_{>0}.

Define these integer polynomials:

    q=beta J+1, h=q-1, X=wq, mu=q^2+1, Y=q^3 s,
    k=eta+zeta, c=kY+eta,
    A=mu Y(X+1)+1, Delta=A^2-1, H=4A-5,
    V0=X mu^2 Y^2, E=1+V0(V0+1)k^2,
    R=[h(q-F)+alpha](q^2-1)+(MC+q MF)J,
    e=k-R-1, C=q-F-alpha, B=(K0+w)C-F,
    U=i c^2, a=Delta U^2 E, F0=1+a, G=E F0,
    Fsq=1+4aF0, Q=Delta(Fsq-1),
    b=c(T+alpha)-R, V=Fsq b-c,
    Kpos=X(3c-2X)+2, M=h mu^2 H.

For the 81-operation equation choose L=V^2. For the82-operation equation choose L=bV. In either case put

    Z=h mu^2[H(n-LB)+Kpos]-H[mu^2 B+h e],
    RG=M^2 G,
    N=Q(Z^2-RG V^2)+(RG-Z^2).

The equation is N=0. All divisions and roots below are proof notation only. In particular delta=Q-1, Dy=QV^2-1 and z=Z/M abbreviate

    N=delta Z^2-M^2 G Dy,
    z=n+kappa-Wt-rho,                         (1)
    kappa=Kpos/H, W=1+hL, t=B/h, rho=e/mu^2.

## 2. Polynomial normalization identity, without a false positivity inverse

Let N_old,Z_old,M_old be the exact source133 polynomials with the matching transport weight. Substitute

    Y_old=q^3 s, n_old=n-s,

and leave the other inputs unchanged. All kernel registers, including L, then coincide. The old rational carrier contained the additional term Y_old/q^3=s; it cancels the shift in n_old. Consequently the following are identities at every integer input:

    Z_old=q^3 Z, M_old=q^3 M, N_old=q^6 N.       (2)

The exponent is6, not12: the product-square output is quadratic, rather than quartic, in the cleared coordinates Z,M. The shift n-s is not always positive. Identity (2) by itself is therefore not a soundness proof. Sections3--5 establish soundness on the actual positive domain directly. The positive converse in Section6 uses the shift in the safe direction.

## 3. Kernel and root recovery, before any transport sign

The new Y is positive. Hence every kernel inequality of source133 remains valid at that Y, without using n,B,C or divisibility of a rational carrier. Specifically q>=32,X>=q,mu>=1025,c>=3,A>4,E>1,U>=c^2,Fsq>c+1,Q>1,H,M>0. For integral b, either b=0 and V=-c, or |V|>=Fsq-c>1. Therefore Dy>0.

Pell doubling supplies the polynomial identities

    Fsq=(1+2a)^2, Q=4 Delta^2 U^2 G.

Thus G divides Q, and both delta and Dy are -1 modulo G. In particular gcd(G,delta Dy)=1. At a zero, delta z^2=G Dy. For every prime dividing G, the other two factors have valuation zero, so the valuation of G must be even. It follows that G=g^2 for a positive integer g, even though M need not be coprime to G. Since F0=1 modulo E, gcd(E,F0)=1, and

    E=tau^2, F0=f0^2, g=tau f0

for positive integers tau,f0. The positive rational y=|z|/g satisfies

    QV^2-(Q-1)y^2=1.                           (3)

The adjacent-Pell descent makes y integral: if y=r/m in lowest terms then m^2 divides Q-1. For v=|V|>1 the norm-preserving transformation

    v'=(2Q-1)v-2(Q-1)y,
    y'=(2Q-1)y-2Qv

has integral v', preserves the reduced denominator m of y', and satisfies 0<|v'|<v, using v<y<Qv/(Q-1). It descends to v=1,y=1. Therefore

    z=epsilon g y, epsilon in {-1,1}.           (4)

Set f=1+2a and I=2Ug. Then f^2=Fsq, f^2-Delta I^2=1, Q=(Delta I)^2 and c^2 divides I. The retained all-index folding theorem, applied to V=-c modulo f and (3), gives c=psi_A(p) for an odd positive p. The first norm gives k=2psi_(2V0+1)(n0). The index n0=1 would put c=2Y+1 strictly between psi_A(1)=1 and psi_A(2)=2A, so n0>=2. Thus k>=8V0+4,c>kY>=k>8q^5,c>X and Kpos>0.

The unchanged mask inequality R<q^4+(alpha+2)q^2 now implies b>c and V>0. Furthermore

    rho<b/mu^2,                                (5)

because b-e=c(T+alpha)-k+1>0. This is only an upper bound; no sign or integrality of rho is assumed.

## 4. Exclusion of negative transport for both branches

All estimates in this section precede rank recovery, q parity, carrier divisibility, and native-source interpretation.

For L=V^2, the exact inequality a^2>G gives g<a. Since b>c>=3,

    V>(Fsq-1)b>ab>3g, V>b,
    y/V<sqrt(Q/(Q-1))<3/2,
    gy<V^2/2.

If the integer B<=-1, Wt<=-V^2-1/h. Solving (1),(4) for the actual positive n and discarding the negative kappa gives

    n=epsilon gy-kappa+Wt+rho
      <V^2/2-V^2+V/mu^2<0,

a contradiction. This handles both signs of epsilon.

For L=bV the source133 fifth-index argument applies unchanged. Since p is odd and c>=3, p>=3 and c>=4Delta+3. Thus V>4Q. Writing Q=S^2, the Pell classification of (3) gives SV=chi_S(j); j is odd, while j=1,3 would give V=1,4Q-3. Hence j>=5 and

    V>=16Q^2-20Q+5>8Q^2,
    b>4Delta^3 I^2>4g.

Therefore gy<(3/2)gV<3bV/8<L/2. If B<=-1, then Wt<-L, so

    n<L/2-L+b/mu^2<0,

again a contradiction for both root signs. Thus both equations force B>=0. Since B=(K0+w)C-F with F>0, C>0.

Removing the old -s term from these bounds is harmless: it had been discarded anyway. We have not asserted positivity of n-s.

## 5. Ordered arithmetic decoding

The source133 kernel, ratio and native-reconstruction interfaces now apply in their original order. They need n to be an integer addend in the carrier after transport, not a positive shifted n-s.

First C>0 gives 3q<R<q^4-2, and the normalized strong-rank and signed auxiliary-index arguments give p=R. Odd p then gives q even and J odd. Only at this point use gcd(mu^2,hH)=1. Since (4) makes the carrier integral, (1) cleared modulo mu^2 gives mu^2|e. The first-index comparison and congruence give n0=(R+1)/2 and the retained strict ratio bounds.

Clearing (1) modulo H gives H|h Kpos and hence H|q^3 h Kpos, exactly the source's weaker projection premise. Its universal projection and whole-product height bound force X=2^R. This uses a bound on the entire product, not cancellation of a potentially nonunit factor modulo H. Therefore kappa is an integer. The remaining fraction in (1) gives Wt integral. Since W=1 modulo h, h|B and t>=0 is integral.

The requirement q^3|Y holds by definition, not by a new inference. Fixed-minus parity, exact half-binomial rounding and the fresh unscaled source reconstruction at Y(X+1)+2 now have all their original hypotheses. They yield the source133 native predicate, hence a finite syntactic refutation through the same whole directly indexed BFS943 coefficient calibration.

Alternatively, after the direct transport proof one can multiply (1) by q^3 and use (2): the retained later arguments are unchanged for integral n_old=n-s. No positivity claim about that shifted coordinate is required.

## 6. Canonical completeness, including native t=0

A finite refutation supplies source133's canonical outer, first and main data, in particular q^3|Y and Y>0. Choose exactly its fresh seed Pell period divisible by c^2 tau, so i>0, then double the seed pair to obtain f,I. Its explicit odd auxiliary witness gives T>0,V,y. None of these choices restricts an arbitrary old zero; this is the canonical existence construction.

Source133 Section8 gives the positive integer

    n_old=gy+Wt+rho-kappa-Y/q^3>0.

Set s=Y/q^3>0 and n=n_old+s>0. Identity (2) then yields q^6 N=N_old=0, hence N=0 because q>0. Every coordinate is strictly positive. Equivalently,

    n=gy+Wt+rho-kappa>0,

since the seed-growth estimate gives g>kappa, and Wt,rho are nonnegative. This includes t=0. No simultaneous independent Pell solvability is assumed: both strong quantities arise by doubling one fresh seed period.

Both directions establish positive-zero equivalence with the retained syntactic-refutation predicate. Consequently, at exactly that ordinary source/native calibration, ZFC proves the equivalence between absence of a positive zero and Con(ZFC). This is not a proof of either side separately and not a newly emitted internal formal endpoint.

## 7. Counts, degrees and attained leading forms

Relative to each source133 evaluator, move q^2,q^3 before the new gate Y=q^3s, delete P=q^3h and the three low-Y carrier gates, and change the five remaining carrier rows. The added multiplication and four deletions save three gates. The materialized counts are81=(48 products,19 sums,14 differences) and82=(49,19,14). Every gate, all ten unknowns and all four fixed ports are live; multiplication by a numeral counts.

The degrees of A,c,U,E,a,F0,G,Fsq,Q,b,V,M,B are respectively

    8,5,11,30,68,68,98,136,152,6,142,13,2.

In the V^2 case Z has degree299, so delta Z^2 has degree750, while M^2 G Dy has degree560. In the bV case Z has degree163, so delta Z^2 has degree478 and the other summand has degree560. Thus there can be no cancellation between the two dominant summands in either equation.

For exact nonvanishing at the authentic tuple, write q0=beta J,k0=eta+zeta,t0=T+alpha,C0=q0-F-alpha. The leading components are

    A0=q0^6 w s, U0=i k0^2 q0^6 s^2,
    E0=q0^22 w^2 s^4 k0^2,
    a0=i^2 q0^46 w^4 s^10 k0^6,
    G0=i^2 q0^68 w^6 s^14 k0^8,
    Q0=4 i^4 q0^104 w^10 s^22 k0^12,
    b0=k0 q0^3 s t0,
    V0_aux=4 i^4 q0^95 w^8 s^21 k0^13 t0,
    M0=4q0^11 w s, B0=w C0.

The attained full homogeneous forms are

    [N81]_750=2^14 q0^506 w^46 s^108 i^20 k0^64 t0^4 C0^2,
    [N82]_560=-2^10 q0^384 w^34 s^80 i^14 k0^46 t0^2.

For N81 choose the coefficient of J^506 w^46 s^108 i^20 eta^64 T^4 F^2: it is2^14 beta^506>0. For N82 choose J^384 w^34 s^80 i^14 eta^46 T^2: its coefficient is-2^10 beta^384<0. Their total degrees are750 and560. All claims concern the complete specialized polynomial, not generic ports or only a numerical ray.

## 8. Verification and boundaries

`python -B build.py --check` verifies exact deterministic circuit reconstruction. `python -B verify.py` independently checks topology/liveness/counts, every coefficient byte hash and bit length, the whole tuple, graph versus separately written formulas, complete normalization with exponent6, degree upper bounds and exact leading forms on modular polynomial rays, local Pell identities, rational extraction controls, and actual-gate mutations. Repeat both under Python -O. Tests supplement the unbounded proof above; they do not decide consistency or replace the inherited number-theoretic/calibration theorems.
