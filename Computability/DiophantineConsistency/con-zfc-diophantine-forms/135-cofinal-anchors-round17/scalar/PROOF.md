# Linear cofactor saturation in eleven unrestricted integers

## Result and mathematical boundary

The principal equation below has eleven unrestricted integer variables, exact total degree 328, and 130 live binary arithmetic operations. Its free-scale direct and simple-center companions have degree/cost pairs 352/125 and 340/129. A weak-scale direct equation gives 398/121. These improve the inspected incoming eleven-integer frontier; they are not global minimum claims. The other weak-scale variants, 382/125 and 366/126, are dominated by 352/125 and are retained only as comparisons.

The new arithmetic device places the factors A and Dm inside a linear free cofactor B=r A Dm. A single square-product condition then recovers the square of B, the strong Pell norm, and the auxiliary norm. There is no separate square condition on r or Dm. The previously known main-radicand saturation used a squared free multiplier and an extra factor A; the new construction lowers both the strong norm and the auxiliary coordinate. An exact sharp center removes two further powers of A. The guard uses the round16 modulo-sixteen nonsquare argument, extended here to the free-scale budget.

Every unbounded implication needed for the new transformation is proved below. The signed Pell/rank, intersective-quintic, supported-modulus interpolation and native/compiler/refutation calibration are explicitly retained ordinary mathematical dependencies. Their relevant hypotheses are restored before use. No new proof of consistency, encoded object-ZFC derivation or end-to-end proof-assistant endpoint is asserted.

## 1. Complete ordinary polynomials

All eleven independent variables j,C,z,h,r,v,w,T,c,n,s range over Z. The six ports beta,K0,MC,MF,cone_A,cone_B are fixed numerals, with the complete compressed little-endian payloads and finite reconstruction recipe in coefficients/. They are not additional unknowns. In particular beta=2^1064921-1, cone_A=2^1113, cone_B=2^666104, and MF is already shifted by beta.

For the free-scale family define the following polynomial abbreviations:

    J=6j+1, q=beta J+1, W=12w+4, X=qW, Y=v,
    E=XY, a=E+Y, A=a+2, H=4a+3, Delta=a^2+H=A^2-1,
    F=(K0+W)C-z(q-1),
    R=[q(q-F)-C](q^2-1)+(MC+q MF)J,
    k=R+1+hE, eta=c-Yk,
    Derr=(cone_A F-q)^2+(cone_B C-q)^2,
    B0=k^2(q^2-Derr)-4q^2 eta^2,
    Budget=Y^2 B0-k^2 q^8,
    D=Budget-4, ell=XY^2, Dt=1+ell(ell+1)k^2,
    Dg=1+D Dt s^2, P=Dt Dg,
    Dm=1+Delta c^2,
    B=r A Dm, U=r c^2 Dm,
    I2=c^4 B=A c^2 U,
    Df=1+Delta I2, Q=Delta^2 I2, delta=Q-1,
    V=Df(c-R+4A U T)-c, Cy=QV^2-1, Da=delta Cy,
    K=X(3c-2X)+2,
    M=2q^3, Dc=HM, S=srH M^5,
    zc=Dc T+M K+H(v-q^3),
    Ac=(zc^2+3Dc^2)(zc^3-19Dc^3).

The sharp equation uses lambda=(2Delta+1)U. The simple-center equation uses lambda=2A^2U. The direct equation uses lambda=0. In every case put

    Z=S(n+lambda V)-Ac,
    pa=delta Z^2, pb=delta S^2 P, pc=4S^2 B Df Cy,
    N=(pa+pb-pc)^2-4pa pb.                              (1)

Equation N=0 is the complete integer polynomial. All symbols are abbreviations, not quantified variables. There are no divisions, radicals or variable exponents in its DAG.

For the weak-scale family use Y=qv, Budget=B0, M=2q^2 and zc=HM T+M K+H(v-q^2). All other formulas remain the same.

The literal implementation shares P=Dt+(Budget-4)(Dt s)^2, L=E(Yk), and

    Budget=(Yk)^2(q^2-Derr)-q^2[4(Y eta)^2+(kq^3)^2]

in the free-scale family. It shares Delta c^2 between Dm and Df. These are identities, not semantic replacements. The three choices of center are integral polynomial shears of n and preserve integer-zero existence with explicit inverse shears.

## 2. Unconditional arithmetic and the guard

The authentic affine restrictions give q even, q=2 modulo3, |q|>=beta-1>=16, X=0 modulo8, X=2 modulo3 and |X|>=4|q|. H is odd and nonzero. If Y=0, a=0, A=2 and Delta=3. Otherwise |a|>=|X|-1>3. Thus A!=0, Delta>1 and Dm>=1 on every integer assignment. Also a=0 modulo3, hence A=2 modulo3 and Delta=0 modulo3.

Dt>=1 since ell(ell+1)>=0. Since ell is a multiple of8, Dt=1 modulo8. Put ucone=cone_A F and vcone=cone_B C. Both are multiples of16. Expansion gives

    B0+(qk)^2
      =k^2[2q(ucone+vcone)-ucone^2-vcone^2]-4q^2 eta^2
      =0 modulo16.

Consequently B0=0 or12 modulo16. In the free family q^8 is divisible by16, so Budget=-(qkY)^2 modulo16, again 0 or12. In the weak family Budget=B0. Hence, for both families,

    D=8 or12 modulo16.                                (2)

D is nonzero, divisible by4, and never an integer square. Dg=1 modulo4, P=1 modulo4, and neither vanishes. These facts do not assume positivity or Pell solvability.

Q cannot equal1 because it is divisible by Delta^2>1. Df cannot vanish because Df=1 modulo Delta. Thus delta and Cy never vanish. In addition Q is even and delta odd. To see this for all A,c,r, if A is odd then Delta is even; if A is even, Delta is odd, and c^4 A Dm is even. No parity restriction on Y is used.

The rational polynomial pi(t)=(t^2+3)(t^3-19) has no rational zero. Dc!=0, and Ac=Dc^5 pi(zc/Dc), so Ac!=0. At S=0, equation (1) becomes delta^2 Ac^4!=0. Every zero has S!=0 and thus s,r!=0. Consequently B=r A Dm is nonzero.

Da is strictly positive without assuming the sign of B. If c=0 then Q=0 and Da=1. If c!=0 and B<0 then Q<0, so delta and Cy are both negative. If c!=0 and B>0 then Q>1 and Df=1+Delta c^4 B>|c|+1. Writing V=Df b-c for an integer b, b=0 gives |V|=|c|>=1, and b!=0 gives |V|>=Df-|c|>1. Therefore Cy>0. Finally, B Df is positive whenever c!=0, because B and Df have the same sign. The only possible negative case for Cstar=B Df Da is c=0 with B<0.

## 3. Two squareclasses and the linear cofactor

Over a field containing the relevant complex square roots, equation (1) is delta^2 times the four-factor norm with radical terms

    2S sqrt(B Df Cy/delta),   S sqrt(P).

The radicand B Df Cy/delta equals Cstar/delta^2. Thus a zero gives a rational signed sum of 2sqrt(Cstar) and delta sqrt(P), after division by nonzero S and multiplication by delta.

Neither Cstar nor P is zero. If exactly one is negative, its nonzero imaginary term cannot cancel. If both are negative, the preceding section gives c=0, delta=-1 and Cstar=B. Cancellation then requires 4B=P, impossible since P=1 modulo4. Thus Cstar>0 and P>0.

Both are integer squares. Indeed, write each positive integer as a square times a positive squarefree integer. Different nontrivial squarefree radicals are independent over Q. If both terms have the same nontrivial squarefree part, the coefficient of 2sqrt(Cstar) is even, while that of delta sqrt(P) is odd: P is odd and delta is odd. They cannot cancel. If either nontrivial class occurs alone it cannot be rational either. Therefore both squareclasses are trivial.

The three nonzero integer factors B,Df,Da are pairwise coprime. Since Q is a multiple of B and Df=1 modulo B,

    gcd(B,Df)=1, Da=1 modulo B.

Modulo Df one has Q=-Delta, delta=-A^2, V=-c, Cy=-Dm and hence Da=A^2 Dm. Since B=r A Dm, Df=1 modulo A and modulo Dm. Therefore gcd(Df,Da)=1 as well. These statements remain valid with negative B or Df.

Since B Df Da is a positive square and Da>0, the absolute values of B,Df,Da are individually squares and B,Df have the same sign. But Df=1 modulo3, while a negative integer square is 0 or2 modulo3, never1. Thus B and Df are positive. Choose positive integers u,f,e with

    B=u^2, Df=f^2, Da=e^2.                             (3)

Notice carefully what has and has not been concluded: B=r A Dm is a square, not necessarily r or Dm individually. The proof needs only B.

Since gcd(Dt,Dg)=1 and Dt>=1, positivity and the square condition on P give Dt=tau^2 and Dg=g^2 with positive tau,g. Because s!=0, Budget<=3 would imply Dg=1+D Dt s^2<=0, impossible. Thus Budget>=4, strengthened by (2) to Budget>=12.

For the free family this gives k!=0, Y!=0 and B0>0. As B0<=k^2q^2,

    Y^2 B0>k^2 q^8 implies |Y|>|q|^3.                 (4)

For both families the standard centered disk consequences of B0>0 give Derr<q^2, |c/k-Y|<1/2, and the common nonzero sign of q,F,C,q-F-C. In the free family (4) already excludes c=0. The inherited packing bounds are

    |q|(|q|^2-1)<R<|q|^4-2.                            (5)

## 4. Integral auxiliary root and carrier divisibility

Define proof-only integers

    I=c^2 u, T_old=uT.

By (3), f^2-Delta I^2=1, Q=(Delta I)^2, and

    V=f^2(c-R+4I T_old)-c,                             (6)

because A U=c^2 B=c^2u^2. In particular c^2|I. When c!=0, I!=0 and |I|>=c^2. The rational y=e/delta satisfies

    QV^2-(Q-1)y^2=1.                                  (7)

If c=0, Q=0, e=1, delta=-1 and y=-1 is integral. Otherwise Q>1. The retained adjacent-coefficient denominator descent makes y integral: if its reduced denominator is b then b^2 divides Q-1. The integral unimodular transformation

    V'=(2Q-1)V-2(Q-1)y,
    y'=(2Q-1)y-2QV

keeps V' integral, preserves that denominator, and after signs reduces |V| until |V|=1. Indeed V>1 implies V<y<QV/(Q-1), hence -V<V'<V, and the norm excludes V'=0. At |V|=1 one has |y|=1, forcing b=1.

The normalized roots in the four-factor equation are now the integers 2ufy and tau g. Hence Z/S is an integer. The center lambda V is an integer polynomial, so

    S divides Ac.                                     (8)

This conclusion also holds before c!=0 in the weak family, avoiding circularity in its scale restoration.

## 5. Scale restoration and exact native source recovery

The free-scale carrier and strengthened budget are inherited from source/FREE_SCALE_PROOF.md, with the fifth-power strengthening retained in source/INCOMING_MAIN_SATURATION_PROOF.md. Here are the complete relevant steps.

Since M^5 divides S, it divides Ac. If p^e exactly divides M and v_p(zc)=b<e, the zc^5 term in

    Ac=zc^5+3Dc^2 zc^3-19Dc^3 zc^2-57Dc^5

has valuation 5b, strictly less than every other term. This contradicts p^(5e)|Ac. Thus M|zc and

    M | H(v-q^3)                                      (free family).

Its 2-primary part, with H odd, gives Y=v even. Also H|Ac and zc=MK modulo H give H|(MK)^5. Put Kq=X(X+2ac)-1. The identity K=HXc-2Kq and odd H yield

    H | q^15 Kq^5.                                    (9)

The omitted main root is recovered before signed rank is invoked. Put Babs=|A|, Cabs=|c|, Iabs=|I|. We have Babs>=3, 0<Cabs<=Iabs, and f^2-(Babs^2-1)Iabs^2=1. Write f=chi_Babs(m), Iabs=psi_Babs(m); then f>2Iabs. Put rho=(Babs^2-1)Iabs. The auxiliary norm classifies rho|V|=chi_rho(nu), |y|=psi_rho(nu); nu is odd because an even-index abscissa is plus or minus1 modulo rho. The odd quotient-polynomial identity and V=-c modulo f give psi_Babs(nu)=plus or minus Cabs modulo f. Fold nu modulo2m and reflect to 0<=p<=m. Since psi_Babs(p)+Cabs<=2Iabs<f, this congruence cannot wrap and forces Cabs=psi_Babs(p), p>=1. This is the absolute folding argument retained in source/signed-quadratic-proof.md Section2 and source/SELECTIVE_FUSION_PARENT.md Section3. It does not require an odd multiplier, a sign of A or c, or a main projection. In particular Dm has now been shown to be an integer square, rather than assumed to be one.

The signed rank theorem now has its complete pre-projection hypotheses: the centered signs and strip, |Y|>|q|^3, even Y, Dt=tau^2, the strong pair (6), c^2|I and I!=0, and V=-c modulo f and V=-R modulo c. The second residue follows immediately from (6). The first-index congruence uses |XY|>3R+1, which follows from (4),(5) and |X|>=4|q|. The theorem does not assume I/c^2 odd and does not require the incoming main radicand Dm to be a separately supplied square. It recovers the main Pell coordinate from the strong and auxiliary norms, as in source/centered11-proof.md Section5.2 and source/INCOMING_LINEAR_MULTIPLIER_PROOF.md Section4.

It yields c=sign(c) psi_A(R), R=2t+1, and

    |Y|>(|X|-3)^t/2-1, |H|>|X|(|X|-3)^t.

The bound (5), with |q|>=16, gives t>=36 (in fact much larger). Write x=|X|, sigma=sign(c), and Pi=(sigma X-2^R)(2^R sigma X+1). The inherited signed Pell projector says 2^R Kq=Pi modulo H. Equation (9) gives H|q^15 Pi^5. Each factor of Pi is less in absolute value than 2^(R+1)x, so

    |q|^15 |Pi|^5<2^(20t-10)x^25,
    |H|>x^(t+1)/2^t.

Since the actual x>=2^64 and 64(t-24)-(21t-10)=43t-1526>=22, the divisible integer has absolute value below |H|. Thus Pi=0. Its second factor is odd and nonzero, so sigma X=2^R.

Now q|X makes |q| a power of two. H is odd, so gcd(H,M)=1. The early carrier divisibility finally gives M|v-q^3, restoring

    Y=(2v_old+1)q^3.

The exact projector also gives H|Kq and H|K. Since X=2 modulo3 and R odd, sigma=+1 and X=2^R. The retained first-index sign and centered orientation give k,Y,c>0, and its uniform half-binomial theorem gives 0<eta/k<1/4.

For the weak family, q divides Y from the start, H=3 modulo q and gcd(H,2q^2)=1. The same valuation argument immediately restores v=q^2(2v_old+1), so Y=(2v_old+1)q^3, and also H|K^5. This excludes c=0 from B0>0. The same signed rank theorem applies; the ordinary fifth-power projection bound without the extra q^15 factor suffices (already for t>=24). Its source restoration is identical thereafter.

For precision about the final source handoff, the retained nonodd strong-rank lemma obtains the main Pell index p from |c|=psi_|A|(p), |I|=psi_|A|(m): c^2|I implies p|m, c|m/p, then c|m and m>2p. It uses no odd multiplier hypothesis. After orientation its literal native restoration keeps the outer coordinates and constructs fresh I_star=psi_A(Rc), f_star=chi_A(Rc), rho_star=Delta I_star. Since A is even and R,c odd, I_star and rho_star are odd; composition gives c^2|I_star. Hence r_old=(rho_star/c^2-1)/2 is integral. With t=(R-1)/2, take V_star=(-1)^(t+1)Q_t(rho_star^2), y_star=psi_rho_star(R), using the odd quotient Q_t(z^2)=chi_z(2t+1)/z. The exact residues V_star=-c modulo f_star^2 and V_star=-R modulo c produce the old private coordinates. Together with the recovered positive strip and the square coordinate 2^((R-1)/2), these give an actual old signed Q41 zero. Only this restored zero is passed to the retained source34/native/compiler/finite-syntactic-refutation calibration.

## 6. Converse with one fixed strong pair

Start with a finite syntactic ZFC refutation and the retained canonical outer source witness. In the free family set v to the canonical Y; in the weak family set v=q^2(2v_old+1). Keep all outer values. They give A>0 even, Dm=d^2 with d>0, c=psi_A(R)>0, Dt=tau^2, B0>q^2 k^2/4, and Y>X=2^R>4q^3. Therefore the free Budget exceeds64, and the weak Budget=B0 also exceeds64.

By (2), D=Budget-4 is positive and nonsquare. Dt=tau^2 is a nonzero square, so D Dt is positive nonsquare. Ordinary Pell existence supplies s,g>0 with g^2=1+D Dt s^2. Fix these.

Choose ONE positive strong Pell pair I,f with

    4s A d c^2 | I, f^2-Delta I^2=1.

The retained finite matrix-period construction permits this. Define

    t_strong=I/(A d c^2), u=I/c^2=A d t_strong,
    r=A t_strong^2.

All are positive integers. Then r A Dm=u^2, exactly B=u^2, and I2=I^2. Keep this pair I,f fixed for every subsequent step. Every prime dividing u s r divides I: this holds separately for A,d,t_strong and s by the chosen divisibility. Thus the supported-modulus interpolation theorem applies to the modulus u s r, not just to a modulus dividing I.

The exact canonical projector gives H|K. Put kappa=K/H. In either family the carrier has

    zc=HM(T+kappa+v_old),
    Ac/S=H^4 pi(T+kappa+v_old)/(sr).

The intersective quintic pi has a root modulo every positive integer. Choose a0 modulo sr with pi(a0+kappa+v_old)=0 modulo sr. Apply supported-modulus interpolation to the SAME fixed strong pair with

    T_old=u a0 modulo u s r.

It supplies an integral auxiliary y. Hence T=T_old/u is an integer and T=a0 modulo sr. Formula (6) is then exactly the polynomial auxiliary expression, and Ac/S is integral. Finally set

    n=Ac/S+2u f y+tau g-lambda V.

Every input is integral, and one factor of the four-factor norm vanishes. This proves completeness. The choice order is outer data, guard s/g, one strong pair I/f, u/r, intersective residue, interpolated T_old/y and T, then n. The strong pair is never reselected after a residue is requested.

Soundness and completeness establish the integer-zero equivalence with the retained calibrated source. Composing its explicitly identified ordinary theorem, ZFC proves that universal nonvanishing of each fixed displayed polynomial over Z^11 is equivalent to syntactic Con(ZFC). This does not prove either side true.

## 7. Exact degrees and actual leading coefficients

For free scale the important exact degrees are

    a3, Delta6, k5, B0_14, Budget18, Dt18, P56,
    Dm8, B12, U11, I2_16, Df22, Q28, V37, Cy102,
    M3, Dc6, S20, Ac35, lambda17, Z74 (sharp/simple).

For weak scale they are

    a4, Delta8, k5, Budget16, Dt22, P62,
    Dm10, B15, U13, I2_19, Df27, Q35, V45, Cy125,
    M2, Dc6, S16, Ac35, lambda21, Z82 (sharp/simple).

The cofactor relation B Df=B+Delta A^2 U^2 gives the exact center identities

    lambda^2-4B Df=U^2-4B                    (sharp),
    lambda^2-4B Df=4A^2 U^2-4B               (simple).

Put W0=Sn-Ac and denote the appropriate right side by diff. The complete cancellation identity is

    pa+pb-pc = delta W0^2+2delta S lambda V W0+delta S^2P
              +S^2{[delta diff-4B Df]V^2+4B Df}.       (10)

The unique highest term in the sharp inner bracket is S^2 Q U^2 V^2, with degree164/free or183/weak. In the simple center it is 4S^2 Q A^2 U^2 V^2, with degree170/free or191/weak. The correction 4pa pb has degree300/free or328/weak, strictly below the respective squared-inner degrees. For the direct form pc uniquely dominates, of degree176/free or199/weak. This proves degrees328,340,352 and366,382,398.

For entire leading forms put q0=6 beta j, X0=12q0w, Y0=v/free or q0v/weak, a0=X0Y0, and e=15/free or10/weak. Then

    S0=128sr a0 q0^e, B0_top=r a0^3 c^2,
    U0=r a0^2 c^4, Df0=r a0^5 c^6,
    Q0=r a0^7 c^6, V0=4r^2 a0^8 c^10 T.

The entire highest homogeneous form is the following single monomial:

    sharp:  2^36 s^4 r^18 c^68 T^4 q0^(4e) a0^58,
    simple: 2^40 s^4 r^18 c^68 T^4 q0^(4e) a0^62,
    direct: 2^40 s^4 r^18 c^68 T^4 q0^(4e) a0^66.

In particular the actual degree328 coefficient is

    [j^118 w^58 v^58 s^4 r^18 c^68 T^4] N
         =2^270 3^176 beta^118 >0.

The direct free coefficient is 2^298 3^192 beta^126 at j^126 w^66 v^66 s^4 r^18 c^68 T^4. The weak direct coefficient is 2^344 3^238 beta^172 at j^172 w^66 v^66 s^4 r^18 c^68 T^4. Every exponent sum equals its stated degree. These are exact whole-polynomial proofs at the authentic coefficient tuple, not generic coefficients or numerical line samples.

## 8. Portable checks and inherited dependencies

build.py produces the six explicit live arithmetic DAGs. check.py does not import the producer or its circuit module. It independently binds every local polynomial register and live arithmetic gate, expands all four conjugate factors, proves the center and cofactor remainder identities, authenticates all six decompressed coefficient payloads and reconstructs their complete finite recipe, recounts topology/liveness/operations, and propagates a nonzero actual leading coefficient through every node. The only cancellation cut is (10), checked as a free-ring identity and with a unique highest weighted term. The complete per-node attained-leading ledger is emitted alongside the summaries. Coefficient bytes are authenticated, and altered literal, variable, degree and selected formula controls are rejected by explicit runtime checks, including under python -O.

Finite tests are regression controls only. They do not replace the unbounded Pell, interpolation, intersectivity or logical calibration arguments. The full source directory retains those ordinary dependencies, including the nonodd signed-rank argument, the powered saturation interpolation proof, the incoming free-scale proof, and the incoming linear-multiplier proof. SOURCE_PINS.json authenticates their actual bytes. The coefficients, recipe, provenance and license notices are included for portable replay.
