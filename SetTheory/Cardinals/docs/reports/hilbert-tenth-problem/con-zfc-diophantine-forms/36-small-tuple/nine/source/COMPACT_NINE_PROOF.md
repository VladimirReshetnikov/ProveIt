# Nine-variable equation from the compact coefficients and the 31-variable quartic

## Result and scope

At the pinned ProveIt revision ae3007ca4467011e0e051c84acb4a1dd13971b0e, combine the Jones nine-witness reduction with the new 31-positive-variable, 22-quadratic parent and the complete compact943 compiler tuple. The resulting equation is an ordinary integer polynomial in exactly nine nonnegative integer unknowns. Its final circuit is `nu31/nine_compact_magnitude_tight.json`.

* Exact total degree: `120724 * 5^32 + 366 = 2810824662446975708007812866`.
* Live binary operations: 1,840 = 715 additions + 22 subtractions + 1,103 multiplications.
* Variable leaves: nine. Fixed leaves: 404 = 402 weighted coefficient constants, z, and y.
* The four underlying compiler integers are actual materialized integers, totaling 5,312,269 raw bytes or 20,260 deterministic-gzip bytes.
* The new index constant is the actual integer z=2^45933757. Its materialization occupies 5,741,720 raw bytes or 5,613 gzip bytes. Its SHA-256 is d2b21c2c280cd06b3f233616ce4add5fd554f3d9178baa4ef7923826a3b1e100.
* The 402 weighted coefficients and the much larger index y are bounded explicit recipes, not materialized integers in this package. No coefficient is an existential parameter.

This is an ordinary mathematical proof using the previously identified native/Pell compiler, literal K215 calibration, and Jones arithmetic theorems. The new algebra and finite audits are not a new end-to-end proof-assistant theorem. They neither decide consistency nor supply a halting/refutation witness.

## 1. Coherent compiler binding and the parent quartic

The authoritative binding is the COMPLETE compact943 tuple, not the historical t-shape default metadata carried by the inert source:

    beta = B_native-1;
    K0 = K = DC+B_native*DR;
    MC = compact data mask;
    MF = MF_source = MF_native+B_native-1;
    B_native = 2^(5^10).

All four values must come from the same compact943 instance. `nu31/COMPACT_COEFFICIENT_BINDING.json` and the round-three compiler proof give the finite 943-tile recipe, exact masks, geometry, and verified bytes. In particular the verified interface includes the no-carry bounds, balanced mask populations, two-band rotation separation, unique anchor synchronization, mod-5 unit 2DC-DR=4, actual-rank dummy control, positive slack, and canonical odd/square-scale completeness. MF is never the unshifted native mask. The machine table and language are the same exact K215 blank-halt language, not a new machine-input parameter.

The old 32-variable source already uses exactly this abstract four-port arithmetic interface. The new parent removes its register G. Write, in this parent paragraph only,

    q=beta J+1, C=q-F-alpha, G=(q-1)(q-F)+alpha.

Its retained quadratic equation N=q(L_parent+1) implies

    G=q(q-F)-C;
    L_parent G=(q-F)(N-q)-C L_parent.

Thus the G definition and old packing equation are replaced by the single quadratic packing equation

    jc-V=(q-F)(N-q)-C L_parent+(MC+q MF)J.

Every other residual is unchanged. Conversely recover G from its displayed formula. G is positive: the literal retained transport equation gives

    (K0+w)C+(q-F)=1+z_parent(q-1)>=q.

If C<=0, the left side is at most q-F<q, a contradiction. Hence C>0, q-F=C+alpha>0, and G=(q-1)(q-F)+alpha>0. This establishes both directions on the required positive domain, with no change of the source quotient convention. The new system has 31 positive variables and 22 quadratic residuals r_j.

Define P31(x,n)=sum_j r_j(n+1)^2, independent of its dummy input x. The fifth residual is E*X+E-a*X and equals 1 when all positive coordinates equal 1. Therefore P31(x,0)>0 for every x, independently of the four compiler values. Its degree is exactly four since the coefficient of tau^4 is 1. The literal sparse parent is `../arithmetic/quartic31.json`; its SHA-256 before any nonalgebraic metadata editing is 1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287.

The parent-to-K215 equivalence remains the imported arithmetic/compiler theorem, now transported by the exact G elimination. K215 blank halting is equivalent to finite syntactic ZFC refutability by the identified literal-machine calibration. Those ordinary arguments are formalizable in ZFC; this package does not claim their rechecking inside a newly built Lean/Rocq kernel.

The Jones parameter nu counts parent-quartic witness variables. It is now 31, not 9. The unrelated native fixed radix B_native=2^(5^10) cannot justify setting nu=9. A normalized quartic in nine witnesses and its admissible index would be needed for that substitution. No such reduction is claimed.

## 2. Explicit index without an uninstantiated recursive-enumeration index

Set nu=31 and L=5^32. Expand P31 in the 32 coordinates (dummy x plus 31 witnesses). For alpha in N^32 with |alpha|<=4 let p_alpha be its ordinary coefficient and put

    c_alpha=(4-|alpha|)! * product(alpha_j!) * p_alpha;
    expo(alpha)=sum_(j=0)^31 alpha_j*5^j.

There are exactly 402 nonzero symbolic coefficient records, each explicitly a small polynomial in (beta,K0,MC,MF). They are listed in `nu31/COMPACT_CONSTANTS.json`. Unlisted c_alpha are zero. The independent expansion has 675 terms when the four ports are retained symbolically. All exponent powers in the records are ordinary fixed nonnegative integers.

The authentic port bit lengths, in this order, are

    (9765625,13201251,9765625,9765626).

For each record c_alpha=sum_t a_t product port_j^(e_tj), define the completely explicit integer upper bound

    H_alpha=sum_t |a_t| * 2^(sum_j e_tj * bitlength(port_j)).

The actual absolute coefficient is at most H_alpha. Exact finite integer arithmetic verifies, for every one of the 402 records,

    H_alpha+1 < 2^45933757.

The sparse powers-of-two certificate is `nu31/INDEX_BOUND_CERTIFICATE.json`; it does not require materializing any quartic coefficient. Set

    z=2^45933757;
    u=sum_(j=1)^31 (2z)^(5^j);
    y=sum_(|alpha|<=4) (z+c_alpha)(2z)^(L-expo(alpha));
    e(T)=sum_(|alpha|<=4) (z+c_alpha)T^(L-expo(alpha)).

The y sum has exactly binomial(36,4)=58,905 terms. All digits z+c_alpha lie strictly between 1 and 2z, and the exponent positions are distinct by base-five uniqueness. Hence y is a positive integer, 2(2z)^L <= y < (2z)^(L+1). In particular it has at most 45,933,758*(5^32+1) binary digits. The unused u is explicit as well; it is not a polynomial leaf or unknown.

These definitions satisfy precisely `Jones1982.Index 31 P31 z u y`: z is a power of two, |c_alpha|+1<z, and u,y are the specified lpoly/epoly evaluations. P31 is normalized, has degree <=4, nu>=1, and the chosen input is x=1>0. These are exactly the hypotheses of `Jones1982.Nine.wset_iff_nine`, rather than a misuse of the public generic theorem whose convenience proof passes through a 58-variable quartic.

## 3. The literal nine-coordinate equation

The nine unknowns are

    epsilon,g0,h0,s0,w0,phi,i0,j0,n in N.

Set g=g0+1, h=h0+1, s=s0+1, w=w0+1, i=i0+1, j=j0+1. Every symbol below is only a polynomial abbreviation. Define

    b=y+1+epsilon, B=b^5, q=B^L;
    ell=sum_(r=1)^31 B^(5^r), lambda=sum_(r=0)^(4L-1) B^r;
    e=e(B), theta=B-2z, N=q^16, Gcap=32b B^(5^31);

    R=[g+e q^3+ell q^5+
       (2(e-z lambda)(1+B+g)^4+lambda B+lambda B q^4)q^7](N^2-N)
      +[q^3-b ell+ell+theta lambda q^3+(B-2)q^8](N^2-1).

Continue with exactly the Jones ratio expressions:

    U=N^2 w, Y=N^2 s, M=R Y, P=2M^2 U;
    K=R+1+h(P-1), A=M(U+1), B1=2R+1, W1=bw;
    C=B1+W1+phi, J=4A-5, Q=3W1 C-2(W1^2-1);
    D=(A^2-1)C^2+1, E=i J D C^2, F=(A^2-1)E^2+1;
    G1=A+F(CD+1-A), H=B1+jC, I=(G1^2-1)H^2+1;
    a0=(P^2-1)K^2+1, a1=DFI;
    d=(JF)^2, c=(QF+J(H-C))^2;
    m=K^2 Gcap-4(C-KY)^2 Gcap-8gK^2.

The d,c here are respectively the divisor and dividend, not parent coordinates or coefficient records.

The new magnitude companions are

    deltaR=32 z lambda g^4 q^7 (N^2-N), Rbar=R+deltaR;
    Kbar=Rbar+1+h(P+1), Abar=Rbar Y(U+1);
    Cbar=2Rbar+1+bw+phi, Jbar=4Abar+5;
    Dbar=(Abar^2+1)Cbar^2+1, Ebar=i Jbar Dbar Cbar^2;
    Fbar=(Abar^2+1)Ebar^2+1;
    Gbar=Abar+Fbar(Cbar Dbar+1+Abar), Hbar=2Rbar+1+jCbar;
    V0=(P+1)Kbar+2;
    V1=((Abar+1)Cbar+1)((Abar+1)Ebar+1)((Gbar+1)Hbar+1)+1.

Finally define

    Omega=d(2m-1);
    Theta=dn+c-Omega(c+V0 V1);
    F9=(Theta^2-Omega^2(a0+V0^2 a1))^2-4 Omega^4 V0^2 a0 a1.

The single requested equation is F9=0. Every exponent in the entire display is fixed. There are no divisions, radicals, variable exponents, or additional quantified variables in the equation.

## 4. Noncircular magnitude bounds, including negative packed ranks

All following inequalities hold on EVERY natural assignment of the nine inputs, before any zero or square condition is assumed. The admissible index gives b>=2, B>=4, B>2z, and e(B)>0. Since the exponents in ell are a subset of 0,...,L-1,

    ell <= (q-1)/(B-1), and b<=B-1, hence b ell<q.

Thus the entire right bracket in R is positive. Put u0=B+1. The elementary convexity inequality (u0+g)^4<=8(u0^4+g^4) holds for nonnegative u0,g. Also

    16z(B+1)^4 < 128 B^5 < B^9 <= B q^4,

using B>2z, B>=4, and L>=2. The positive lambda B q^4 term in the left bracket therefore absorbs 16z lambda(B+1)^4. Consequently

    R+16 z lambda g^4 q^7(N^2-N)>=0.

The added term is nonnegative, so Rbar=R+32 z lambda g^4 q^7(N^2-N) dominates both R and -R. Thus Rbar>=|R| without assuming R positive. This is the key improvement over simply replacing every minus sign by a plus sign.

P=2M^2U is nonnegative. The displayed companion formulas then give, successively,

    Kbar>=|K|, Abar>=|A|, Cbar>=|C|, Jbar>=|J|,
    Dbar>=|D|, Ebar>=|E|, Fbar>=|F|,
    Gbar>=|G1|, Hbar>=|H|.

These follow only from triangle inequalities and nonnegative products. For real a,b,

    sqrt(|(a^2-1)b^2+1|) <= (|a|+1)|b|+1.

Indeed the squared right side exceeds (a^2+1)b^2+1, which already bounds the absolute radicand. Therefore V0,V1>=2 and

    sqrt(|a0|)<=V0-1, sqrt(|a1|)<=V1-1.

Unlike the baseline all-integer majorant lemma, this improved weight lemma is asserted only on the natural input domain with the specified valid index. That is exactly the domain needed by the nine-witness equivalence. It never assumes the desired margin, divisibility, squarehood, or R positivity.

## 5. Exact sign/root finalizer proof

J=4A-5 is a nonzero integer. Also F cannot vanish: if (A^2-1)E^2+1=0, then (1-A^2)E^2=1 forces A=0 and E=+/-1; but E=iJDC^2 is then divisible by 5, impossible. Hence d=(JF)^2>0 and c>=0, while Omega=d(2m-1) is nonzero at every integer assignment.

Choose formal complex roots r0^2=a0,r1^2=a1. Direct multiplication yields

    F9=product_(sigma,tau in {-1,1}) [Theta-Omega(sigma r0+tau V0 r1)].

If F9=0, absorb the signs of a vanishing factor into r0,r1. Then s*=Theta/Omega=r0+V0r1 is rational. If s*!=0, the identity 2s*r0=s*^2+a0-V0^2 a1 makes both roots rational. If s*=0, |r1|=|r0|/V0<1, so the integer |a1|<1, forcing a1=a0=0. In either case the roots are rational, hence integers since their squares are integers. This proof covers negative candidate radicands, zero roots, and repeated square classes.

Set Z=c+V0V1+r0+V0r1. The established root bounds give Z>=c+1>0. The vanishing factor reads

    dn+c=d(2m-1)Z.

It implies d divides c and m>0. Conversely, if a0,a1 are squares, d divides c, and m>0, choose their integer roots and define

    n=(2m-1)Z-c/d.

This is a nonnegative integer (indeed >=1), and its factor vanishes. Finally (JF)^2 divides (QF+J(H-C))^2 iff JF divides QF+J(H-C). Thus existential elimination of n gives EXACTLY the original two square tests, one divisibility test, and positive margin.

The source theorems `Nine.reduced_of_mem`, `Nine.mem_of_reduced`, `Nine.ratio_complete`, and `Nine.ratio_sound` retain their literal arithmetic expressions. Only the final weights and the witness n change. Therefore the new F9 has a natural zero iff P31 has one, iff the compact native compiler accepts a blank K215 computation, iff there is a finite ZFC refutation. Negating gives, provably by the stated ordinary mathematics in ZFC,

    (there is no natural nine-tuple with F9=0) iff Con(ZFC).

## 6. Exact degree, not merely a naive upper bound

Write L=5^32. The dominant R term is +lambda B q^4 q^7 N^2, of degree 235L; the apparently large negative quartic term is lower degree. Selected ordinary degrees are

    R:235L; P:950L+3; K:950L+4; A:555L+2;
    D:1580L+4; E:2605L+7; F:6320L+18;
    G1:8135L+22; H:235L+1; I:16740L+46;
    a0:3800L+14; a1:24640L+68;
    d:13750L+40; c:13110L+40; m:2221L+11;
    V0:1900L+7; V1:12320L+34;
    Omega:15971L+51; Theta:30191L+92.

A naive degree calculation misses an important cancellation. Set eta_degree=20L+1. On the all-coordinates-equal-t specialization, R has leading coefficient 1, while deltaR has degree 215L-1 and leading coefficient 32z. Thus Rbar/R first differs by relative leading term 32z*t^(-eta_degree).

Relative companion defects for A,C,J,H have multiplier 1, for D multiplier 4, E multiplier 7, F multiplier 16, and G1 multiplier 21. The three factors in V1 consequently have total relative defect (2+8+22)=32 times that first R defect. The Pell subtractions of 1 have smaller degree. Since the leading coefficient of a1 is 2^46,

    degree(V1^2-a1)=24620L+67;
    leading coefficient(V1^2-a1)=2^57 z.

For a fully polynomial certificate, expand differences of products by telescoping, e.g. xbar^2-x^2=(xbar-x)(xbar+x), rather than dividing polynomials. The independent auditor supplies that cancellation-free identity for every companion, the three factors, and V1^2-a1.

Put E0=dn+c-Omega c, so Theta=E0-Omega V0V1. Then

    Theta^2-Omega^2(a0+V0^2a1)
      =E0^2-2 E0 Omega V0V1
       +Omega^2 V0^2(V1^2-a1)-Omega^2 a0.

The third term alone has highest degree 60362L+183 and leading coefficient 2^137 z. The cross term has lower degree 59272L+183. The final subtracted norm term 4Omega^4V0^2a0a1 has degree 96124L+300, below twice 60362L+183. Thus

    degree F9 =120724L+366;
    leading coefficient F9(t,...,t)=2^274 z^2>0.

This nonzero leader proves exactness after the authentic fixed constants are substituted. The proof does not assume a Diophantine solution and does not treat fixed constants as variables.

## 7. Circuit savings and verification boundaries

The sparse coefficient correction is evaluated by sorted-exponent Horner arithmetic. Powers share a radix-five ladder p_j=B^(5^j) and cached equal-digit runs. The baseline digit sum is

    B^(5^nu) h4(B^(5^nu), B^(5^nu-1), ..., B^(5^nu-5^nu)),

with ascending complete-homogeneous recurrence. Finally

    lambda=product_(j=0)^nu (1+p_j+p_j^2+p_j^3+p_j^4) * (1+q)*(1+q^2).

These are exact identities, with no divisions in the output circuit. They account for most of the operation-count improvement. Fixed exponentiation is fully expanded into binary multiplications, and squaring and scalar multiplication are charged. Shared reuse is free. The construction/materialization cost of fixed integer constants is not charged as variable arithmetic; all constants nevertheless have bounded definitions.

Independent diagnostics include exact rebuilding of all shifted and weighted coefficients, the strict index bound, all four compiler-byte hashes/bit lengths, literal 58,905-term index-baseline comparisons, 752 actual-instance named-node comparisons across four primes and four input tuples, 512 companion/root-bound assignments, and 576 constructed finalizer witnesses. The degree certificate also checks cancellation-free algebra independently. These are finite checks of the definitions, not an empirical proof of the unbounded semantic equivalence.
