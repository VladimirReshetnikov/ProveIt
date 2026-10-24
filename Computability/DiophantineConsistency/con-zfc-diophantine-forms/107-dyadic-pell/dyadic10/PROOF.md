# Ten positive unknowns, dyadic square classes, three centers

Date: 23 October 2026. Prepared with AI assistance (ChatGPT).

## 0. Scope and inherited calibration

This is an ordinary mathematical reduction, formalizable in ZFC, relative to the explicit native compiler/calibration theorem of ProveIt package 61. It is not an end-to-end Lean/Rocq proof. The new result is a polynomial of exact degree **706**, evaluated by **133 binary operations**, in ten strictly positive integers. It uses the same four concrete fixed integer coefficients as the existing ten-positive degree-816 candidate. No claim of global minimality or a new universal-polynomial variable record is made.

The pinned source is ProveIt commit `ec80841c07e91be8956ce6ed4af9a9c0b782d3d9`. The immediate parent is

`Computability/DiophantineConsistency/candidates/ten-positive-scaled-norm/PROOF.md`.

Its source interface is package 61, `report/congruence_carriers.tex`, Theorem `thm:source`, together with its canonical promises and Lemmas `lem:rank`, `lem:index`, `lem:auxcomplete`, `lem:odd`. The parent's Sections 3--4 restate the relevant Pell facts and lemmas. We use those precise statements, including the main-index projection and the fixed-minus parity lemma. They are unaffected by the modifications below. This note explicitly checks the steps that need changes and records the remaining bridge to the source system.

The coefficient files in `coefficients/` are the entire compact44 tuple, copied without alteration. They are interpreted as little-endian nonnegative integers after gzip decompression. Their SHA-256 digests are in `build.py` and the emitted JSON. They bind

- beta = 2^590069 - 1;
- K0 = the native compiler constant;
- 0 < MC < beta;
- beta < MF < 2 beta, with MF **already shifted**.

No coefficient port is existentially quantified. The coefficient/calibration dependency is inherited, not re-proved here.

## 1. Exact polynomial

The unknowns, all strictly positive integers, are

    j, F, alpha, i, T, w, Y, n, eta, zeta.

Define integer-polynomial registers as follows; all displayed fractions later in the proof are explanatory identities, and no division occurs in the circuit:

    J = 2j+1,       q = beta J+1,        C = q-F-alpha,
    X = wq,        a = Y(X+1),          k = eta+zeta,       c = kY+eta,
    mu = q^2+1,    lambda = 2mu,
    A = lambda(a+2)+1,     H = 4A-5,     Delta = A^2-1,    a_minus = A-2,
    V0 = X lambda^2 Y^2,   Dtau = V0(V0+1)k^2+1,
    G = (q-1)(q-F)+alpha,
    R = G(q^2-1)+(MC+q MF)J,
    e = k-R-1,     Bt = (K0+w)C-F,
    I = i c^2,     Df = 1+Delta I^2,    Q = Delta^2 I^2,   delta = Q-1,
    Tprime = T+alpha,     b = c Tprime-R,
    V = Df b-c,     Dnum = Q V^2-1,     Dmain = Delta c^2+1,
    Cf = A I,      Ct = V0 k,
    L = (k+F+1)(Tprime+6),              W = 1+(q-1)L,
    P1 = q^3(q-1),                      M = P1 mu^2 H,
    Z = P1 mu^2 [H(n+V+2Cf+4Ct)+8(X+a_minus c)]
          +H[mu^2((q-1)Y-q^3 W Bt)-P1 e].

Put

    s = delta Z^2,
    aa = 16 delta M^2 Dtau,
    bb = 4 delta M^2 Df,
    cc = M^2 Dnum,
    dd = 64 delta (P1 mu^2)^2 Dmain.

For five formal arguments s,a,b,c,d define the fixed norm polynomial

    sigma1 = a+b+c,   sigma2 = ab+(a+b)c,   sigma3 = abc,
    U = s+d,         P = U-sigma1,
    E = P^2+4(sd-sigma2),
    Gnorm = E^2+16(sd P^2-4 sigma3 U),
    Onorm = E P-16 sigma3,
    F16(s;a,b,c,d) = Gnorm^2-64sd Onorm^2.

Our equation is

    N := F16(s;aa,bb,cc,dd) = 0.

It is one polynomial equation with fixed integer coefficients. `circuit.py` lists all 133 binary operations. The labels `Ap`, `Hp`, `Dp` in the executable stand for A,H,Delta. The executable distributes `W Bt/(q-1)=L Bt+Bt/(q-1)`: it subtracts L Bt directly from the centered carrier and uses Bt alone in the remaining fractional term. This exact polynomial identity saves one binary operation; W is an abbreviation in the proof, not a materialized circuit register.

The standard product identity, proved by pairing conjugates in the parent's Section 2, is

    F16(x^2;ra^2,rb^2,rc^2,rd^2)
       = product_(eps in {+-1}^4) (x-eps1 ra-eps2 rb-eps3 rc-eps4 rd).

For the positive real roots

    tau = sqrt(Dtau),    f = sqrt(Df),
    y = sqrt(Dnum/delta),    Dm = sqrt(Dmain),    d = Dm/H,

this gives

    N = delta^8 M^16 product_eps [Z/M -4eps1 tau-2eps2 f-eps3 y-8eps4 d].  (1)

The carrier identity is

    Z/M = n+V+2Cf+4Ct+8(X+a_minus c)/H
                      +Y/q^3-W Bt/(q-1)-e/mu^2.                         (2)

## 2. Proof of the equivalence

### 2.1 All-input facts and the dyadic lemma

For every positive input, beta odd and J odd give even q >=16. Consequently mu is odd and lambda is even, so A is odd, Delta is even, V0 is even, and H is odd. We have c>=3, I>=c^2, A>Y(X+1), and Delta>mu^2. In particular Q>1 and delta>0.

If b=0 then V=-c, so |V|>=3. If b is a nonzero integer, then

    |V| >= Df-c > 1,

because Df>=1+Delta c^4. Thus Dnum>0 for every positive input, even before an equation or a sign for V is assumed. The four radicands are positive rational numbers, and

    v_2(Dtau) = v_2(Df) = v_2(Dnum/delta) = v_2(Dmain/H^2) = 0.          (3)

Indeed every numerator and denominator displayed in (3) is odd.

**Dyadic square-class separation lemma.** Let r_0,...,r_(m-1)>0 have rational squares of 2-adic valuation zero. If a signed sum of `2^h r_h`, with distinct integer exponents h, is rational, then every r_h is rational.

Proof. In the multiquadratic Galois extension generated by the roots, project the rational relation onto any nontrivial sign character. The projection says that the signed sum of the weighted roots in one common square class is zero. Divide by one of the roots in that class. Every remaining rational ratio has 2-adic valuation zero, because its square does. Hence the terms in this rational relation have distinct 2-adic valuations h. The unique term of least valuation cannot be cancelled: clearing their odd denominators reduces this to the parity of an odd integer plus even integers. This is a contradiction. No nontrivial square class occurs, so every root is rational. QED.

The weights in (1), ordered as `(y,f,tau,d)`, are `(1,2,4,8)`. Thus equation N=0 forces all four roots to be rational, without any Archimedean comparison between them. The rational tau,f,Dm have integer squares and therefore are integers. The adjacent-coefficient descent lemma, restated and proved in the parent's L2, applies to

    Q V^2-(Q-1)y^2=1

and implies y is an integer. If V is negative at this stage, apply the lemma to |V|. This is the only integrality descent used here.

### 2.2 Coprime index congruence and Pell classification

The original modulus mu^2 is retained, even though lambda=2mu is the Pell scaling. Since q is even,

    gcd(mu^2,q^3(q-1))=1,
    H=4lambda(a+2)-1=-1 modulo mu.

Consequently mu^2 is coprime to q^3(q-1)H. Substituting the rational signed-root equation in (2) and using the integrality of tau,f,y gives

    8(X+a_minus c-eps4 Dm)/H +Y/q^3-W Bt/(q-1)-e/mu^2 is an integer.

The coprime partial-fraction lemma therefore gives mu^2|e. Write rho=e/mu^2, and put

    g=(eps4 Dm-X-a_minus c)/H,  s0=Y/q^3>0,  t=Bt/(q-1).

Then

    n =4(eps1 tau-Ct)+2(eps2 f-Cf)+(eps3 y-V)+8g-s0+W t+rho.          (4)

Standard Pell classification gives

    tau=chi_P(n0),  k=2psi_P(n0),  P=2V0+1,
    Dm=chi_A(p),    c=psi_A(p),
    f=chi_A(m),     I=psi_A(m),

with positive indices. The fundamental solution for `x^2-V0(V0+1)k^2=1` is `(2V0+1,2)`; k=1 would require a square strictly between consecutive squares.

The case n0=1 would force k=2, eta=zeta=1, c=2Y+1, whereas no main Pell ordinate equals that value: psi_A(1)=1 and psi_A(p)>=2A>2Y+1 for p>=2. Hence n0>=2 and

    c>k>=4P>8X lambda^2Y^2>8q^5.                                    (5)

As in the parent, the mask inequalities imply the one-sided bound

    R<q^4+(alpha+2)q^2.                                              (6)

Thus c(T+alpha)>R, b>=1, and V=Df b-c>1. In particular y>V.

### 2.3 A quadratic transport majorant

For all positive inputs one also has the two-sided bound

    |R|<q^4+Fq^3+(alpha+2)q^2.

Because q>=16 and mu^2>q^4,

    |R|/mu^2 < F+alpha+1,
    |rho| <=(k+1+|R|)/mu^2 < k+F+alpha+1.                            (7)

The relevant one-sided root estimates are

    tau-Ct<k,               f-Cf<0,              8g<k.                 (8)

For the last estimate, `Dm<Ac` and eps4<=1 yield

    g < 2c/H < 4kY/H,

and H>32Y. The inequality f<Cf follows from `Df=A^2 I^2-I^2+1<A^2 I^2`, since I>1.

Let u=y-V. Since V>1 and y>V,

    u=(V^2-1)/[(Q-1)(y+V)] < V/[2(Q-1)]
       < Df b/[2(Q-1)] < b/Delta.

The last inequality follows from `Delta Df=Q+Delta<2Q-2`, valid for Delta>=3 and I>=1. Furthermore Delta>mu^2 and c<2kY<k Delta, so

    u < k Tprime+F+alpha+1.                                         (9)

Suppose Bt<0. Then Bt is an integer at most -1, hence

    Wt <=-W/(q-1)<-L.

Using (7)--(9) in (4), including `eps3 y-V<=y-V`, gives

    n<kTprime+6k+2F+2alpha+2-L<0.

The final inequality follows by expanding

    L-(kTprime+6k+2F+2alpha+2)
      =(F+1)Tprime+4F+4-2alpha
      =(F+1)T+(F-1)alpha+4F+4>0.

This contradicts n>=1. Therefore Bt>=0. As in the source proof, `(K0+w)C>=F>0` gives C>=1 and the outer bounds

    3q<R<q^4-2.                                                      (10)

### 2.4 Recovering the indices, the exponent, and the source solution

All subsequent Pell arguments of the parent's Sections 6.9--6.18 apply, with arbitrary scaling lambda=2mu and the same index modulus mu^2. Here are the precise reasons.

First, `k=2n0 modulo 4V0` and mu^2|4V0. Together with mu^2|e and (10), this gives `2n0>=R+1`. Equations (5) and (10) imply c>2R, while c=psi_A(p)>2p. The rank lemma requires only c^2|I, which holds for I=i c^2; it gives c|m and m>2p. The auxiliary register has

    V=-c modulo f,   V=-R modulo c,
    S^2=Delta(f^2-1)=Q,   S=Delta I,   c|S.

The source index lemma gives p=R. Since P>A, monotonicity of Pell ordinates gives n0<R. The congruence `2n0=R+1 modulo mu^2` and (10) then force `2n0=R+1`. The fixed-minus parity lemma gives `R=3 modulo 4`.

Put r=(R-1)/2. The parent's ratio bound L4(a) is stated for every positive integer scaling lambda, so it applies unchanged to lambda=2mu. It gives

    Y>X^r/3,   a>X^(r+1)/3,   r>=24.                                 (11)

Before the exponent projection we know

    H | 8q^3(q-1)(X+a_minus c-eps4 Dm).

Since H is odd, the factor 8 cancels. The source projection identities

    Dm-a_minus c=2^R modulo H,
    Dm+a_minus c=2^(-R) modulo H

and the parent's Archimedean estimate

    q^4 2^(R+1)X < X^(r+1) < 3a < H

then give eps4=+1 and X=2^R exactly as in its Section 6.16. The factor 8 creates no residual modulus requirement. Now g is an integer, so the remaining partial fractions give

    q^3|Y,     q-1|Bt.

The ratio estimate and the half-binomial lemma give the same unique integer

    Y = (1/2) sum_(h=0..r) binom(2r,r+h) X^h.

To reach the original unscaled source theorem, keep J,F,alpha,w,Y and set `s=Y/q^3`, `z=Bt/(q-1)+1`. Reconstruct fresh unscaled Pell witnesses with main parameter a+2 and first parameter 2XY^2+1, exactly as in the parent's Section 6.18. That construction depends only on the now-proved statements `X=2^R`, `R=3 mod4`, the half-binomial value of Y, and the transport/divisibility conditions. It supplies all fifteen positive source witnesses. Package 61's `thm:source` therefore gives a finite syntactic refutation of ZFC.

This establishes soundness, without using root-size separation and without the discarded factor mu in I.

### 2.5 Completeness and positivity of the new sum coordinate

Assume ZFC has a finite syntactic refutation. Use the canonical positive source solution furnished by package 61. It has

    q=B^N with odd N>1,   R=3 mod4,   X=2^R,
    Y equal to the half-binomial above,   C>0.

The parent's Section 7 constructs scaled main/first Pell values for every positive integer lambda by the same ratio estimate. Use lambda=2mu. Thus c=psi_A(R), k=2psi_P((R+1)/2), and eta=c-kY, zeta=k-eta are positive. The quantities rho=(k-R-1)/mu^2, g=(Dm-X-a_minus c)/H and t=Bt/(q-1) are integers with rho,g>=1 and t>=0.

For the strong pair take the smaller index

    m=Rc,       I=psi_A(m),       f=chi_A(m).

Pell composition gives `psi_A(Rc)=c psi_Dm(c)`. The standard congruence

    psi_Dm(c)=c Dm^(c-1) modulo Dm^2-1

and c^2|Dm^2-1 imply c|psi_Dm(c), hence c^2|I. Therefore i=I/c^2 is a positive integer. No divisibility by mu is required or claimed.

Apply the same auxiliary completeness lemma. With S=Delta I and Q=S^2, its explicit solution has

    V*=chi_S(R)/S = Q_v(S^2),     v=(R-1)/2>=2,
    y=psi_S(R),
    T*=(V*+c+R f^2)/(c f^2),
    Q(V*)^2-(Q-1)y^2=1.

The source lemma ensures T* is a positive integer. Its usual Pell bound gives

    V* >=(4Q-3)^v >=(3Q)^v >=9Q^2.

Since c<S and f^2=Df<Q, `T*>V*/S^3>=9S>alpha`. Indeed the canonical C>0 implies alpha<q<S. Set T=T*-alpha>=1, so Tprime=T* and V=V*.

The additional centers make the strong-root contribution negative, so positivity of n deserves an explicit proof. Put u=y-V. Since V>=2 and y<2V,

    u=(V^2-1)/[(Q-1)(y+V)] >V/(4Q) >=9S^2/4>3S+1.

Also I<S and Y<c<I. Therefore

    u>2I+Y+1.                                                       (12)

Finally define the integer

    n=Wt+rho+8g+4(tau-Ct)+2(f-Cf)+u-Y/q^3.

All terms except the last strong-center and quotient terms are nonnegative, with tau>Ct. Since f>(A-1)I, one has f-Cf>-I. By (12), n>0, hence n>=1. Substituting in (2) yields

    Z/M=4tau+2f+y+8d.

One factor of (1) vanishes, proving completeness.

Thus, inside ZFC by the same arithmetized source calibration,

    N has a positive integer zero iff ZFC has a finite syntactic refutation.

Negating both sides gives the required equivalence with Con(ZFC).

## 3. Exact total degree 706

The 133-row circuit has the conservative syntactic degree 832. The exact degree is lower, because three leading radical terms are already present in the carrier.

We give a symbolic proof, not an inference from random evaluations. Replace every unknown x by t*x and work over the rational function field K in the ten direction variables and the fixed coefficient field. For a rational function, its degree is its degree in t at infinity. The square roots below admit formal Laurent expansions in K((t^-1)): each radicand is the square of the indicated center times 1 plus a strictly lower-degree rational function. Choose the branches with leading terms Ct,Cf,V and the usual main leading term. The product over all signs does not depend on branch choices.

The relevant degrees are

| Register/root | Degree in t |
|---|---:|
| mu, lambda | 2 |
| A,H,Delta | 5,5,10 |
| I,Q,delta | 5,30,30 |
| Df,V | 20,24 |
| M | 13 |
| Cf,Ct | 10,9 |
| tau-Ct | 1 |
| f-Cf | at most 0 |
| y-V | -6 |
| d | 2 |
| L,W,Bt | 2,3,2 |
| Z/M-V-2Cf-4Ct | 4 |

For example, `f^2-Cf^2=1-I^2` has degree 10, and division by the degree-10 leading sum f+Cf shows degree at most zero. The auxiliary error follows from `(y-V)(y+V)=(V^2-1)/(Q-1)`, giving degree 48-30-24=-6. The degree-4 leading term of the last row is `-L_2 Bt_2`, from `-W Bt/(q-1)`.

The sixteen factors in (1) divide into four exact leading-degree classes:

| Signs | Number of factors | Leading term | Degree each |
|---|---:|---|---:|
| eps3=-1 | 8 | 2V | 24 |
| eps3=+1, eps2=-1 | 4 | 4Cf | 10 |
| eps3=eps2=+1, eps1=-1 | 2 | 8Ct | 9 |
| eps3=eps2=eps1=+1 | 2 | -L_2 Bt_2 | 4 |

Therefore the product has exact degree

    8*24+4*10+2*9+2*4=258,

and the nonzero prefactor delta^8 M^16 has degree `8*30+16*13=448`. Thus N has exact degree **706**.

For an explicit leading form, let q0=2 beta j, k0=eta+zeta and put

    lambda0=2q0^2,   A0=lambda0 wq0Y,   Delta0=A0^2,
    c0=k0Y,         I0=i c0^2,
    Q0=Delta0^2 I0^2,
    Vtop=-(Delta0 I0^2) q0^3(q0-F),
    Cf0=A0 I0,      Ct0=wq0 lambda0^2 Y^2 k0,
    M0=4q0^8 A0,
    L0=(k0+F)(T+alpha),     Bt0=w(q0-F-alpha).

The degree-706 homogeneous component is

    2^22 Q0^8 M0^16 Vtop^8 Cf0^4 Ct0^2 (L0 Bt0)^2.                  (13)

Every factor is a nonzero polynomial, so it cannot vanish identically. On the diagonal, with all ten variables equal to t and q0=2beta now a fixed integer, the coefficient of t^706 simplifies to

    9 * 2^202 * q0^366 * (q0-1)^8 * (q0-2)^2 > 0.

This also provides an explicit lower-degree witness for the actual fixed ports. Only beta occurs in this leading coefficient; the other three ports affect lower terms.

## 4. Verification, counts, and limitations

`build.py --check` authenticates every compressed/raw coefficient payload, verifies the defining coefficient bounds, checks topology and liveness, and reproduces the circuit JSON byte for byte. The circuit has exactly 79 multiplications, 33 additions and 21 subtractions, including operations by small numerals. No gate is dead and every unknown and coefficient is used.

`audit.py` independently evaluates the displayed polynomial formulas at modular points, computes full degree-bounded univariate restrictions modulo two primes, checks (13), and verifies the elementary parity/majorant premises and canonical-gap inequalities on finite exact cases. These checks support but do not replace the universal proof above. They do not solve the target equation or prove Con(ZFC).

The final equation still depends on the established K215/native compiler calibration. The dyadic separation method is a general p-adic principle; no broad novelty claim is made for it. The specific contribution here is combining the even scaling, dyadic-weighted roots, deletion of the strong mu multiplier, and the quadratic transport majorant in this ten-positive-variable kernel. Relative to the pinned immediate parent, the exact degree falls from 816 to 706 (110 degrees, about 13.48%), while the operation count increases from 124 to 133. These are different simplicity measures; neither circuit uniformly dominates the other.
