# Independent audit of Sections 6–8

Audited against `canonical_sectors_proof.md` on 2026-10-02. Verdict: the complex-saddle argument, all-orders remainder, prefactor, parity, and additive first-pair error pass. No substantive gap was found. The sealed delivered files were not modified.

## 1. Circle phase and principal saddle

For fixed k, write zeta = zeta_k, phi = arg(zeta), kappa = (g_k^2 pi^2/(4 zeta))^(1/3), and h = n^(-1/6). The principal-root identities are compatible because |phi| < pi/2:

- delta_s = zeta kappa h^4, with arg(delta_s) = 2 phi/3
- g_k pi / sqrt(zeta kappa) = 2 kappa
- Re(kappa) > 0

The leading phase on the radius-|delta_s| circle has real part |kappa| h^(-2) f_phi(alpha). The stated derivative factorization is exact. Its cosine factor is positive and its sine factor changes sign only at alpha_s = 2 phi/3, so alpha_s is the unique global maximum. Near alpha_s, the real-part loss is bounded below by a positive constant times h^(-2)(alpha-alpha_s)^2. Away from any fixed neighborhood, compactness gives a loss of order h^(-2).

The leading complex phase in theta = alpha-alpha_s is kappa h^(-2)(exp(i theta)+2 exp(-i theta/2)); its quadratic term is -3 kappa h^(-2) theta^2/4. The real theta contour therefore has the required Gaussian damping, without a contour rotation. The local exponent's omitted terms are uniformly O(h^2) over the full angular interval, including the two bank limits.

The bank bound is valid since |zeta+x| increases for x >= 0 and B_cut is integrable. Moreover,

(n+1) log(|zeta+r_n|/|zeta|) = |kappa| cos(phi) h^(-2) + O(h^2),

so each bank is exponentially smaller than the saddle envelope. The clockwise circle parameterization has the sign in the proof note.

## 2. Uniform all-orders remainder

Here is a fully explicit version of the analytic estimate used in Section 7. Let

a(delta) = sqrt(delta/(exp(delta)-1)),

choosing a(0)=1, and let

b(delta) = -delta/2 - 3(atan(sqrt(exp(delta)-1))/sqrt(exp(delta)-1) - 1).

Both are analytic near zero. Then the local exponent can be written as its constant plus

2 kappa h^(-2) exp(-i h y/2) a(zeta kappa h^4 exp(i h y)) + b(zeta kappa h^4 exp(i h y)).

The negative powers from this expression and the logarithm cancel exactly in S. The remaining leading-phase expression is

kappa h^(-2)[exp(i h y)+2 exp(-i h y/2)-3+3 h^2 y^2/4],

which starts at order h y^3. The other nonconstant terms start at order h y, h^2, or higher. Consequently, for 0 <= t <= h and |y| <= h^(-eta), with any fixed 0 < eta < 1 and h sufficiently small,

|S(t,y)| <= C t (1+|y|^3).

For each fixed derivative order q, the h derivatives of S are bounded on the same range by a polynomial in |y|, uniformly in h. This follows from the convergent analytic local formula and |t y| <= h^(1-eta). Taylor's theorem and the finite derivative formulas for exp(S) therefore give, at every fixed truncation order J,

|exp(S(h,y)) - sum_(j=0)^J h^j [h^j] exp(S)|
 <= h^(J+1) P_J(|y|) exp(C h(1+|y|^3)).

Since h|y| <= h^(1-eta), the product with |exp(-3 kappa y^2/4)| is bounded by a fixed constant times

exp(-3 Re(kappa) y^2/8) P_J(|y|)

for all sufficiently small h. This is integrable independently of h. Thus the integrated Taylor remainder is O(h^(J+1)).

The exact formal symmetry S(-h,-y)=S(h,y) proves that its order-j coefficient, and the order-j coefficient of exp(S), have y-parity j. On a symmetric central interval, odd terms vanish exactly. Taking J=2K+1 therefore gives integrated error O(h^(2K+2)). Extending the finite polynomial-Gaussian terms to the real line has error smaller than any power of h. The complementary angular arcs have relative loss exp(-c h^(-2 eta)), up to harmless polynomial factors, from the phase maximum already proved.

The eta in Section 6's n-based angular window equals eta/6 when using Section 7's h-based window. This is a harmless reuse of notation, not a mathematical discrepancy.

## 3. Prefactor and first coefficients

After alpha=alpha_s+h y, the exact circle Jacobian and powers give

exp(zeta/2-3) zeta^(-n) exp(3 kappa h^(-2)) [kappa h^5/(2 pi)].

Multiplying by the complex Gaussian integral sqrt(4 pi/(3 kappa)) gives exactly

C_k n^(-5/6), where C_k=exp(zeta/2-3) sqrt(kappa/(3 pi)).

The square root is principal; the Gaussian integral is nonzero. In particular the factor exp(zeta/2)=2(-1)^k is retained, so the odd-sector sign is correct.

An independent expansion through h^4 gives

S_1 = i y - i kappa y^3/8,
S_2 = kappa^2(1-zeta)/2 + 3 kappa y^4/64,
S_3 = i kappa^2 y(1-zeta/4) + i kappa y^5/128,
S_4 = kappa(1+zeta/2) + kappa^2 y^2(zeta/16-1) - 11 kappa y^6/7680.

Gaussian moments independently recover

c_1 = kappa^2(1-zeta)/2 - 5/(36 kappa),
c_2 = kappa^4(1-zeta)^2/8 + kappa(53 zeta-17)/72 - 35/(2592 kappa^2).

These agree with the existing symbolic check. Numerical files were inspected as regression evidence, not used as proof.

## 4. Additive first-pair error

The previously audited global construction supplies exact, radius-independent H_k and conjugation H_(-k)=conj(H_k). Its fixed-radius bound makes the |k|>=2 tail O_R(R^(-n)) whenever |zeta_1|<R<|zeta_2|. Because the local saddle result is asserted only for fixed k, no uniform-in-k saddle estimate is needed to combine it with that global bound.

Apply the all-orders estimate to H_1, take twice the real part, and bound the complex remainder by its modulus. This gives precisely O_K(E_1(n)n^(-(K+1)/3)), plus the separate O_R(R^(-n)) tail. It remains valid at oscillatory near-cancellations because it is an absolute envelope bound. Subtracting exact H_0, rather than a finite dominant expansion, is essential and is done correctly in the statement.
