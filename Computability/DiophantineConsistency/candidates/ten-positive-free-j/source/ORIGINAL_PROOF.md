# Ten positive unknowns at degree 816: complete proof

Status: complete ordinary mathematical proof relative to package 61's
inherited compiler/calibration interface. The literal circuit and the
finite audits are `circuit.py`, `build.py` and `verify.py`. This is not an
end-to-end formal certificate.

## 0. Result and dependencies

The fixed integers are the whole compact44 tuple beta, K0, MC, MF bound in
`build.py`. Here B = beta+1 = 2^590069, and MF is the already shifted high
mask; it is not shifted again. The ten unknowns are strictly positive
integers:

    j, F, alpha, i, T, w, Y, n, eta, zeta.

**Theorem.** The polynomial N of Section 1 has a zero in strictly positive
integers if and only if there is a finite syntactic refutation of ZFC.
Consequently ZFC proves: Con(ZFC) holds iff N has no positive zero.
N has 124 binary operations and exact total degree 816.

The proof uses, as stated and without change:

* package 61, `report/congruence_carriers.tex`: Theorem `thm:source`
  (its normalized positive source system, soundness, and the canonical
  promises of the section "Canonical promises used in completeness"),
  and Lemmas `lem:rank`, `lem:index`, `lem:auxcomplete`, `lem:odd`;
* package 69, `positive/PROOF.md` Section 2 (adjacent-coefficient descent),
  reproved below as Lemma L2;
* the fixed-minus parity argument of
  `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md`,
  reproved below as Lemma L7;
* standard Pell-sequence facts, listed in Section 3.

Completeness uses, besides the statement of `lem:auxcomplete`, the
explicit witnesses from its proof: V* = chi_S(R)/S = Q_v(S^2) and
T* = (V* + c + R f^2)/(c f^2) (Section 4).

Package 61's `thm:source` composes the native-window/Pell compiler, the
compact-coefficient adapter and the blank-K215 halting/refutation
calibration. That composition is the only inherited theorem. Unlike
package 70, no weighted transport theorem is used.

The archive `con-zfc-radical-residue-2026-10-23.zip` (arrival
`440dd03ab8`) already contains a ten-positive equation of the same overall
shape: 131 operations, degree 1152. It shares with this note:

* four roots in one sixteen-fold norm;
* the same superincreasing orders, extraction by square-class characters,
  and adjacent-coefficient descent;
* the inverse projection that fixes the main-root sign.

Its literal circuit also uses the 28-operation compact norm schedule
of Section 1.

This note's first version was being built in scratch files when that
archive arrived. Its author learned of the archive only after writing that
version. The present version adopts that proof's Archimedean separation
(6.16). Two further devices come from reviewed eleven-positive work:

* centering the carrier at the auxiliary register, with the inner
  cancellation delta[z(z+2MV) - A - Bf] - M^2(V^2-1), from the joint-guards
  endpoint reviewed in `PROPOSAL_REVIEW_WAVE11_POSITIVE.md`;
* the offset auxiliary coordinate T + F + alpha, from the polynomial-shears
  arrival (also `440dd03ab8`), reviewed in
  `PROPOSAL_REVIEW_POLYNOMIAL_SHEARS_POSITIVE.md`.

New here:

* mu-scaling of both Pell parameters, so that the first-index modulus is
  mu^2 while Y stays a free unknown;
* the offset alpha alone, which suffices by the mask bound (5.2.1);
* the sixteen-fold pairing lemma and weight argument that prove the exact
  degree (Lemma 8.1).

Section 9 gives the details.

## 1. The polynomial

Every quantity below is an integer polynomial in the unknowns and the fixed
ports; no division occurs.

    J = 2j+1,            q = beta J + 1,         C = q - F - alpha,
    X = w q,             a = XY + Y,             k = eta + zeta,      c = kY + eta,
    mu = q^2 + 1,
    A' = mu(a+2) + 1,    H' = 4A' - 5,           Delta' = A'^2 - 1,   a' = A' - 2,
    V0 = X mu^2 Y^2,     Dtau = V0(V0+1)k^2 + 1,
    G = (q-1)(q-F) + alpha,                      R = G(q^2-1) + (MC + q MF)J,
    e = k - R - 1,       Bt = (K0 + w)C - F,
    I = i mu c^2,        Df = 1 + Delta' I^2,    Q = Delta'^2 I^2,    delta = Q - 1,
    T' = T + alpha,      b' = cT' - R,           V = Df b' - c,
    Dnum = Q V^2 - 1,    Dmain = Delta' c^2 + 1,
    L = 4(A'-1)I + b' + cT',                     W = 1 + (q-1)L,
    P1 = q^3(q-1),       Mtot = P1 mu^2 H',
    Znum = P1 mu^2 (H'(n+V) + X + a'c) + H'[mu^2((q-1)Y - q^3 W Bt) - P1 e],

and, with

    fs = delta Znum^2,   fa = delta Mtot^2 Dtau,  fb = delta Mtot^2 Df,
    fc = Mtot^2 Dnum,    fd = delta (P1 mu^2)^2 Dmain,

the polynomial is

    N = F16(fs; fa, fb, fc, fd).

Here, for indeterminates s,a,b,c,d,

    sig1 = a+b+c,   sig2 = ab + (a+b)c,   sig3 = abc,
    U = s + d,      Po = U - sig1,        Pe = Po^2 + 4(sd - sig2),
    Ge = Pe^2 + 16(sd Po^2 - 4 sig3 U),   Go = Pe Po - 16 sig3,
    F16(s; a,b,c,d) = Ge^2 - 64 sd Go^2.

Inside F16 the letters a,b,c,d are formal; they are unrelated to the
registers a, c. Dividing out the definitions gives

    Znum/Mtot = n + V + (X + a'c)/H' + Y/q^3 - W Bt/(q-1) - e/mu^2.     (1.1)

The circuit materializes A'-1 = mu(a+2), and computes H' = 4(A'-1) - 1,
Delta' = (A'-1)(A'+1) and Dtau = V0k (V0k + k) + 1. It has 124 binary
operations (74 multiplications, 30 additions, 20 subtractions), every row
live and every input used. Audit `contracts` checks it against an
independent evaluation of these formulas.

## 2. The sixteen-fold norm

**Lemma 2.1.** In Z[x, ra, rb, rc, rd], with a=ra^2, b=rb^2, c=rc^2, d=rd^2,

    F16(x^2; a,b,c,d) = prod over eps in {1,-1}^4 of
                        (x - eps1 ra - eps2 rb - eps3 rc - eps4 rd).

F16 is homogeneous of degree 8 in (s,a,b,c,d), and its coefficient of s^8
is 1.

*Proof.* Fix eps4 and put y = x - eps4 rd. The product over eps1,eps2,eps3
of (y - eps1 ra - eps2 rb - eps3 rc) is the octic norm of package 70,
Section 5:

    [(w - sig1)^2 - 4 sig2]^2 - 64 sig3 w,     w = y^2.

Here w = U - eps4 r with U = x^2 + d and r = 2x rd, so r^2 = 4sd. Expanding,

    (w - sig1)^2 - 4 sig2 = Pe - 2 eps4 r Po,

and then [Pe - 2 eps4 r Po]^2 - 64 sig3 w = Ge - 4 eps4 r Go. The product of
the two values eps4 = 1 and eps4 = -1 is Ge^2 - 16 r^2 Go^2, which equals
Ge^2 - 64 sd Go^2. Homogeneity and the s^8 coefficient follow from the
product form. Audit `norm` also verifies the identity by full symbolic
expansion. QED

All radicands below are positive for every positive input (Section 5).
Define the positive reals

    tau = sqrt(Dtau),  f = sqrt(Df),  y = sqrt(Dnum/delta),  Dm = sqrt(Dmain),  d = Dm/H'.

**Corollary 2.2.** For every positive input,

    N = delta^8 Mtot^16 prod over eps of
        (Znum/Mtot - eps1 tau - eps2 f - eps3 y - eps4 d).

*Proof.* Apply Lemma 2.1 with x = sqrt(delta) Znum,
ra = sqrt(delta) Mtot tau, rb = sqrt(delta) Mtot f,
rc = Mtot sqrt(Dnum) = sqrt(delta) Mtot y and
rd = sqrt(delta) P1 mu^2 Dm = sqrt(delta) Mtot d. Their squares are
fs, fa, fb, fc, fd. Each factor equals sqrt(delta) Mtot times the
displayed factor. QED

## 3. Pell notation and standard facts

For an integer A >= 2 and n in Z define chi_A(n), psi_A(n) by

    chi_A(n) + psi_A(n) sqrt(A^2-1) = (A + sqrt(A^2-1))^n.

Both satisfy z(n+2) = 2A z(n+1) - z(n); psi_A is odd in n and chi_A even.

* (P1) The positive integer solutions of x^2 - (A^2-1) y^2 = 1 are exactly
  (chi_A(n), psi_A(n)), n >= 1.
* (P2) gcd(psi_A(r), psi_A(s)) = psi_A(gcd(r,s)).
* (P3) psi_A(uv) = psi_A(u) psi_D(v) with D = chi_A(u). Also
  psi_D(v) = v D^(v-1) modulo D^2 - 1.
* (P4) (2A-1)^(n-1) <= psi_A(n) <= (2A)^(n-1) for n >= 1. Hence
  psi_A(n) >= n, and psi_A is strictly increasing on n >= 0. For fixed
  n >= 0, psi_A(n) is nondecreasing in A.
* (P5) psi_A(n) = n modulo A - 1.
* (P6) chi_A(n) - A psi_A(n) = -psi_A(n-1).
* (P7) chi_A(2j) = 1 + 2(A^2-1) psi_A(j)^2. If F = chi_A(m), then
  chi_A(z+2m) = -chi_A(z) and psi_A(z+2m) = -psi_A(z) modulo F.
* (P8) chi_Z(2h+1) = Z Q_h(Z^2) for integer polynomials Q_h with
  Q_h(0) = (-1)^h (2h+1) and Q_h(1-A^2) = (-1)^h psi_A(2h+1); this is
  package 61's `lem:odd`. Also chi_Z(2h) = (-1)^h modulo Z, from the
  recurrence, as used in 61's proof of `lem:index`. Finally,
  Q_h(x) >= (4x-3)^h for real x >= 1.

(P1)-(P3), (P6) and (P7) follow from the closed form. For (P3), note
D + psi_A(u) sqrt(A^2-1) = D + sqrt(D^2-1). Then expand
psi_D(v) = sum_t binom(v,2t+1) D^(v-2t-1)(D^2-1)^t. (P4): psi(n+1) lies
between (2A-1)psi(n) and 2A psi(n), and the binomial expansion has
nonnegative coefficients. (P5): modulo A-1 the recurrence is
z(n+2) = 2z(n+1) - z(n). For the bound in (P8), use
Q_(h+1) = (4x-2)Q_h - Q_(h-1) >= (4x-3)Q_h, by induction.

## 4. Lemmas

**L1 (rational signed sums).** Let r1,...,rm be positive reals with squares
in Q. If some signed sum of them is rational and no nonempty signed subsum
vanishes, then every ri is rational.

*Proof.* K = Q(r1,...,rm) is Galois over Q, and its group G sends each ri to
+ri or -ri. So chi_i(g) = g(ri)/ri defines a character chi_i: G -> {1,-1}.
Then chi_i = chi_j iff ri rj is rational, and chi_i is trivial iff ri is
rational. If some chi_k is nontrivial, apply
pi = |G|^-1 sum over g of chi_k(g) g to the relation sum eps_i r_i = x in Q.
We get pi(x) = 0, while pi(ri) = ri if chi_i = chi_k and 0 otherwise. So
the signed subsum over {i : chi_i = chi_k} vanishes, and it contains k.
This is a contradiction. QED

**L2 (adjacent-coefficient descent; package 69).** If Q > 1 and V are
integers, y is rational and Q V^2 - (Q-1) y^2 = 1, then y is an integer.

*Proof.* Take V, y > 0; V = 0 or y = 0 is impossible. Write y = u/m in
lowest terms. Then m^2 | Q-1. If V = 1 then y = 1. If V > 1, put
V' = (2Q-1)V - 2(Q-1)y and y' = (2Q-1)y - 2QV. V' is an integer, and since
(2Q-1)^2 - 4Q(Q-1) = 1, also Q V'^2 - (Q-1) y'^2 = 1. Next,
(Q-1)(y^2 - V^2) = V^2 - 1 > 0 gives y > V, and
(QV)^2 - ((Q-1)y)^2 = QV^2 + Q - 1 > 0 gives QV > (Q-1)y. Hence
-V < V' < V and V' != 0. Since 2Q-1 = 1 modulo m, y' has reduced
denominator m. Strong induction on V reaches V = 1, so m = 1. QED

**L3 (partial fractions).** If m1,...,m4 are pairwise coprime positive
integers and u1/m1 + ... + u4/m4 is an integer, then mi | ui for every i.
More generally, if m4 is coprime to m1 m2 m3, then m4 | u4.
*Proof.* Multiply by the product of the other moduli. QED

**L4 (ratio bounds).** Let X, Y, r >= 1, a = Y(X+1) and
xi = (X+1)^(2r)/X^r.

(a) For every integer lam >= 1 put A' = lam(a+2)+1 and P' = 2X lam^2 Y^2 + 1.
Then

    xi < psi_A'(2r+1)/psi_P'(r+1) < xi (1 + 3/a)^(2r).

(b) Put A = a+2 and P0 = 2XY^2 + 1. Then

    xi < psi_A(2r+1)/psi_P0(r+1) < xi (1 + 2/a)^(2r).

*Proof.* By (P4), for any A, P >= 2,

    ((2A-1)^2/(2P))^r <= psi_A(2r+1)/psi_P(r+1) <= ((2A)^2/(2P-1))^r.

Use a^2 = Y^2(X+1)^2. For the lower bound in (a),

    (2A'-1)^2 X - (X+1)^2 (2P') > 4 lam^2 X [(a+2)^2 - a^2] - 2(X+1)^2
                                >= 16 lam^2 X (a+1) - 2(X+1)^2 > 0.

For the upper bound, lam(a+2)+1 <= lam(a+3) gives

    (2A')^2/(2P'-1) < 4 lam^2 (a+3)^2/(4X lam^2 Y^2) = ((X+1)^2/X)(1+3/a)^2.

In (b), (2a+3)^2 X - (X+1)^2 (4XY^2+2) = X(12a+9) - 2(X+1)^2 > 0, and

    4(a+2)^2/(4XY^2+1) < ((X+1)^2/X)(1+2/a)^2.

QED

**L5 (projections).** Let A >= 2 and H = 4A - 5. Then H is odd, and for every
j >= 0

    chi_A(j) - (A-2) psi_A(j) = 2^j,
    chi_A(j) + (A-2) psi_A(j) = 2^(-j)          modulo H.

*Proof.* Modulo H we have 4A = 5. The sequences 2^j and 2^(-j) satisfy
z(j+2) = 2A z(j+1) - z(j), since 4A - 1 = 4 and 4(A-1) = 1. The initial
values match: 1 and A-(A-2) = 2 for the first, 1 and 2A-2 = 1/2 for the
second. QED

With A = a+2, H = 4a+3, this is package 61's exponent projection.

**L6 (half-binomial).** Let r >= 1 and X = 2^(2r+1). Then

    xi = M + theta,   M = sum_{j=0..r} binom(2r,r+j) X^j,   theta = sum_{j=1..r} binom(2r,r-j) X^(-j),

with M even and 0 < theta < 1/4.

*Proof.* binom(2r,r) and X are even. Also
theta < X^(-1) sum_{j>=1} binom(2r,r-j) < 2^(2r-1)/X = 1/4. QED

**L7 (fixed-minus parity).** Let A >= 2, Delta = A^2-1, and let p >= 3 be odd
with c = psi_A(p) > 2p. Let f = chi_A(m) > 2c, c | m and m >= 2p. Let S > 1
with c | S and S^2 = Delta(f^2-1). Suppose positive integers V, y satisfy
S^2V^2 - (S^2-1)y^2 = 1, V = -p modulo c and V = -c modulo f. Then
p = 3 modulo 4.

*Proof.* By (P1), SV = chi_S(nu) and y = psi_S(nu) with nu >= 1. By (P8),
chi_S(even) = +-1 modulo S, while S | SV, so nu = 2h+1 is odd. Then
V = Q_h(S^2). Since S^2 = 0 modulo c and S^2 = 1-A^2 modulo f,

    (-1)^h nu = -p (mod c),       (-1)^h psi_A(nu) = -c (mod f).       (4.1)

Squaring the second and using (P7) gives chi_A(2nu) = chi_A(2p) modulo f.
The plus-sign step-down below, with k = 2p <= m, gives 2nu = +-2p modulo
4m. So nu = eps p + 2m phi with eps in {1,-1} and phi in Z. By (P7),
psi_A(nu) = (-1)^phi eps c modulo f, and c | m gives nu = eps p modulo c.
With p = 2r+1, h = r + m phi if eps = 1, and h = -r-1+m phi if eps = -1.
Either way (-1)^h eps = (-1)^(r + m phi). Substituting into (4.1),

    (-1)^(r+m phi) p = -p (mod c),     (-1)^(r+(m+1)phi) c = -c (mod f).

Since 0 < 2p < c and 0 < 2c < f, both signs are -1. Hence phi is even, and
then r is odd. QED

*Plus-sign step-down.* Let F = chi_A(m), 0 < k <= m, and let n be an integer
with chi_A(n) = chi_A(k) modulo F. Then n = +-k modulo 4m. By (P7),
chi_A(n) is congruent to +-chi_A(l) for some 0 <= l <= m, and the sign is +
exactly when n = +-l modulo 4m.

* If k < m, then chi_A(k) lies in (0, F).
  - l = m is impossible, since then chi_A(l) = F is 0 modulo F.
  - If l < m, then chi_A(l) also lies in (0, F), and
    chi_A(l) + chi_A(k) <= 2 chi_A(m-1) < F. So the - sign is impossible,
    and the + sign forces l = k.
* If k = m, the residue is 0, which forces l = m.

This is Section 2 of the parity note.

The following statements of package 61 are used verbatim (A >= 2,
Delta = A^2-1):

* `lem:rank`: if c = psi_A(p) > 2, f, I > 0, f^2 - Delta I^2 = 1 and
  c^2 | I, then f = chi_A(m), I = psi_A(m) with pc | m, c | m, m > 2p.
* `lem:index`: if p, m, R, c, f, S > 0, c = psi_A(p), f = chi_A(m),
  c | m, m > 2p, S >= 2, c | S, S^2 = Delta(f^2-1), 0 < p, R < c/2, and
  integers V, y satisfy S^2V^2 - (S^2-1)y^2 = 1, V = -c (mod f) and
  V = -R (mod c), then p = R.
* `lem:auxcomplete`: if R >= 3, R = 3 (mod 4), c = psi_A(R),
  f^2 - Delta I^2 = 1, f, I > 0 and c | I, then with Q = (Delta I)^2 there
  are positive integers T*, u with V* = f^2(cT* - R) - c and
  Q V*^2 - (Q-1)(V*+u)^2 = 1. Its proof gives V* = chi_S(R)/S = Q_v(S^2),
  where S = Delta I and R = 2v+1.

## 5. Estimates valid for every positive input

Fix any strictly positive input; no equation is assumed.

**5.1 Moduli.** J = 2j+1 >= 3 is odd and beta is odd, so q = beta J + 1 is
even and q >= 3 beta + 1 >= 16. Then mu^2 is coprime to q^3 and to q-1:
gcd(q, q^2+1) = 1, and gcd(q-1, q^2+1) = gcd(q-1, 2) = 1 because q-1 is
odd. Also mu | A'-1, so H' = 4(A'-1) - 1 = -1 modulo every prime of mu.
Hence mu^2 is coprime to q^3 (q-1) H'. Further, q^3 and q-1 are coprime,
and W = 1 modulo q-1. No coprimality of H' with q or q-1 is claimed.

**5.2 Masks.** `build.py` verifies 0 < MC < beta, beta < MF < 2 beta and
K0 > 0. Hence 0 < (MC + q MF)J < beta J(1+2q) = (q-1)(2q+1) < 2q^2. If
F >= q then G <= alpha, and if F < q then 0 < G <= (q-1)^2 + alpha. In both
cases G(q^2-1) < q^4 + alpha q^2, so

    R < q^4 + (alpha + 2) q^2.                                       (5.2.1)

**5.3 Sizes.** We have Y >= 1, k >= 2, c = kY + eta > kY >= k, c >= 3,
c <= 2kY - 1, X >= q >= 16, a = Y(X+1) >= 17 and mu >= 257. Also
A' = mu(a+2)+1 > a, and H' = 4A'-5 > A' > a > X. Moreover a' >= 1 and
I >= mu c^2. Finally Delta' > mu^2 (a+2)^2 > V0 + 1, because
a^2 = Y^2(X+1)^2 > XY^2.

**5.4 Root brackets.** Let b' = cT' - R, an integer.

* (a) V0 k < tau < (V0+1)k.
* (b) (A'-1)c < Dm < A'c, so d = Dm/H' < c.
* (c) f > sqrt(Delta') I > (A'-1)I >= mu^2 (a+2) c^2. Also f < A'I + 1,
  because Df < (A'I)^2 + 1.
* (d) Dy = Dnum/delta = V^2 + (V^2-1)/(Q-1). If b' = 0, then V = -c,
  Q - 1 > c^2 - 1 > 0, so c^2 < Dy < c^2 + 1 and c < y < c+1. If b' != 0,
  then |V| >= Df - c >= 2 and |V| < y < 2|V|.

So delta > 0 and Dnum > 0, and all radicands of Corollary 2.2 are positive.

**5.5 Superincreasing roots.** Put A~ = (A'-1)I. Then

    f > A~ >= mu^2(a+2)c^2 > mu^2 XY c^2 >= V0 k c >= 3 V0 k
      > (V0+1)k + 2c + 1.                                            (5.5.1)

The last step holds because k + 2c + 1 <= 4c < 8kY <= 2V0 k, and
V0 >= 16 * 257^2 Y^2. Also V0 k > 4kY > 2c + 1.

* If b' = 0: the order is d < y < tau < f, each root exceeding the sum of
  the smaller ones. Indeed y > c > d; tau > V0 k > 2c + 1 > y + d; and
  f > tau + y + d by (5.5.1).
* If b' != 0: the order is d < tau < f < y. Indeed tau > V0 k > c > d and
  f > tau + d. Also f > c+2 and f(f-2) > c, so y > |V| >= f^2 - c > 2f.

Hence no nonempty signed subsum of tau, f, y, d vanishes.

**5.6 The transport majorant.** By (5.5.1), tau + 2c + 1 < A~. By 5.4(c),
f + 1 < A~ + I + 2 <= 2A~. Hence

    tau + f + (2c + 1) + 1 < 3 A~ < 4 A~.                            (5.6.1)

## 6. Soundness

Assume N = 0 at a strictly positive input.

**6.1 A signed root sum.** By Corollary 2.2, delta Mtot != 0, and all
factors are real, there are signs eps1,...,eps4 with

    Znum/Mtot = eps1 tau + eps2 f + eps3 y + eps4 d.                  (6.1)

**6.2 Rational roots.** The radicands are positive rationals, (6.1) is a
rational signed sum, and by 5.5 no nonempty signed subsum vanishes. By L1,
tau, f, y and d are rational, and so is Dm = H' d.

**6.3 Integral roots.** tau, f and Dm are rationals with integer squares, so
they are integers. The rational y satisfies Q V^2 - (Q-1) y^2 = 1 with Q > 1
and V an integer, so y is an integer by L2.

**6.4 The index modulus.** By (1.1), (6.1) becomes

    (X + a'c - eps4 Dm)/H' + Y/q^3 - W Bt/(q-1) - e/mu^2
        = eps1 tau + eps2 f + eps3 y - n - V,                        (6.4)

and the right side is an integer. By 5.1 and L3, mu^2 | e. Put
rho = e/mu^2, an integer. Also put the rationals

    g = (eps4 Dm - X - a'c)/H',   s = Y/q^3 > 0,   t = Bt/(q-1).

Then

    n = eps1 tau + eps2 f + (eps3 y - V) + g - s + W t + rho.         (6.5)

**6.5 Pell classification.**

* *First Pell.* tau^2 - V0(V0+1)k^2 = 1. Here d0 = V0(V0+1) lies strictly
  between V0^2 and (V0+1)^2, and V0^2 + V0 + 1 is not a square, so no
  solution has k = 1. Put P' = 2V0 + 1. Then (P', 2) is the least positive
  solution, and every positive solution is a power of it. Since
  2 sqrt(d0) = sqrt(P'^2-1), tau = chi_P'(n0) and k = 2 psi_P'(n0) for some
  n0 >= 1.
* *Main Pell.* Dm^2 - Delta' c^2 = 1, so c = psi_A'(p), Dm = chi_A'(p) with
  p >= 1.
* *Strong Pell.* f^2 - Delta' I^2 = 1 with I = i mu c^2 > 0.

**6.6 Early size of c.** If n0 = 1, then k = 2, so eta = zeta = 1 and
c = 2Y + 1. But psi_A'(1) = 1 < c, and psi_A'(p) >= 2A' > 2a > c for p >= 2.
So n0 >= 2 and

    c > kY >= k >= 2 psi_P'(2) = 4P' > 8 X mu^2 Y^2 >= 8 q^5.         (6.6)

**6.7 The auxiliary register is positive.** By (6.6) and (5.2.1),

    cT' = c(T + alpha) > 8q^5 (1 + alpha) > q^4 + (alpha+2) q^2 > R,

so b' >= 1 and V = Df b' - c >= Df - c > 0. By 5.4(d), y > V. Then

    y - V = (V^2-1)/((Q-1)(y+V)) < V/(2(Q-1)) < Df b'/(2(Q-1)) < b'/2,

using Df < Q - 1.

**6.8 Transport sign and outer bounds.** We have

    |rho| <= |e|/mu^2 < b'/2 + cT'/2.

Indeed |e| <= k + 1 + |R|. If R >= 0, then R < cT' and k + 1 <= c <= cT', so
|e| < 2cT'. If R < 0, then |e| <= k + 1 + b' - cT' <= b'. Use mu^2 >= 4.

Suppose Bt <= -1. Then W t <= -W/(q-1) < -L. Also eps3 y - V <= y - V. By
(5.6.1) and |g| < c + 1 + c, (6.5) gives

    n < tau + f + |g| + (y - V) + |rho| - L
      < 3 A~ + b'/2 + b'/2 + cT'/2 - L < 0,

because L = 4A~ + b' + cT'. This contradicts n >= 1. Hence Bt >= 0. Then
(K0 + w)C >= F >= 1, so C >= 1. Now G = (q-1)C + q alpha lies in
[q, q^2 - q], and 5.2 gives package 61's outer bound

    3q < q(q^2-1) < R < q^4 - 2.                                     (6.8)

**6.9 First index bound.** By (P5), psi_P'(n0) = n0 modulo P'-1 = 2V0, so
k = 2n0 modulo 4V0, and mu^2 | 4V0. Since mu^2 | e, 2n0 = R+1 modulo mu^2.
By (6.8), 0 < R+1 < q^4 < mu^2, so 2n0 >= R+1.

**6.10 Main index constraints.** By (6.6) and (6.8), c > 8q^5 > 2R. Also
c >= 3 forces p >= 2, and then c = psi_A'(p) > 2p by (P4).

**6.11 Rank.** Since c > 2 and c^2 | I, `lem:rank` gives f = chi_A'(m),
I = psi_A'(m) with pc | m, c | m and m > 2p.

**6.12 The main index is R.** Apply `lem:index` with A = A', S = Delta' I and
the integers V and eps3 y. The hypotheses hold: c | I | S and S >= 2;
S^2 = Delta'(f^2-1); 0 < p, R < c/2 (6.10);
S^2 V^2 - (S^2-1) y^2 = Q V^2 - (Q-1) y^2 = 1; V = Df b' - c = -c modulo f;
and Df = 1 modulo c, so V = -R modulo c. Hence p = R.

**6.13 The first index is (R+1)/2.** P' - A' = mu(2 mu X Y^2 - XY - Y - 2) > 0.
If n0 >= p, then k/2 = psi_P'(n0) >= psi_P'(p) >= psi_A'(p) = c > k, which is
impossible. So n0 <= R-1, and 0 <= 2n0 - (R+1) <= R-3 < mu^2. This number
is divisible by mu^2, so 2n0 = R+1. Thus R is odd. Put r = (R-1)/2; then
n0 = r+1, and r >= 24 because R > 3q >= 48.

**6.14 R = 3 modulo 4.** Apply L7 with A = A', p = R, the f and m of 6.11,
S = Delta' I, and the positive integers V (6.7) and y. Its hypotheses hold:
R >= 3 is odd and c > 2R; f > 2c (5.4(c)); c | m and m >= 2R;
S^2 = Delta'(f^2-1), c | S; V = -R modulo c and V = -c modulo f. Hence
R = 3 modulo 4.

**6.15 A first lower bound for Y.** Now c = psi_A'(2r+1) and
k = 2 psi_P'(r+1), and kY < c < k(Y+1) because 0 < eta < k. So
c/psi_P'(r+1) lies in (2Y, 2Y+2). By L4(a) with lam = mu, xi < 2Y + 2. Since
xi > X^r >= 16^24,

    Y > X^r/2 - 1 > X^r/3,       a > X^(r+1)/3.                      (6.15)

**6.16 Exponent and main-root sign (Archimedean step).** Since rho is an
integer, (6.4) gives

    (X + a'c - eps4 Dm)/H' + Y/q^3 - W Bt/(q-1)  is an integer.

Multiplying by q^3(q-1),

    H' | q^3 (q-1)(X + a'c - eps4 Dm).                               (6.16)

By L5 with A = A', and with c = psi_A'(R) and Dm = chi_A'(R), we have
Dm - a'c = 2^R and Dm + a'c = 2^(-R) modulo the odd modulus H'. By (6.15)
and X >= q >= 16,

    q^4 2^(R+1) X < X^(r+1) < 3a < H'.

For the first inequality, X^r >= q^4 16^(r-4) = q^4 2^(4r-16) > q^4 2^(2r+2).

* If eps4 = -1, then (6.16) and multiplication by 2^R give
  H' | q^3(q-1)(2^R X + 1). This multiple of H' is positive and less than
  q^4 2^(R+1) X < H', which is impossible.
* Hence eps4 = +1, and H' | q^3(q-1)(X - 2^R). Here
  |q^3(q-1)(X - 2^R)| < q^4 (X + 2^R) < q^4 2^(R+1) X < H', so

      X = 2^R.                                                       (6.17)

Now g = (Dm - X - a'c)/H' is an integer, so Y/q^3 - W Bt/(q-1) is an
integer. Multiplying by q^3(q-1) gives q^3 | (q-1)Y and q-1 | q^3 W Bt.
Coprimality then gives

    q^3 | Y,    q-1 | Bt.                                            (6.18)

So s and t are integers and t >= 0. Put z = t+1 >= 1. Since
Bt = (z-1)(q-1),

    (K0 + w)C + (q - F) - z(q-1) = 1.                                (6.19)

Finally q | X = 2^R, so q = 2^kappa with kappa >= 4.

**6.17 Y is the half-binomial.** By (6.15), 6r/a < 1/2, so
(1 + 3/a)^(2r) <= 1/(1 - 6r/a) <= 1 + 12r/a. Then L4(a) gives

    0 < c/psi_P'(r+1) - xi < 12 r xi/a < 12 r (2Y+2)/(Y(X+1)) <= 48r/(X+1) < 1/2.

Thus xi/2 < c/k < xi/2 + 1/4. By L6 and (6.17), xi/2 = M/2 + theta/2 with M/2
an integer and 0 < theta/2 < 1/8. So c/k lies in (M/2, M/2+1). It also
lies in (Y, Y+1), so

    Y = M/2.                                                         (6.20)

**6.18 A positive solution of package 61's source system.** Keep J, F,
alpha and w. Put s = Y/q^3 and take z from (6.19). With the same X = wq, Y,
a and E = XY, define the unscaled kernel

    A = a+2,  Delta = A^2-1,  H = 4a+3,  P0 = 2XY^2+1,
    c_o = psi_A(R),  D_o = chi_A(R),  k_o = 2 psi_P0(r+1),  tau_o = chi_P0(r+1),
    eta_o = c_o - k_o Y,  zeta_o = k_o - eta_o,
    h = (k_o - R - 1)/E,  gamma_o = (D_o - X - a c_o)/H.

* *Interval.* By (6.20), a > X^(r+1)/2, so 4r/a < 1/2. Then L4(b) and
  xi = 2Y + theta < 3Y give 0 < c_o/psi_P0(r+1) - xi < 24r/(X+1) < 1/4.
  So c_o/k_o lies in (Y + theta/2, Y + theta/2 + 1/8), inside (Y, Y+1),
  and eta_o, zeta_o are positive integers.
* *Index quotient.* By (P5), k_o = R+1 modulo 4XY^2, and E | 4XY^2. Also
  psi_P0(r+1) > r+1. So h is a positive integer.
* *Exponent quotient.* By L5 with A = a+2, D_o - a c_o = 2^R = X modulo H.
  By (P6), D_o - a c_o = 2c_o - psi_A(R-1) > c_o > k_o Y >= M > X. So gamma_o
  is a positive integer.
* *Strong pair.* Let m_o = R c_o and I_o = psi_A(m_o). By (P3),
  I_o = c_o psi_Do(c_o), and psi_Do(c_o) = c_o D_o^(c_o-1) = 0 modulo c_o,
  because c_o^2 | D_o^2 - 1. Put i_o = I_o/c_o^2 >= 1 and f_o = chi_A(m_o).
* *Auxiliary pair.* R >= 3, R = 3 modulo 4 (6.14), and c_o | I_o, so
  `lem:auxcomplete` gives positive T*, u. Here
  V_o = f_o^2(c_o T* - R) - c_o and Q_o V_o^2 - (Q_o-1)(V_o+u)^2 = 1, with
  Q_o = Delta^2 I_o^2. Put T_o = f_o T* and y_o = V_o + u.

These values satisfy package 61's normalized system (`eq:oldreg` through
`eq:oldtransport`):

* tau_o^2 - ell(ell+k_o) = 1, with ell = E k_o Y, since
  ell(ell+k_o) = XY^2(XY^2+1)k_o^2 = (P0^2-1) psi_P0(r+1)^2.
* D_o = X + a c_o + H gamma_o, and D_o^2 - Delta c_o^2 = 1.
* f_o^2 - Delta(i_o c_o^2)^2 = 1.
* With V_old = c_o(T_o f_o - 1) - R f_o^2 = V_o and
  Delta(f_o^2-1) = Q_o: Delta(f_o^2-1)(V_old^2 - y_o^2) + y_o^2 = 1.
* k_o - hE - R = 1, and (6.19) is the transport equation.

The registers q = beta J + 1, C, X = wq and Y = s q^3 are package 61's. All
fifteen coordinates

    J, F, alpha, z, f_o, h, i_o, T_o, s, w, tau_o, eta_o, zeta_o, y_o, gamma_o

are strictly positive integers. By `thm:source`, there is a finite
syntactic refutation of ZFC. The scaled kernel only pins down R, X, Y and
the divisibilities. The source theorem is applied to the fresh unscaled
witnesses.

## 7. Completeness

Assume a finite refutation of ZFC. `thm:source` gives a strictly positive
solution of package 61's system with these canonical promises:

* q = B^N with N odd and N > 1, and J = 1 + B + ... + B^(N-1);
* R = 3 modulo 4 and X = 2^R;
* c_o = psi_(a+2)(R), k_o = 2 psi_P0(n0) and n0 = (R+1)/2 >= 3.

Take its J, F, alpha, w, Y = s q^3 and z.

* J is odd and J >= 1+B, so j = (J-1)/2 >= 1. The transport equation gives
  (K0+w)C = (z-1)(q-1) + F > 0. So C > 0, (6.8) holds and r >= 24. Put
  t = z-1 >= 0; then Bt = (q-1)t.
* *Y = M/2.* The canonical kernel has 0 < eta_o < k_o, so
  Y < c_o/k_o < Y+1. By L4(b), xi < 2Y+2, so a > X^(r+1)/3 and 4r/a < 1/2.
  Then 0 < c_o/psi_P0(r+1) - xi < 32r/(X+1) < 1/4, and c_o/k_o lies in
  (M/2, M/2 + 1/4). So Y = M/2.
* *Scaled kernel.* Put c = psi_A'(R), Dm = chi_A'(R), k = 2 psi_P'(r+1) and
  tau = chi_P'(r+1). By L4(a), with xi = 2Y + theta and 12r/a < 1/2, we get
  0 < c/psi_P'(r+1) - xi < 12r(2Y+1)/(Y(X+1)) < 1/4. So c/k lies in
  (Y + theta/2, Y + theta/2 + 1/8). Put eta = c - kY and zeta = k - eta;
  both are positive. Then Dtau = tau^2 and Dmain = Dm^2.
* *Index excess.* k = 2(r+1) = R+1 modulo 4V0, and mu^2 | 4V0, so mu^2 | e.
  By (P4), e = 2(psi_P'(r+1) - (r+1)) > 0, so rho = e/mu^2 >= 1.
* *Projection.* By L5, Dm - a'c = 2^R = X modulo H'. By (P6),
  Dm - a'c = 2c - psi_A'(R-1) > c > kY > X. So g = (Dm - X - a'c)/H' >= 1.
* *Strong pair.* Let m = Rc mu and D = chi_A'(Rc). By (P3),
  psi_A'(Rc) = c psi_Dm(c) is divisible by c^2, as in 6.18. Also
  psi_A'(m) = psi_A'(Rc) psi_D(mu), and psi_D(mu) = mu D^(mu-1) modulo
  D^2 - 1 = Delta' psi_A'(Rc)^2. Since mu | A'-1 | Delta', mu | psi_D(mu).
  Hence mu c^2 | I = psi_A'(m). Put i = I/(mu c^2) >= 1 and f = chi_A'(m),
  so Df = f^2.
* *Auxiliary pair.* `lem:auxcomplete` with A = A' gives T*, u > 0. Here
  V* = Df(cT* - R) - c = Q_v(S^2), with S = Delta' I and v = (R-1)/2 >= 12,
  so V* >= (3S^2)^12 by (P8). Since Df <= S^2 and c < I < S,
  T* > V*/(c Df) > S^20 > alpha. The last step holds because the canonical
  solution has C > 0, so alpha < q < q^4 < Delta' <= S. Hence
  T = T* - alpha >= 1, T' = T*, V = V*,
  and y = V + u satisfies Q V^2 - (Q-1) y^2 = 1.
* *Sum variable.* Put s = Y/q^3 and

      n = W t + rho + g + tau + f + u - s.

  Here tau > k > Y >= s, because tau^2 > k^2 and k >= 2(2P'-1)^r > Y. The
  other terms are nonnegative, so n >= 1.

By (1.1),

    Znum/Mtot = n + V + (X + a'c)/H' + s - W t - rho
              = tau + f + (V + u) + Dm/H' = tau + f + y + d,

so the factor of Corollary 2.2 with all signs +1 vanishes and N = 0. The
weight W is computed from these witnesses; it imposes no condition. This
proves completeness.

## 8. Exact degree 816 and the operation count

Give every unknown degree 1 and every port and numeral degree 0. The
syntactic degrees of the registers are

    q 1, X 2, c 2, a 3, mu 2, A'-1 5, H' 5, Delta' 10, V0 8, Dtau 18, R 4,
    I 7, Df 24, Q 34, V 28, Dnum 90, Dmain 14, L 12, W 13,
    Mtot 13, Znum 41,

and of the arguments of F16

    fs 116,  fa 78,  fb 84,  fc 116,  fd 64.

The syntactic bound is therefore 8 * 116 = 928. The exact degree is lower,
because the carrier is centered. Put omega = fs - fc. Since
fc = delta Mtot^2 V^2 + Mtot^2(V^2-1) and Znum - Mtot V =: Z0,

    omega = delta Z0 (Z0 + 2 Mtot V) - Mtot^2 (V^2 - 1).

Here Z0 has degree 27, so omega has degree 34 + 27 + 41 = 102, while the
term Mtot^2(V^2-1) has degree 82.

**Lemma 8.1.** With L = eps1 ra + eps2 rb + eps4 rd,

    F16(s; a, b, s - omega, d) = prod over (eps1, eps2, eps4) of
                                 (omega + L^2 - 2xL),     where x^2 = s.

*Proof.* The sixteen factors of Lemma 2.1 pair as
(x - L - rc)(x - L + rc) = (x - L)^2 - c, which equals omega + L^2 - 2xL
when c = s - omega. QED

Give x, ra, rb, rd and omega the weights 58, 39, 42, 32 and 102. These
are half of, or equal to, the degrees of fs, fa, fb, fd and omega. In
each bracket:

* omega has weight 102;
* the monomials of L^2 have weight at most 84;
* the monomials of xL have weight at most 100.

So the product has weight at most 816, and its weight-816 part is
omega^8. Substituting the registers, each of degree at most its weight,
shows that N has degree at most 816. Its degree-816 component is
omega0^8, where omega0 is the leading form of omega:

    omega0 = 2 Q0 Z00 M0 V00,

with Q0, Z00, M0, V00 the leading forms of Q, Z0, Mtot and V. Write
q0 = 2 beta j and k0 = eta + zeta. Then

    mu0 = q0^2,  a0 = w q0 Y,  (A'-1)0 = mu0 a0,  Delta'0 = (mu0 a0)^2,
    H'0 = 4 mu0 a0,  I0 = i mu0 (k0 Y)^2,  Df0 = Delta'0 I0^2,  Q0 = Delta'0^2 I0^2,
    L0 = 4 mu0 a0 I0,  W0 = q0 L0,  Bt0 = w(q0 - F - alpha),
    M0 = q0^4 * q0^4 * H'0,
    Z00 = -H'0 q0^4 q0^3 W0 Bt0,
    V00 = -Df0 q0^3 (q0 - F).

The last uses R0 = q0^3(q0 - F): (cT' - R) has degree 4, coming from -R. All
of these are nonzero, so N has exact total degree 816 for every value of
the fixed ports. The top form does not involve K0, MC or MF.

Audit `degree` checks this with the actual ports. Random lines are taken
modulo 2^127-1 and 2^89-1. Each restriction of N has degree exactly 816,
and its leading coefficient equals omega0^8 at the direction vector.
Each restriction of omega has degree exactly 102, with leading
coefficient omega0.

The circuit has 124 rows: 74 multiplications, 30 additions and 20
subtractions. These include eight multiplications by numerals: 2j,
4(A'-1), 4(A'-1)I, 4(sd - sig2), 4 sig3 U, 16(sd Po^2 - 4 sig3 U),
16 sig3 and 64 sd Go^2. No row is dead, and every unknown and port is
used.

## 9. Remarks and attribution

* *Natural numbers.* Substituting v+1 for each unknown gives a ten-natural
  equation of the same degree, with at most ten extra additions.
* *Lineage.* Package 70's eleven-positive octic keeps the main Pell
  residual and its quotient gamma separately. Making the main root the
  fourth radical of one sixteen-fold norm removes both. The radical-residue
  archive (arrival 440dd03ab8, reviewed in
  `PROPOSAL_REVIEW_RADICAL_RESIDUE_POSITIVE.md`) did this first: 131
  operations, degree 1152, with Y = q^3 s and unscaled Pell parameters. The
  first version of this note found the same shape concurrently, with full
  coprimality from scaling by q(q-1)(q^2+1): 136 operations, degree 1216.
* *Adapted from that proof:* the Archimedean step (6.16), which tolerates a
  common factor of H' with q or q-1. It follows Sections 5-6 of its
  `ten_positive/PROOF.md`. The superincreasing orders, the descent and the
  inverse projection that fixes the main-root sign are also in that proof.
  Its literal circuit (`ten_positive/generated/p10_positive.json`) already
  evaluates the norm by the compact 28-operation schedule of Section 1.
* *Adapted from eleven-positive work:*
  - centering the carrier at V, together with the inner cancellation
    omega = delta Z0(Z0 + 2 Mtot V) - Mtot^2(V^2-1) of Section 8. This is
    the centered endpoint of `ZFC_Diophantine_Joint_Guards_2026-10-24.zip`,
    whose inner term is delta[z(z+2MV) - A - Bf] - M^2(V^2-1)
    (`PROPOSAL_REVIEW_WAVE11_POSITIVE.md`);
  - the offset auxiliary coordinate T + F + alpha and the second center
    Cf = (a+2)I, from the polynomial-shears arrival 440dd03ab8
    (`PROPOSAL_REVIEW_POLYNOMIAL_SHEARS_POSITIVE.md`). The adaptive
    candidate inherits the offset unchanged.
* *New here:*
  - both Pell parameters scaled by mu = q^2+1, with A' = mu(a+2)+1 and
    P' = 2X mu^2 Y^2+1. The ratio bounds (L4(a)) are kept. mu^2 enters the
    first-index modulus while Y stays a free unknown of degree 1, and only
    the index congruence needs a coprime partial fraction (6.4). X = wq is
    built in;
  - the offset alpha alone, justified by the mask bound (5.2.1, 6.7). It
    lets the single-centered transport weight have degree 13 (5.6, 6.8);
  - the sixteen-fold pairing (Lemma 8.1) and weight argument proving the
    exact degree 816.

  The scaled kernel only pins down R, X, Y and the divisibilities.
  Package 61's theorem is applied to fresh unscaled witnesses (6.18).
* *Limits.* Global minimality is not claimed. The compiler and calibration
  are inherited through package 61's `thm:source`, and no Lean
  formalization was done. The fixed ports are 590,069-bit integers, as for
  every equation bound to this tuple.
