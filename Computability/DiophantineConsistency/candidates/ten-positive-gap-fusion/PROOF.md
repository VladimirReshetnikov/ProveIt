# Coprime fusion with the auxiliary-index gap majorant: proof

This is an ordinary arithmetic reduction relative to the inherited
source/native/refutation calibration, in the same sense as its parents. It is
not a Lean or Rocq proof and not an internal object-ZFC certificate, and it
claims no optimality.

## 0. Sources and what is new

Four published devices are combined; none is new here.

- **Coprime fusion** of the first and strong Pell roots into one radical
  sqrt(D·F_s), with gcd(D, F_s) = 1 because F_s ≡ 1 (mod D). It was found
  independently by wave-12 package 116 (`116-coprime-projection/positive/PROOF.md`,
  direct coordinate, 96 operations, degree 266) and package 113
  (`113-saturated-pell`, report sections on saturation semantics; scaled and
  direct coordinates, 92/283 to 99/254).
- **The auxiliary-index gap** of package 118
  (`118-structural-compression/positive/PROOF.md`, section 6): the auxiliary
  Pell index is at least 5, so the auxiliary parameter b itself is a valid
  transport majorant.
- **Centres** at a multiple of D·E, from package 113's "upper and sharp
  centers" (lemma `lem:sat-centers`), here with the lower centre (A−1)·D·E as
  well as its sharp centre A·D·E.
- **The weight W = 1 + g·b on a centred fused kernel** is already in wave-12
  package 117 (`117-quadratic-frames/ten_positive/`, sharp centre, 93/278):
  with a centre above tau·f no gap lemma is needed there. The research
  session applied the same weight to 113's four centred forms
  (`research/ten-positive-reused-b-weight`, fc77fcd31a).

The scaled zero-offset coordinate is the research session's
`candidates/ten-positive-zero-offset/` (a descendant of this repository's
`candidates/ten-positive-scaled-norm/`), and the expanded transport identity
is package 116's section 8 and the research session's.

The fused-kernel version of 118's gap argument (section 3) was found
independently and concurrently by the research session: its
`research/ten-positive-uncentered-b-weight` (commit 90d8b714f9, 24 October,
16:29) proves the same fifth-index gap and gives the same 89/288 polynomial
(`zero89`) and the 94/262 polynomial in 95 operations (`direct95`). This
packet was built from 116's schedule in the same half hour. What is new here
relative to it: the direct-coordinate schedules are one row shorter (94/262
and 97/254, from 116's direct carrier), the lower centre (A−1)·D·E gives two
further polynomials (91/283 and 96/258), and one transport-sign proof and one
exact-degree proof cover all six circuits (sections 4 and 6). Lemma G is
needed for the uncentred forms and for the lower centre, whose residue
tau·f − Gamma can be close to D·E; only the sharp centre A·D·E, which lies
above tau·f, could do without it (as package 117 does).

## 1. The six equations

The ten unknowns are strictly positive integers J, F, alpha, i, T, ξ, Y, n,
eta, zeta, where ξ = w in the scaled coordinate and ξ = x in the direct one.
The fixed ports are the whole original compact44 tuple bound in
`coefficients/BINDING.json` (the tuple of package 116); they satisfy
beta odd, beta ≥ 31, K0 > 0 and 0 < MC < beta < MF < 2·beta. Define

    q = beta·J + 1,          C_d = q − F − alpha,
    scaled:  X = w·q,  g = q − 1,      B = (K0 + w)·C_d − F,       P = q³(q − 1),
    direct:  X = q + x,  g = q(q − 1),  B = (q·K0 + X)·C_d − q·F,   P = q⁴(q − 1),
    mu = q² + 1,  A = mu·Y·(X + 1) + 1,  Delta = A² − 1,  H = 4A − 5,
    k = eta + zeta,  c = k·Y + eta,
    V1 = X·mu²·Y²,  D = V1·(V1 + 1)·k² + 1,
    G = (q − 1)(q − F) + alpha,  R = G·(q² − 1) + (MC + q·MF)·J,  e = k − R − 1,
    E = i·c²,  F_s = 1 + Delta·D·E²,  Q = Delta²·D·E²,  delta = Q − 1,
    b = c·(T + alpha) − R,  V = F_s·b − c,  Dnum = Q·V² − 1,
    M = P·mu²·H,  Kpos = X·(3c − 2X) + 2,  W = 1 + g·b,
    Gamma ∈ { 0,  (A − 1)·D·E,  A·D·E },
    Z = P·mu²·[ H·(n + V + Gamma − b·B) + Kpos ]
        + H·[ mu²·(g·Y − q³·B − Dlow) − P·e ],   Dlow = 0 (scaled), (q − 1)·X (direct),
    a = D·F_s,  s = delta·Z²,  u = delta·M²·a,  v = M²·Dnum,
    N = (s − v − u)² − 4·u·v.

The equation is N = 0. Every displayed symbol is a polynomial in the ten
unknowns. Dividing Z by M gives the exact rational centre

    Z/M = n + V + Gamma + Kpos/H + Y/q³ − W·B/g − [X/q⁴] − e/mu²,          (1)

with the bracketed term only in the direct coordinate; the identity
−b·B − B/g = −W·B/g is the expanded-transport identity. Divisions in (1)
are proof notation only.

The literal schedules are produced by `build.py` from package 116's tracked
96-row schedule, pinned by SHA-256:

- delete the rows `HI = H·(D·E)` and `L = HI + b`, and read b (the register
  `cTR`) wherever L was read: **94 rows** (direct, Gamma = 0);
- scaled coordinate: replace the five rows of the direct B by the three rows
  `K0w`, `K0wC`, `B`, delete `qbJ` and `lowX`, merge `inner0`/`inner`, and
  compute `P1 = q3·bJ`, `lowY = bJ·Y`: five rows fewer, **89 rows**;
- centre: add `Cg = (A − 1)·(D·E)` and `nVCg = nV + Cg` (two rows), or
  `Afull = (A − 1) + 1`, `Cg = Afull·(D·E)`, `nVCg` (three rows).

| Circuit | Coordinate | Gamma | Rows | ×/+/− | Exact degree |
|---|---|---|---:|---|---:|
| `gap_fusion_scaled` | scaled | 0 | 89 | 53/18/18 | 288 |
| `gap_fusion_scaled_lower_centre` | scaled | (A−1)DE | 91 | 54/19/18 | 283 |
| `gap_fusion_scaled_sharp_centre` | scaled | ADE | 92 | 54/20/18 | 278 |
| `gap_fusion_direct` | direct | 0 | 94 | 56/19/19 | 262 |
| `gap_fusion_direct_lower_centre` | direct | (A−1)DE | 96 | 57/20/19 | 258 |
| `gap_fusion_direct_sharp_centre` | direct | ADE | 97 | 57/21/19 | 254 |

## 2. Inherited steps that precede transport

The following hold at every positive zero, in this order, by the cited
arguments. None uses the transport majorant, the centre Gamma, transport
positivity, parity of q, the identity p = R, or q | X.

1. **Root extraction.** The radicands a and Dnum/delta are positive and
   unequal (reduce delta·a = Dnum modulo D > 1: the left side is 0 and
   Dnum ≡ −1). The norm gives Z/M = eps·sqrt(a) + nu·sqrt(Dnum/delta) with a
   nonzero rational sum, so both roots are rational; gcd(D, F_s) = 1 gives
   D = tau² and F_s = f² with positive integers tau, f. With I = tau·E,
   f² − Delta·I² = 1, Q = (Delta·I)², c² | I and I ≥ c. Adjacent-Pell descent
   makes y = sqrt(Dnum/delta) a positive integer. Thus

       Z/M = eps·tau·f + nu·y,   eps, nu ∈ {+1, −1}.                         (2)

   (116 section 2 for the direct coordinate; 113's section "Two roots recover
   the three required Pell conditions" for the scaled one. The argument does
   not involve X beyond X ≥ q ≥ 32, and never involves Z.)
2. **Folding and the first Pell equation.** The strong/auxiliary folding
   lemma gives c = psi_A(p) for an odd p ≥ 1; the first equation D = tau²
   gives k = 2·psi_(2V1+1)(n0), and n0 = 1 is excluded, so
   c > k·Y ≥ k ≥ 4(2V1 + 1) > 8·X·mu²·Y² (116 section 3, (4); the
   zero-offset proof section 3).
3. **Early bounds.** The mask estimate gives R < c·alpha/4, hence
   b = c(T + alpha) − R > c(T + 3alpha/4) > c, V > 0, and c > 2X gives
   Kpos > 0. Moreover f < A·I and

       tau·f + [X/q⁴] < H·D·E                                               (3)

   (116 (5); in the scaled coordinate tau·f < A·tau²·E = A·D·E < H·D·E).

## 3. The auxiliary-index gap in the fused kernel

**Lemma G.** At every positive zero, before transport, V > 8Q² and b > 8Q.

*Proof.* Since c ≥ 3 > 1 = psi_A(1) and p is odd, p ≥ 3, so

    c ≥ psi_A(3) = 4A² − 1 = 4·Delta + 3 > 4·Delta.

Put S = Delta·I, so S ≥ 2 and Q = S² by step 1. The auxiliary equation
Q·V² − (Q − 1)·y² = 1 reads (S·V)² − (S² − 1)·y² = 1 with S·V > 0 and y > 0,
so S·V = chi_S(v) for an index v ≥ 1, where chi_S(0) = 1, chi_S(1) = S and
chi_S(m+1) = 2S·chi_S(m) − chi_S(m−1). Modulo S the recurrence gives
chi_S(m+1) ≡ −chi_S(m−1), so chi_S(m) ≡ 0 (mod S) exactly for odd m; hence v
is odd. Now

    chi_S(1)/S = 1,   chi_S(3)/S = 4S² − 3 = 4Q − 3,   chi_S(5)/S = 16Q² − 20Q + 5.

Since b ≥ c + 1, V = F_s·b − c > (F_s − 1)·c = Delta·D·E²·c > 4·Delta²·D·E² = 4Q.
This excludes v = 1 and v = 3. So v ≥ 5 and, chi_S being increasing,
V ≥ 16Q² − 20Q + 5 > 8Q² (Q ≥ 3). Finally F_s = 1 + Delta·D·E² < Delta²·D·E² = Q,
so b = (V + c)/F_s > V/F_s > 8Q²/Q = 8Q. ∎

This is package 118's section 6.1 with Df replaced by F_s = 1 + Delta·D·E² and
Q by Delta²·D·E²; the only new inequality to check is F_s < Q, and the
factor D cancels from both sides of V > 4Q.

**Corollary.** Before transport,

    tau·f + [X/q⁴] < H·D·E < b/2,      0 < y − V < b/4,      e/mu² < b/4.     (4)

*Proof.* Since H < 4·Delta²·E, we have 2·H·D·E < 8·Delta²·D·E² = 8Q < b by
Lemma G; with (3) this is the first bound. For the auxiliary root, y > V by the auxiliary
equation, and

    y − V = (V² − 1)/((Q − 1)(y + V)) < V/(2(Q − 1)) < F_s·b/(2(Q − 1)) < b/4,

using V < F_s·b and Q − 1 − 2F_s = Delta·D·E²·(Delta − 2) − 3 > 0. Finally
b − e = c(T + alpha) − k + 1 > 0 because c > k, so e < b and
e/mu² < b/mu² < b/4 (trivially if e ≤ 0). ∎

## 4. Transport sign, and the rest of soundness

**Lemma T.** At every positive zero, B ≥ 0, for each of the three centres.

*Proof.* Solve (1)–(2) for n:

    n = (eps·tau·f − Gamma) + (nu·y − V) − Kpos/H − Y/q³ + W·B/g + [X/q⁴] + e/mu².

Here Gamma ≥ 0, Kpos/H > 0 and Y/q³ > 0, and nu·y − V ≤ y − V. By (4),

    n < b/2 + b/4 + b/4 + W·B/g = b + W·B/g.

If B ≤ −1 then W·B/g ≤ −W/g = −b − 1/g < −b, so n < 0, contradicting n ≥ 1. ∎

Then C_d > 0 (from B ≥ 0 and F ≥ 1), the mask estimate gives
3q < R < q⁴ − 2, and every later soundness step is inherited unchanged:
the strong rank and signed auxiliary index give p = R; R odd gives q even
and J odd; gcd(mu², P·H) = 1 isolates mu² | e; the first-index congruence
gives n0 = (R + 1)/2; the zero-offset ratio lemma gives Y > X^r/3 and
X^(r+1) < H (R = 2r + 1, r ≥ 48); the integral centre gives H | P·Kpos, and
the whole-product projection gives X = 2^R; partial fractions give q³ | Y
and g | W·B, hence (q − 1) | B in the scaled coordinate (after q | X and
B = q·B_t in the direct one); fixed-minus parity gives R ≡ 3 (mod 4); and
the fresh unscaled source reconstruction gives a finite refutation through
the inherited source61/native/controller calibration (116 sections 3–4;
zero-offset proof sections 3–4 for the scaled coordinate, together with
113's section "Licenses for the inherited index and projection proof" for
the fused scaled kernel).

These steps use only the rational part of (1). The centre Gamma is an
integer polynomial; in Z it is multiplied by M = P·mu²·H and vanishes modulo
H, mu² and P. W ≡ 1 (mod g) still holds because W = 1 + g·b. So the centre
and the new majorant change none of these arguments.

## 5. Completeness

Suppose a finite refutation exists. Take package 116's canonical witnesses
(direct coordinate), or for the scaled coordinate the zero-offset parent's
canonical source data at the same whole original tuple, completed by 113's
ordinary-chart construction of the strong pair and auxiliary witness (that
construction is uniform in the tuple):
the source data with X = 2^R, R ≡ 3 (mod 4), r ≥ 48, q³ | Y, t = B/g ≥ 0;
c = psi_A(R), k = 2·psi_(2V1+1)(r + 1), tau = chi_(2V1+1)(r + 1), eta, zeta > 0,
rho = e/mu² ≥ 1; a strong pair I = psi_A(m), f = chi_A(m) with tau·c² | I
from a finite Pell-matrix period, i = I/(tau·c²) > 0; and the auxiliary
witness V* = chi_S(R)/S, y = psi_S(R), T = T* − alpha > 0 from the
auxiliary-completeness lemma. The literal registers then equal these values,
and b > 0, so W = 1 + g·b ≥ 1. Put kappa = Kpos/H, sY = Y/q³ and
u = y − V* > 0, and define

    n = W·t + rho + (tau·f − Gamma) + u − sY − kappa + [X/q⁴].

Every term is an integer; the centre (1) equals tau·f + y, so a factor of the
quartic norm vanishes. It remains to show n > 0.

Since R ≥ 5 is odd, V* = chi_S(R)/S ≥ chi_S(5)/S > 8Q². From the auxiliary
equation, y < 2V*, hence

    u = (V*² − 1)/((Q − 1)(y + V*)) > V*/(4Q) > 2Q.

The loss terms satisfy:

- Gamma = 0: no loss; tau·f > 0.
- Gamma = (A − 1)·D·E: f² − (A − 1)²·I² = 1 + (2A − 2)·I² > 0 gives
  f > (A − 1)·I, so tau·f − Gamma > 0.
- Gamma = A·D·E: A²·I² − f² = I² − 1 gives A·I − f < I/A, so
  Gamma − tau·f = tau·(A·I − f) < tau·I/A = D·E/A < D·E.

In every case the total negative contribution is below D·E + sY + kappa.
Here D·E ≤ Q/Delta², sY < Y < c and kappa < c (since H > 3X and
Kpos < 3X·c), so it is far below 2Q < u. Hence n > 0 for all six circuits.
The map is a fresh existence construction; no pointwise inverse between the
zero sets of these circuits and their parents is claimed.

Together with section 4 this proves, for each of the six polynomials N, the
same statement as for its parents: N has a zero in ten strictly positive
integers if and only if the inherited syntactic refutation calculus derives
a contradiction from ZFC, an equivalence provable in ZFC by these ordinary
arguments and the inherited calibration.

## 6. Exact degrees

Write Z = M·(V + Gamma) + Z0, so

    Z0 = P·mu²·[ H·(n − b·B) + Kpos ] + H·[ mu²·(g·Y − q³·B − Dlow) − P·e ].

With Dnum = (delta + 1)·V² − 1 and a = D·F_s, direct expansion gives the
polynomial identities

    s − v − u = 2·delta·M²·V·Gamma + beta,
    beta = delta·M²·(Gamma² − a) − M²·(V² − 1) + 2·delta·M·(V + Gamma)·Z0 + delta·Z0²,
    N = 4·delta²·M⁴·V²·(Gamma² − a) + 4·delta·M²·V·Gamma·beta + beta²
        − 4·delta·M⁴·a·V² + 4·delta·M⁴·a.                                     (5)

Since F_s = 1 + Delta·D·E² and Gamma = G̃·D·E with G̃ ∈ {0, A − 1, A},

    Gamma² − a = D²·E²·(G̃² − Delta) − D = −Delta·D²·E² − D,
                 −(2A − 2)·D²·E² − D,   or   D²·E² − D.                       (6)

All unknowns have degree 1 and the ports degree 0. The registers have these
syntactic degrees, and their homogeneous leading forms are products of
nonzero forms (q0 = beta·J):

| Register | scaled | direct | leading form |
|---|---:|---:|---|
| q, mu | 1, 2 | 1, 2 | q0, q0² |
| X | 2 | 1 | w·q0 or q0 + x |
| A, Delta, H | 5, 10, 5 | 4, 8, 4 | A0 = mu0·Y·X0, A0², 4A0 |
| D | 18 | 16 | (X0·mu0²·Y²)²·k² |
| E | 5 | 5 | i·k²·Y² |
| F_s, Q = delta | 38, 48 | 34, 42 | Delta0·D0·E0², Delta0²·D0·E0² |
| b | 4 | 4 | −q0³·(q0 − F) |
| V | 42 | 38 | F_s0·b0 |
| M | 13 | 13 | q0⁴ or q0⁵, times mu0²·4A0 |
| a | 56 | 50 | D0·F_s0 |
| Gamma (nonzero) | 28 | 25 | A0·D0·E0 |
| Z0 | ≤ 19 | ≤ 19 | — |

(b's leading form is −R0 because R has degree 4 and c(T + alpha) degree 3.)
Bounding each term of (5):

| Term | scaled 0 | scaled (A−1) | scaled A | direct 0 | direct (A−1) | direct A |
|---|---:|---:|---:|---:|---:|---:|
| 4·delta²·M⁴·V²·(Gamma² − a) | **288** | **283** | **278** | **262** | **258** | **254** |
| 4·delta·M²·V·Gamma·beta | — | ≤ 269 | ≤ 266 | — | ≤ 245 | ≤ 243 |
| beta² | ≤ 260 | ≤ 250 | ≤ 244 | ≤ 236 | ≤ 228 | ≤ 224 |
| 4·delta·M⁴·a·V² | 240 | 240 | 240 | 220 | 220 | 220 |
| 4·delta·M⁴·a | 156 | 156 | 156 | 144 | 144 | 144 |

(For example, in the scaled coordinate with Gamma = 0, the terms of beta
have degrees 130, 110, ≤ 122 and ≤ 86.) In every column the first term is
strictly highest, and by (6) its leading form is

    Gamma = 0:         −4·delta0²·M0⁴·V0²·a0,
    Gamma = (A−1)DE:   −8·delta0²·M0⁴·V0²·A0·D0²·E0²,
    Gamma = A·D·E:      4·delta0²·M0⁴·V0²·D0²·E0²,

a product of nonzero polynomials, hence nonzero. So the exact total degrees
are 288, 283, 278 (scaled) and 262, 258, 254 (direct), for the actual fixed
tuple as for generic ports (the leading forms involve beta but no other
port).

`verify.py` checks the identity (5) at random points, the three leading forms
against the top coefficient of N(t·x) along random rays through the origin,
and the degrees along random lines modulo 2^127 − 1 and 2^89 − 1. These finite
checks confirm transcription; the proof is the argument above.

## 7. Scope

Each of the six equations is relative to exactly the calibration of its
parents: package 116's source/native/refutation pins for the direct
coordinate and the zero-offset kernel's for the scaled one, with the whole
original compact44 tuple. A whole BFS tuple satisfying the same port box
instantiates the same argument; no port of one tuple is substituted into the
other. No consistency claim, Lean theorem or internal-ZFC certificate is
made.
