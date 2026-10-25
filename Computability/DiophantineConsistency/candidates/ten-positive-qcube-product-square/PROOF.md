# q-cube normalization of the product-square kernel: proof

An ordinary arithmetic reduction relative to the calibration of its parent,
wave-14 package 133 (`con-zfc-diophantine-forms/133-staged-certificates/compact/`),
with that package's whole indexed compact44 coefficient tuple. No Lean or
internal-ZFC certificate, consistency claim or minimality claim is made.

## 0. Sources

- **The product-square kernel** is package 133's (its `compact/PROOF.md`):
  Pell doubling of the strong pair makes Q a multiple of the whole combined
  radicand G = E·F0, so one product-square equation forces all roots and
  the centre becomes Z/M = ε·g·y. Its circuits `equation_84.json` (weight
  L = V², 84 operations, degree 436) and `equation_85.json` (L = b·V, 85,
  328) are the parents, pinned by SHA-256 in `build.py`.
- **q-cube normalization** (Y = q³·s and cancellation of the common q³) is
  the research session's `research/ten-positive-qcube-normalization`
  (commit 75f850496c, 89 → 86 operations on the uncentred two-root kernel),
  which developed a measured remark of this repository's
  `candidates/ten-positive-gap-fusion`.
- **Completeness** inherits 133's section 8 as repaired by the research
  session's `research/ten-positive-doubled-product-square/PROOF.md`
  (accepted in commit a223b3e174, after the review
  `reviews/staged-certificates-compact-ordinary-peer.md`): the actual
  canonical bound R > 3q ≥ 96, not the generic R ≥ 3, is needed for the
  shifted input T = T′ − α to be positive. That proof's section 8 and
  equation (11), n = gy + Wt + ρ − κ − s with g > κ + s, are used below.

The same composition was committed first by the research session as the
code-free proposal `research/ten-positive-qcube-doubled/PROPOSAL.md`
(`a576e152f4`, 24 October 2026, 22:07), with the same polynomials and
leading forms; this proof was written independently and concurrently. Its
sections 1–3 give the transfer of 133's soundness and completeness and the
exact degrees in this package's own terms.

## 1. The equations and the transfer identity

Use 133's notation (its section 1): q = βJ + 1, h = q − 1, C = q − F − α,
X = wq, μ = q² + 1, k = η + ζ, c = kY + η, A = μY(X + 1) + 1, Δ = A² − 1,
H = 4A − 5, V0 = Xμ²Y², E = 1 + V0(V0 + 1)k², R, e = k − R − 1,
B = (K0 + w)C − F, U = ic², a = ΔU²E, F0 = 1 + a, G = E·F0,
Fsq = 1 + 4aF0, Q = Δ(Fsq − 1), b = c(T + α) − R, V = Fsq·b − c,
Kpos = X(3c − 2X) + 2, and L = V² (for 133's 84) or L = b·V (for its 85).
133's polynomial is

    N133 = Q(Z² − RG·V²) + (RG − Z²),   RG = M²·G,
    Z = P μ²[H(n − L·B) + Kpos] + H[μ²(hY − q³B) − P e],   M = P μ² H,   P = q³h.

The new circuits have the ten strictly positive unknowns
J, F, α, i, T, w, s, n′, η, ζ. Every register is computed as in 133 with
**Y := q³·s**, and with

    Z′ = h μ²[H(n′ − L·B) + Kpos] − H[μ²·B + h·e],   M′ = h μ² H,
    N  = Q(Z′² − RG′·V²) + (RG′ − Z′²),   RG′ = M′²·G.

Substituting Y = q³s and n = n′ − s into 133's Z gives
Z = q³·Z′ exactly: the term P μ² H·n becomes q³ h μ² H(n′ − s), and
H μ² h Y = q³·h μ² H·s cancels the −s; the other terms carry q³ through
P = q³h and q³B. Also M = q³·M′. Since N133 is homogeneous of degree 2 in
(Z, M) (RG = M²G),

    q⁶ · N(n′, s, …) = N133(n = n′ − s, Y = q³s, …)                     (T)

as polynomials. In particular

    Z′/M′ = Z/M = n′ − L·B + Kpos/H − B/h − e/μ²                         (C)

(133's centre with Y/q³ = s moved into n′). `verify.py` checks (T) and (C)
at random points against the pinned parent circuits.

The literal schedules (`build.py`) differ from the parents by one added
row (Y = q3·s), the deletion of P1 = q3·bJ, the replacement of
P1mu2 = P1·mu2 by hmu2 = bJ·mu2, and the replacement of the eight
low-bracket rows by five: 84 + 1 − 1 − 8 + 5 = 81 and 85 → 82 operations.

## 2. Soundness and completeness

**Soundness.** Let all ten unknowns be positive and N = 0. By (T),
N133 vanishes at Y = q³s ≥ 1 and n = n′ − s. 133's sections 2–4 (positivity,
automatic coprimality, root recovery, folding, the first Pell equation and
the early bounds) never use n; they give positive integers g, y with
Z/M = ε·g·y. By (C), with W = 1 + hL, κ = Kpos/H and ρ = e/μ²,

    n′ = ε·g·y + W·B/h − κ + ρ.                                          (S)

This is 133's equation (8) with n replaced by n′ and its −s term absent.
133's transport arguments (its sections 5 and 6) bound n above by
ε·g·y + W·B/h + ρ after discarding −κ − s; the same bound holds for n′ after
discarding −κ. So B ≤ −1 gives n′ < 0 exactly as there (with L = V²:
n′ < V²/2 − V² + V/μ² < 0; with L = bV: n′ < L/2 − L + b/μ² < 0),
contradicting n′ ≥ 1. Hence B ≥ 0 and C > 0. Every later step of 133's
section 7 uses only the rational centre, now (C) with integral Y/q³ = s,
and its hypotheses; the partial-fraction step "q³ | Y" holds by
construction. The fresh unscaled source reconstruction then gives a finite
syntactic ZFC refutation through the same calibration.

**Completeness.** From a finite refutation take the repaired canonical
witnesses of section 0 (all ten of 133's inputs, with R > 3q ≥ 96): in
particular q³ | Y, s = Y/q³ ≥ 1, integers t ≥ 0, ρ ≥ 0, κ > 0, and
g > κ + s, so that 133's n = gy + Wt + ρ − κ − s is positive. Keep every
input except Y and n, take the new input s := Y/q³, and put

    n′ = g·y + W·t + ρ − κ = n133 + s,

which is a positive integer (it exceeds 133's positive n). By (T) the new
polynomial vanishes. So each circuit has a positive zero exactly when ZFC
has a finite syntactic refutation, an equivalence provable in ZFC by these
ordinary arguments and the inherited calibration.

## 3. Exact degrees

All unknowns have degree 1 and the ports degree 0. With Y = q³s the
registers have degrees (measured, and matching the syntactic bounds)

| Register | 81 (L = V²) | 82 (L = bV) |
|---|---:|---:|
| Q | 152 | 152 |
| V | 142 | 142 |
| RG′ = M′²G | 124 | 124 |
| Z′ | 299 | 163 |

In N = Q·Z′² − Q·RG′·V² + RG′ − Z′² the four terms have degrees:

- 81: 750, 560, 124, 598, so the top is Q0·Z′0²;
- 82: 478, 560, 124, 326, so the top is −Q0·RG′0·V0².

Each leading form is a product of leading forms of products, and of sums
dominated by one summand: Fsq = 4aF0 + 1, V = Fsq·b − c, b = c(T + α) − R
(degree 6 against 4 with Y = q³s), B = (K0 + w)C − F, H = 4(A − 1) − 1,
and, for Z′, the term −hμ²H·L·B, which exceeds n′, Kpos and the low
bracket H(μ²B + he). Four sums have summands of equal degree, and their
leading forms are the nonzero linear forms q0 − F, q0 − F − α, k0 = η + ζ
and T + α, where q0 = βJ. Writing C0 = q0 − F − α, the leading forms are

    81:   2¹⁴ β⁵⁰⁶ J⁵⁰⁶ i²⁰ w⁴⁶ s¹⁰⁸ k0⁶⁴ (T + α)⁴ C0²,
    82:  −2¹⁰ β³⁸⁴ J³⁸⁴ i¹⁴ w³⁴ s⁸⁰ k0⁴⁶ (T + α)²,

which are nonzero. So the exact total degrees are **750** and **560**.
`verify.py` checks that the syntactic degree bound of N is 750 and 560, so
the degree is at most that. It checks that the measured degree along random
lines equals that bound, so the degree is at least that. And it checks that
the measured top coefficient along random rays equals Q0·Z′0² or
−Q0·RG′0·V0², built from the measured register tops.

## 4. Scope

The equivalence is relative to package 133's calibration (the inherited
source61/native/controller theorem with its whole indexed tuple), with
133's completeness corrected as in section 0. The two circuits are
operation/degree tradeoffs against 133's 84/436 and 85/328.
