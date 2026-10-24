# Where the ten-positive kernel is tight, and what a smaller equation needs

Written 24 October 2026, after wave 11. This note records analysis, not an
equation. Its numbers were measured with the actual compact44 coefficients
(line restrictions modulo 2^127 − 1) unless marked as a claim.

## 1. The descendant and its degree budget

This directory's four-root equation (124 operations, degree 816) became the
parent of the research session's
[ten-positive-zero-offset](../ten-positive-zero-offset/README.md) (99
operations, exact degree 368). That equation keeps the mu-scaling, the
offset T' = T + alpha, the centering at the auxiliary register and the
Archimedean separation, removes the main Pell root by the psi-only
register Kpos = X(3c − 2X) + 2 and a strong/auxiliary folding lemma, and
weights the three remaining roots (3 tau, f, y) in one octic.

Its exact degree is 368 = 4 · 92, where 92 is the degree of the centered
difference omega = fs − fc:

    omega = delta · Z0 · (Z0 + 2 M V) − M^2 (V^2 − 1),
    deg omega = deg delta (30) + deg Z0 (25) + deg (M V) (37) = 92.

Each term is at the minimum this architecture allows:

- `mu = q^2 + 1` (degree 2) is the smallest scaling whose square exceeds
  the index range: the first-index congruence needs a modulus coprime to
  q^3, q − 1 and H' and larger than R + 1 < q^4. A degree-2 factor is
  forced; (q^2 + 1)(q^2 − q + 1) would also work and has the same degree.
- `I = i c^2` (degree 5) is forced by the rank lemma (c^2 | I).
- `delta = Q − 1 = (Delta' I)^2 − 1` (degree 30) is the denominator of the
  auxiliary root y^2 = (Q V^2 − 1)/(Q − 1); it multiplies three of the four
  norm arguments.
- `Z0` (degree 25) is dominated by the transport term q^3 · mu^2 · H' · W · Bt
  with W of degree 11; W must exceed the strong root f (degree 10), so
  deg W ≥ 11.
- `M V` (degree 37): M = q^3 (q − 1) mu^2 H' (13) clears the four
  denominators; V = Df (c T' − R) − c (24).

Two further ideas were measured and both lose:

- Centering the strong root at (A' − 1) I adds a center term of degree 28
  above Z0's 25, so omega grows. (On the four-root parent the same trick
  did help: 816 → 796 at 127 operations, because there the strong root's
  pairing partner was different.)
- Folding tau into f by Jones's product square, I = i c^2 Dtau, makes I of
  degree 23 and the quartic norm of degree 378.

A different auxiliary equation with an integral radicand (Jones's
I = (G^2 − 1) H^2 + 1 with an index unknown j) would remove delta from
three arguments but costs the unknown j and a large G; it was not pursued.

So within this kernel the remaining gains are a few operations. No
rearrangement of the registers lowers the degree significantly.

## 2. Why nine positive unknowns need a new encoding

The kernel spends seven unknowns on the Pell side (w, Y, i, T, eta, zeta,
n) and three on the source (J, F, alpha). Jones's nine-unknown layout
spends the same seven plus two source unknowns (b, g), which is how the
collection's nine-positive equations reach nine, at the price of the
H2082 gap source whose radix exponents give degrees near 10^6.

The compact44 source carries two base-q digits of the halting tableau,
F and C = q − F − alpha, inside one word S = qF + C with R = (q^2 − S)(q^2 − 1) + T_w.
The transport equation (K_0 + w) C ≡ F (mod q − 1) tests the two residues
F mod (q − 1) and C mod (q − 1) independently (q ≡ 1, so S ≡ F + C gives
only their sum). Two independent residues cannot be forced by one unknown
without a quotient witness, so F and alpha (or F and C) are both
necessary for this compiler's interface. Nine positive unknowns at low
degree therefore need a compiler whose transport tests one word, which is a
change to the compiler proof (package 44, Sections 5–7), not to the
kernel.

## 3. The two directions that can give a significantly smaller equation

1. **A one-word transport.** Re-derive the native-window compiler so that
   the row-successor relation is tested on S alone. If that works, the
   present ten-positive kernel becomes a nine-positive equation at degree a
   few hundred, against 997,810 today. This is a compiler-level research
   task with an uncertain outcome.
2. **A checked direct quartic.** Wave 11's direct C222 quartics (108's 394
   naturals) rest on two Lean interfaces plus an ordinary proof of
   "polynomial zero iff C222 derivation". Formalizing that step for one
   small direct quartic would give the first fully checked Con(ZFC)
   equation. Lean work is paused in this project at the owner's request,
   so this waits for his decision.

Neither direction was started here.
