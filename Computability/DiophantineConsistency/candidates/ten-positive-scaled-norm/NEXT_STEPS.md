# The current ten-positive degree budget and possible smaller encodings

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

The present proof uses the following degrees. These are a budget for the
existing construction, not lower bounds for every equivalent encoding:

- `mu = q^2 + 1` has degree 2. Its square exceeds the bound
  R + 1 < q^4 used to identify the first index. After q is proved even,
  it is coprime to q^3, q − 1 and H'. Replacing it by q + 1 loses that
  index bound; see the [carrier audit](../../research/compact-carrier-degree-audit/README.md).
  The product (q^2 + 1)(q^2 − q + 1) has degree 4, not degree 2, and
  is therefore not an alternative with the same degree budget. A smaller
  scaling would need a new index argument or a sharper source bound.
- `I = i c^2` (degree 5) is forced by the rank lemma (c^2 | I).
- `delta = Q − 1 = (Delta' I)^2 − 1` (degree 30) is the denominator of the
  auxiliary root y^2 = (Q V^2 − 1)/(Q − 1); it multiplies three of the four
  norm arguments.
- `Z0` (degree 25) is dominated by the transport term q^3 · mu^2 · H' · W · Bt,
  with W of degree 11. The current transport proof uses
  W = 1 + (q − 1)L and L = H'I + b: before transport divisibility is
  known, it needs L > 3 tau + f + b. Merely requiring W > f does not
  establish a lower bound of 11 on its degree. No smaller replacement
  satisfying all the required inequalities and congruences is proved here.
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

These calculations identify obstacles to the tested changes. They do not
prove a degree floor or exclude a better transport weight, carrier,
source compiler, or root encoding.

## 2. What the current compiler leaves unresolved at nine unknowns

The kernel spends seven unknowns on the Pell side (w, Y, i, T, eta, zeta,
n) and three on the source (J, F, alpha). Jones's nine-unknown layout
spends the same seven plus two source unknowns (b, g), which is how the
collection's nine-positive equations reach nine, at the price of the
H2082 gap source whose radix exponents give degrees near 10^6.

The compact44 source carries two base-q digits of the halting tableau,
F and C = q − F − alpha, inside one word S = qF + C with R = (q^2 − S)(q^2 − 1) + T_w.
The transport equation (K_0 + w) C ≡ F (mod q − 1) tests the two residues
F mod (q − 1) and C mod (q − 1) independently (q ≡ 1, so S ≡ F + C gives
only their sum). Simply replacing both words by S does not retain this
transport test. This observation is not an impossibility proof for a
one-word encoding: S already determines F and C when their digit bounds
hold, and a different arithmetic encoding might recover the required
information. No polynomial elimination preserving the existing proof and
reducing the unknown count is supplied here. Re-deriving a transport test
on S alone is one possible compiler-level direction (package 44,
Sections 5–7).

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
