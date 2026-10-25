# Where the nine-positive degree comes from, and what a low-degree source needs

A research note for the route Vladimir chose on 25 October 2026: a new
low-radix ("gap") source aimed at nine positive unknowns at low degree.
No equation, proof or improvement is claimed here. The note measures the
present degree budget and ranks the levers by what they can buy.

## 1. The degree chain is a fixed amplifier of the source degree

The best nine-positive equations are the research session's 405 / 1,191,570
(original31 tuple) and 413 / 1,316,546 (compact54 tuple), in
`research/nine-folded-shared-odd-rank/`. Their recorded register degrees
(`boundary_simple.json`, `named_degrees`) are:

| Register | Degree | Ratio |
|---|---:|---|
| source rank R | 7,931 | 1 |
| A = M(U + 1) | 16,357 | ≈ 2R + 4·deg N |
| F | 146,726 | ≈ 9A |
| I | 635,480 | |
| output | 1,191,570 | ≈ 150 R |

The outer Jones/Pell kernel multiplies the source degree by about 150, for any
source of this shape. The ten-positive kernels show the same factor (about 70
over deg A). **So a low-degree nine-positive equation needs a low-degree source
rank R**, not a better outer kernel.

## 2. The source degree is the layout height

The source (package 101, `nine/report_section.tex`) codes the coordinates p of a
fixed positive quadratic system P0 into one word g = Σ (pᵢ − 1)·B^{wᵢ} in radix
B = 2^κ·b², with fixed kernels K₀, K₁, K₂ chosen so that the coefficient at each
target position q_j of Σ_d K_d·U^d equals 2ρ_j(p). Every radix exponent is
fixed by the layout: W = max wᵢ = 115, H = max(deg K_d + dW) = 1,866, and
L = 2b·B^1983 with 1983 ≈ H + W + 2. Hence

    deg R ≈ 4(H + W) ≈ 7,931,   output degree ≈ 600 (H + W).

The system P0 is gapN86 (`con-zfc-diophantine-forms/66-gap-congruence/source/`):
31 coordinates, 22 quadratic residuals, 86 coefficient records. Each quadratic
record places a kernel term at q_j − w(S); convolved with all pair sums of the
weights, it reaches a band about 2W wide, which other targets must avoid. So H
grows roughly like (number of residuals) × W, and W like the number of
coordinates, subject to uniqueness of every used pair sum.

## 3. Levers, ranked

1. **Modernize P0 (small).** gapN86 still carries a main Pell norm
   (rows 9 and 12, coordinates D and γ) for the gadget X = 2^R. The
   ten-positive kernels use the integrality of κ = Kpos/H instead, which as a
   quadratic row is (4a + 3)κ = X(3c − 2X) + 2, with c's Pell property
   recovered by all-index folding from rows 17, 19 and 22 that gapN86 already
   has. That saves one coordinate, one row and three records. The other rows
   (q², q³, the first norm, the strong and auxiliary Pell, transport and
   index) are already as tight as this architecture allows. Estimated gain:
   about 10% of H in total, with a new layout. Real, but not significant.
2. **Better layouts (unknown, probably small).** The published layouts come
   from the research session's searches; narrower 106-label experiments were
   worse. A lower bound on H for a given P0 would settle this.
3. **Merge the inner and outer kernels (large, open).** P0 is itself a Pell
   kernel. It turns the native exponential conditions (q = B^N, X = 2^R and
   the bit masks) into polynomials, and the outer Jones coding then supplies
   its own exponentials and masking. The outer machinery already forces b to
   be a power of two, and its test S∧T = 0 is bitwise on whole radix-B digits.
   So the native mask tests (C − 1)∧(MC·J + 1) = 0 and F∧(MF·J − 1) = 0 could
   sit directly in matching digits of S and T, where each digit holds a whole
   native word. And q = B^N could be tied to b. What has no replacement yet is
   X = 2^R with R about q⁴, which still needs a Pell exponential. If it can be
   supplied once, P0 shrinks to the native polynomial relations (transport,
   rank) and H could drop several-fold. That would also cut the degree
   several-fold. This needs a new version of the Jones nine-unknown theorem
   that accepts masked native words, with a full soundness and completeness
   proof.

## 4. Status

Nothing here has been built or checked beyond reading the cited artifacts and
their recorded degrees. Lever 3 is the only one that could give a
significantly lower nine-positive degree. Its first concrete step is to state
the merged source theorem: which native relations become outer digit tests,
and where the single remaining exponential X = 2^R is produced.
