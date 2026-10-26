# Brief: a merged-source nine-positive equation for Con(ZFC)

Prepared 25 October 2026 for the research session in
`Computability/DiophantineConsistency/`, at Vladimir's request. It hands over
a design sketch that the intake session worked out on paper, but neither
built nor verified. Every figure below is an estimate. No circuit, builder
or proof accompanies this brief: deriving all three is the task.

## Goal

Vladimir's direction was a new low-radix source (for example a Jones-style
gap source) aimed at **nine positive unknowns at low degree**, rather than
more schedule edits on the ten-positive kernel.

Success means a complete nine-positive equation that dominates every current
nine-positive point on both operations and degree. A clear target is at
most about 420 operations at a degree below 10^5, with the standing ordinary
proof that ZFC proves "no positive solution" ↔ Con(ZFC).

## Baseline to beat

The [collection README](../../Computability/DiophantineConsistency/con-zfc-diophantine-forms/README.md),
row "Nine positive, Pareto frontier", gives these package points (degree /
operations):

| Point | Package |
|---|---|
| 1,472,168 / 420 | 101 |
| 1,376,378 / 456 | 105 |
| 1,158,228 / 726 | 82 |
| 997,810 / 1,057 | 101 |

The research session's own nine-positive points, 405 operations at degree
1,191,570 and 413 at 1,316,546 (`23d8510a10`), dominate the package row.
[PROPOSAL_REVIEW_LATEST.md](../../Computability/DiophantineConsistency/PROPOSAL_REVIEW_LATEST.md)
also lists a 475 / 1,379,730 option and the folded-saturation family.

Every one of these points sits at degree 10^6 or more. That is the gap the
design aims at.

## Design sketch (unverified)

The idea is to stop treating the native source and Jones's nine-unknown
reduction as two stages, and to merge the source into the reduction's
kernel.

1. **Outer kernel.** Keep the Jones nine-unknown kernel as the outer
   structure, with its base set to b := βJ + 1, where J is the kernel's
   coding variable and β the native radix parameter.
2. **Masks as digits.** Encode the native coefficient masks as base-T digit
   blocks at two of the kernel's coordinates (C and F). Their popcounts are
   to sum to dN + 2.
3. **Rotation and transport.** Use one rotation residual, b = (βv + 1)u, plus
   the existing transport.
4. **Inner layout.** Five coordinates and two residuals, with layout height
   14: weights C = 6, F = 2, t = 4, u = 0, v = 1, and targets 1 and 9.
5. **Scales.** N = 2^κ·B^15 and L = B^23, where B is the native base.

On paper this gave roughly **133 operations at degree about 15,000**. If it
holds, that is about a third of the operations and about 1/80 of the degree
of the best point now.

## What needs to be done

1. **Source and proof.** Write the merged source exactly, and prove each
   merge step sound and complete against the repository's Jones development
   (`Jones1982.Nine.wset_iff_nine` and its ratio lemmas) and the native
   calibration. Earlier nine-positive work shows the format:
   - [GAP_SOURCE_NINE66.md](../../Computability/DiophantineConsistency/GAP_SOURCE_NINE66.md),
     [GAP_NINE_POLYNOMIAL66.md](../../Computability/DiophantineConsistency/GAP_NINE_POLYNOMIAL66.md) and
     [GAP_NINE_RATIO66.md](../../Computability/DiophantineConsistency/GAP_NINE_RATIO66.md);
   - [NATIVE_NINE_POLYNOMIAL52.md](../../Computability/DiophantineConsistency/NATIVE_NINE_POLYNOMIAL52.md) and
     [SPLIT_NINE_POLYNOMIAL59.md](../../Computability/DiophantineConsistency/SPLIT_NINE_POLYNOMIAL59.md);
   - [COMPILER_JONES.md](../../Computability/DiophantineConsistency/COMPILER_JONES.md).
2. **Circuit and measurement.** Emit the literal circuit, then count live
   operations and measure the exact degree with the actual ports, as for the
   maintained pages.
3. **Coefficients.** Bind a coefficient tuple through the retained
   native/K215 calibration, preferably one of the session's small tuples.
4. **Review.** Run an independent review in the session's usual form.

## Known risks

- **Estimates only.** The 133-operation and degree-15,000 figures come from
  a paper count, not a circuit. The digit layout could need more room.
- **Carries.** The mask digit blocks must not carry into one another. The
  popcount condition (sum dN + 2) and the layout height 14 have to be proved
  sufficient, not assumed.
- **Kernel side conditions.** `Jones1982.Nine.wset_iff_nine`
  (`Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineMain.lean`)
  assumes 1 ≤ ν, a parent polynomial of total degree at most 4, and a
  normalized parent. The merged source must still meet all three, and the
  completeness direction must still produce positive witnesses.
- **Degree accounting.** The scales N and L dominate the degree. A larger
  B^k than estimated would move the degree by orders of magnitude.

## Provenance

The design was worked out by the intake session (Claude), at Vladimir's
direction, as a paper calculation. An earlier attempt to write a builder for
it in that session was stopped before completion. No code from it exists or
is supplied.
