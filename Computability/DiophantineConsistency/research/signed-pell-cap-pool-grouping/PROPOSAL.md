# Partial sums for the accepted signed-cap quartic

An exact post-chart extension is worth checking next: split the pooled index
row into five groups and the frame row into two groups, using five fresh
unrestricted integers. Inert collection over the fixed accepted centered
359-coordinate chart gives 364 declared coordinates, 227 residuals, degree4,
4574 monomials and height128446. This is a prospective fixed-chart calculation,
not an accepted new projected endpoint. No compiler, optimizer, factorizer,
source generator, centering search, incoming program or Lean was executed.
The only executed new file reads frozen JSON and performs ordinary sparse
integer arithmetic. Full source materialization and independent coefficient,
inverse and closure checks remain separate work.

The old359 chart remains the alternative with fewer coordinates. The proposed
extension has fewer declared coordinates, residuals and monomials than the
separately accepted centered433 chart (433/287/4606), at the same height.
These comparisons do not assert that a subsequent optimizer will retain the
new coordinates, or that any recorded layout is globally best.

## 1. Universal extension theorem and exact source maps

Let Q(x)=sum_i r_i(x)^2 be any integer sum-of-squares equation with quadratic
residuals. Suppose one old residual is exactly

    r(x)=G_0(x)+...+G_(m-1)(x)+H(x),

where all displayed polynomials have integral coefficients and degree<=2.
Introduce unrestricted integers S_0,...,S_(m-2), with no sign graphs, and use

    D_j=S_j-G_j(x),                 j=0,...,m-2,
    P=S_0+...+S_(m-2)+G_(m-1)(x)+H(x).

Keep every other residual. Universally, on every integer assignment,

    P-sum_j D_j=r.                                      (1)

At an old zero, the unique extension is S_j=G_j(x), and all new residuals
vanish. At a new zero, every residual vanishes because it is an integer
sum of squares, and (1) recovers the old zero. Forgetting the new integers
and adjoining their defining values are inverse maps between zero sets.
Every old coordinate, including all old private witnesses, is fixed.
No positivity, boundedness or power semantics is needed for this theorem.

The polynomial changes. Writing Q_new for the new sum of squares,

    Q_new-Q_old
      =2P sum_j D_j-2 sum_(j<k) D_j D_k.                 (2)

This is an exact polynomial identity; Q_new=Q_old is not asserted. Splitting
another residual independently adds another term of the same form to (2).
All new residuals remain quadratic and the new equation remains quartic.

## 2. The complete literal error list

In the frozen402-coordinate body, pool row219 is

    sum_(j=0..15) e_j^2-(v246-1)*v395,

with the following actual affine errors. The final entry is the cap error.

| j | e_j in the literal body |
|---:|---|
| 0 | v258-v0-16 |
| 1 | v267-2v25 |
| 2 | v281-v0-v4-16 |
| 3 | v296-v16-1 |
| 4 | v310-v17-1 |
| 5 | v316-v18-1 |
| 6 | v322-v19-1 |
| 7 | v328-v20-1 |
| 8 | v334-v2-1 |
| 9 | v340-v21-1 |
| 10 | v346-v22-1 |
| 11 | v352-v1-1 |
| 12 | v358-v23-1 |
| 13 | v364-v24-1 |
| 14 | v370-v171-1 |
| 15 | v387-v245 |

The inert audit matches every coefficient of this expression to row219, to
the unchanged Horn pool row217, and, after applying only the147 published
substitutions and retained-coordinate map, to projected row130. It then
applies each already-published translation and matches the corresponding
complete old row and every coefficient of the old whole quartic. It imports
none of the programs that produced those files.

In the fixed centered359-coordinate chart write x for its coordinates.
The same errors become

    e0=x169-x0,
    e1=x174-2(x0+x1+x2+x3),
    e2=x181-x0-x4,
    e3=x188-x10, e4=x194-x11, e5=x198-x12,
    e6=x202-x13, e7=x206-x14, e8=x210-x2,
    e9=x214-x15, e10=x218-x16, e11=x222-x1,
    e12=x226-x17, e13=x230-x18, e14=x234-x105,
    e15=x239-x157.

Here old pool row130 is exactly sum e_j^2-x158*x247. The disappearance
of its linear quotient term uses the accepted shift of coordinate158 by1;
it is checked from the actual translation certificate, not presumed.

## 3. The specified five-pool/two-frame extension

Use these five disjoint error groups, in this order:

    I0={2,0,3}, I1={4,5,6,7}, I2={8,9,10,11},
    I3={12,13,14,15}, I4={1}.

Set G_j=sum_(i in Ij) e_i^2. Introduce x359,...,x362 and replace old
row130 by the consumer

    P=x359+x360+x361+x362+G4-x158*x247.

Append definitions D_j=x_(359+j)-G_j, j=0..3. Universally,

    P-D0-D1-D2-D3 = old row130.                         (3)

For the frame use the actual centered row186, label
`shared.frame_definition`. Sort its47 nonzero monomials by their coordinate
tuple, with the constant tuple first; rotate this list left by one position;
take the first24 terms as L and the remaining23 as R. Thus L starts at the
term8*x0 and ends at -2*x16^2. The constant -16 belongs to R. All literal
coefficients and both complete term lists are in STATIC.json under
`charts.centered.five_pool_two_frame_finite_layout_comparison`.
They satisfy L+R=old row186 coefficient-for-coefficient.

Introduce x363. Replace row186 by U=x363+R and append D4=x363-L. Then

    U-D4 = old row186.                                 (4)

One complete residual ordering is unambiguous: retain the old222 positions,
replace only positions130 and186 by P and U, then append D0,...,D4 at
positions222,...,226. Old coordinates0,...,358 keep their exact meanings.
At an old zero append (G0,G1,G2,G3,L); conversely forget coordinates359..363.
Equations(3),(4) reconstruct every changed old row; every other old row is
identical. The full SOS difference is (2) for D0..D3, plus2*U*D4.

The new integers do not join the old frame's semantic atom list, any old
sign graph, power port or semantic front. Only their new definitions and
the two replacement rows refer to them. The old359 endpoint's
complete inverse translations, published monic restorations, handling of
its two free factored coordinates and Horn reconstruction still apply after
the new integers are forgotten. Ordinary soundness and positive source
completeness therefore require no change to the cap proof or native compiler.
The proposed materializer must retain those existing inverse maps in full.

## 4. Finite coefficient comparisons and their limits

The following are exact inert calculations over the fixed centered chart.
Only these declared extension rows are added; no subsequent projection or
centering is performed. Height is128446 throughout.

| Pool groups | Pool only: terms | With2 frame chunks: terms |
|---:|---:|---:|
| 2 | 5451 | 4996 |
| 3 | 5237 | 4780 |
| 4 | 5108 | 4642 |
| 5 | 5055 | 4584 |
| 6 | 5034 | 4563 |
| 8 | 5032 | 4559 |
| 16 | 5188 | 4714 |

This table uses a simple unrotated23/24 frame cut. The specified five-group
proposal instead uses the24/23 rotated cut in section3, giving4574 terms.
It was the best of658 explicitly enumerated cuts of the rotated sorted
term list with both supports>16, for this chosen pool partition. No other
layout family is covered by that statement. Three/four frame chunks also
have their exact comparisons recorded, but possess short definitions.

The centered maximum coefficient128446 occurs at x10^2*x11*x12. Both the old
pool square and old frame square contribute zero to it. None of their
partitioned replacements contributes to it either, so this fixed-chart
extension cannot lower the height. The whole collected prospective
polynomial, rather than only that observation, verifies the stated height.

## 5. Projection support is a separate issue

The two/three initial pool partitions and all further fixed partitions are
recorded with complete raw, projected and translated group term sets.
Along the published147 substitutions, the five-group definitions have
minimum supports18,21,21,19. Its K-only consumer initially gives a short
restoration with support8; the existing affine definition
v25=18+v0+v1+v2+v3 raises its consumer support to26. The reviewed optimizer
prioritizes affine restorations before quadratic ones. This is useful
evidence for a future pre-centering route, not a certificate of a new run.

After the accepted centering the four definitions have supports11,12,12,12,
and a fresh support16 optimizer could eliminate them. Six/eight/sixteen
pool groups have additional short definitions already before centering.
For the proposed POST-CENTERED extension none of these restorations is
executed: the partial sums are deliberately retained. The single frame
definition and its consumer restorations have supports24 and23. These
facts do not imply a projected coordinate count for any new optimizer.

STATIC_AUDIT.py is standard-library-only and refuses a different existing
output. Its normal and optimized records bind all read input bytes, itself,
all exact group/changed-row term sets, full old quartic checks, the finite
layout family and hashes of the complete prospective coefficient vectors.
SOURCE_PINS.json binds the accepted endpoint/source manifests and this
ordinary static packet. No accepted input or frozen packet was changed.
