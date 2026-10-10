# Proposed integration into ProveIt

Baseline: `fc4d3bf80534ad7c901d3b8c9e71baf2df0064ed`, 10 October 2026.
This package changes no repository files. The following is a concrete proposed
merge plan for the supplied mathematical additions.

## Placement and dependencies

| Article material | Suggested manuscript location | Main prerequisite |
| --- | --- | --- |
| Mellin–Lerch master and integer resonances | Integration chapter or a linked new chapter | Polylogarithm order ladder, beta/Fermi integrals |
| Gamma/Stieltjes jets and anchored primitives | Integration/differentiation chapter | Mellin master and standard Hurwitz derivatives |
| Shifted harmonic reflection | Gaussian harmonic-sum chapter | Mellin master; distinguish generalized from elementary-symmetric harmonic numbers |
| Dilation and unequal-grid products | Canonical periodic Stieltjes calculus | Distributional finite parts and the undilated Hurwitz kernel |
| Research status and questions | Research chapter / discovery status index | Preserve theorem, conjecture, and rejection labels |

The single generated `manuscript-addition.tex` contains Sections 1–6 with the
known undilated coefficient mechanism included at its correct position.
It has no document class or bibliography environment. Its comments list the
standard packages and notation macros required from the standalone preamble.
Use its `mld:` labels unchanged or perform a consistent mechanical rename.
Merge the twelve bibliography entries from `references.tex` into the canonical
bibliography, resolving keys rather than creating a nested bibliography.

The standalone article has been compiled. The fragment has not been compiled
inside the full canonical manuscript; theorem counters and global macro choices
should be reconciled during that build. This is mathematical research source,
not a claim of a fully tested canonical-manuscript patch.

## Incoming questions answered

The following archive-member line locations refer to the exact retrieved bytes;
they are provenance pointers, not stable identifiers after a merge.

1. **Bilinear Closure**, `article.tex`, lines 1247–1254: unequal positive integer
   dilations. The new all-index formula treats every disjoint pair of singular
   grids and every argument derivative. Collision is still a separate question.
2. **Shifted Hurwitz Jets**, `sections.tex`, lines 782–783: dilation, traces,
   canonical extension, differentiation, and local scale. The new coefficient
   polynomials `c_{n,r}` and `b_{r,n}` supply the exact conversion and commutator.
3. **Convolution Calculus**, `Stieltjes_Convolution_Calculus.tex`, lines 1705–1712:
   positive integer linear coverings. The separate nonlinear-coordinate problem
   remains open and is formulated as Q3 in the article.

## Stale open questions to reconcile

The Closure report's questions on undilated parameter differentiation
(`article.tex`, 1256–1261) and associative convolution (1271–1277) are already
answered by the current Shifted Hurwitz and Convolution deliveries. Point to
those results rather than keeping these entries open across the combined set.
The present article restates the known undilated closure for self-containment;
that block can become a cross-reference once a canonical version is chosen.

## Mathematical normalization requirements

- `FP_x` removes divergent terms in the unscaled ambient local coordinate
  `x-x0` and adds no finite point-supported term.
- A separate constant term in each ambient cutoff gives the same convention.
  Setting cutoffs equal to different constant multiples of one variable and
  extracting a single constant term generally changes it.
- True distributional pullback transports the original extension. It differs
  from `FP_x` by the proved grid-supported polynomial correction.
- The unequal grids are disjoint exactly when `(p/gcd(p,q))*a` is not an integer.
- Derivatives inside the product act on the special-function argument. The
  distribution calculus supplies derivatives of the fractional-part profiles.
- A common dilation preserves the ordinary spectral product integral but
  changes its ambient-coordinate finite part. Retain `log(lcm(p,q))`.
- At Mellin/spectral resonances, evaluate complete analytic germs before
  replacing any vanishing factor or singular zeta value by a number.

## Conjecture and error status

The `S4` proof already exists. `S6` and the current `S8` candidate remain
conjectures; the present harmonic reflection has no coefficient in their
parity. Do not present the already-proved equivalence of two `S6` coordinate
baskets as a proof of the conjecture. Do not confuse the present `S8` vector
with the earlier rigorously rejected vector.

No new false theorem was found in the selected pinned correlation and Gaussian
claims. The audit's concrete corrections concern reconciliation, explicit
normalization of the extension, and retention of existing distinctions.
See `GAUSSIAN_STATUS.md`, `INCOMING_AUDIT.md`, `MELLIN_AUDIT.md`, and
`JETS_AUDIT.md` for the individual analytic and source audits.
