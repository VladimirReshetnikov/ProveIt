# Proposed editorial changes to Chapter 4

These are proposals, not changes already applied to the repository.

Source: `Analysis/Polylogarithms/docs/manuscript/chapters/04-depth.tex` at
commit `29d9344771b41df39ff9b7890c76b1f152572dde`, blob
`6171912ff7724784cabb789a066c61223ab298bc`. Locate targets by their text or
labels; line numbers can change after integration.

## 1. Upgrade only the three displayed weight-four triple candidates

Target: the three formulas for `Im Li_(2,1,1)(i,1,1)`,
`Im Li_(1,2,1)(i,1,1)` and `Im Li_(1,1,2)(i,1,1)` immediately after the
weight-six double formulas labelled `gauss:eq:g51` through `gauss:eq:g15`.

The formulas themselves require **no coefficient correction**. Theorem 5.1
of the companion article proves all three, including their branch
conventions. The stronger complex formulas and the general one-zero
family are proved earlier in that article.

Add before those three formulas:

> The three weight-four triple identities below are exact. They are
> specializations of the one-zero classical reduction proved in the
> complementary-depth companion article. This proof upgrade applies to
> these three displays; it does not by itself upgrade the other numerical
> identities collected in this section.

Add the compact insert in `complementary-depth-insert.tex` at a suitable
point after the triple display, or move its longer structural statements
into a new subsection.

Do not delete the general warning about candidates whose proofs or
underlying scripts remain unavailable. In particular, this contribution
does not prove `gauss:eq:S4-closed` or `gauss:eq:wt5-sporadic`.

## 2. Correct the involution at mixed Gaussian points

Target: the paragraph immediately after the remark following
`double:eq:g-diag`, beginning:

> The consequence is structural: all depth-2 content of the Gaussian
> doubles lives in the antisymmetric parts Li_(a,b)(P)-Li_(b,a)(P), which
> vanish on the diagonal.

Replace it with:

> The stuffle involution swaps both the indices and the colors. Thus the
> complementary combinations are
> Li_(a,b)(x,y)-Li_(b,a)(y,x). For equal colors, this reduces to index
> antisymmetry and vanishes when a=b. At mixed points it need not vanish
> even when the indices agree. For example,
> Li_(1,1)(i,-1)-Li_(1,1)(-1,i)
> = pi^2/24-log(2)^2/4+i*(Catalan-pi*log(2)/2), which is nonzero.
> The symmetric stuffle combinations reduce to products of singles,
> but this fact alone does not eliminate the mixed-color diagonal
> antisymmetric combinations.

The nonvanishing is proved without relying on a numerical approximation:
the real part is greater than 1/8. The original symmetric stuffle
identities are correct and should be retained.

This local correction does not by itself validate or invalidate any
reported rank matrix elsewhere in the chapter; those matrices must be
checked under their own column conventions.

## 3. Explain, without overinterpreting, the weight-six triple rank

Target: “Triple sums and the scope of formal quotient dimensions.”

The all-weight formal theorem supplies a precise setting for the reported
rank seven on ten triple coordinates. In the shuffle algebra of binary
words ending in 1, modulo products of positive-weight words, the
weight-w/depth-d dimension is

    (1/w) * sum_{k | gcd(w,d)} mobius(k) * binomial(w/k,d/k).

The ambient coordinate count is binomial(w-1,d-1). At (w,d)=(6,3) the
indecomposable dimension is three and product rank seven. The Lyndon
representatives are (4,1,1), (3,2,1), and (3,1,2), agreeing with the
reported representatives. A new explicit 7-by-10 matrix is supplied;
we do not claim to have recovered the original thirteen rows.

Retain the manuscript's warning that these are formal dimensions, not
independence of evaluated real or imaginary parts and not a theorem
about numerical minimal depth. The transformed half-point argument
also enlarges the comparison algebra.

## 4. Retain the S4 problem, with a reproducible restricted obstruction

The S4 identity stays unresolved here. The finite matrix in
`certificates/s4_rowspace_obstruction.json` contains 134 rows on 23
imaginary-coordinate columns. Its rank is 19 and rises to 20 after the
target row is adjoined. The supplied dual vector n satisfies A*n=0 and
v*n=24 exactly.

This certifies that the target cannot be obtained from this explicitly
specified collection of homogeneous depth-two rows. It does not disprove
the proposed period identity, does not establish completeness of
cyclotomic double shuffle, and does not imply any new transcendence or
independence theorem. Higher-depth laws and other argument transformations
remain concrete next steps.

## 5. Cross-reference the discovery chapter and source inventory

In the discovery chapter's surviving research programme, add the
three now-proved triple identities and the all-weight one-zero family to
the list of results with analytic proofs. Keep the remaining root-of-unity
basket and independence questions open.

Add this package to the repository's source inventory after review, with
its new file hashes. Do not reuse the old manuscript blob hash for the
new contribution. The package has its own provenance and manifest.
