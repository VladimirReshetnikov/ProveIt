# Cyclotomic correction review at 7389d7de4

The substantive correction and its explicit counterexample pass this bounded review. One minor displayed identity has a missing exponent; it does not invalidate the following domination argument. The general directional residue formula and the inverse claim remain conjectural. No ordinary-integer compiler or arithmetic-operation bound follows from this publication.

This review concerns immutable commit `7389d7de4cec2bf27f0c882e00f26ecc7acc5c83`, parent `9a8894d0a0393b00513529ad1d6b3693a9674018`, in the q-Pochhammer/q-binomial monograph under `Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/exponents-and-q-series/q_pochhammer_q_binomial_monograph/`. Later corrections are outside this immutable finding record.

## Read and authentication scope

All changed textual hunks were read: the README append, chapter07 changes, and three new bibliography entries in the master TeX. The commit changes four files: three text files with285 added and4 deleted lines, plus the PDF. The JSON authenticates every before/after Git blob, byte count, SHA-256, full-index raw diff hash, and hunk range. The PDF is authenticated only as bytes; I did not build it, inspect rendered pages, check fonts, or verify the reported build logs.

The principal exact text spans are:

| Immutable file | Before | After | Scope |
|---|---:|---:|---|
| README.md |732–734|732–766|Complete correction append and its reported evidence |
| chapters/07_certification_and_frontiers.tex |715–800|715–1014|Normalization, original/corrected conjecture, retention note, status, counterexample and entire new proof |
| q_pochhammer_q_binomial_monograph.tex |17392–17397|17392–17414|All added bibliography entries and context |
| Master TeX counter declarations |—|59–115|Shared theorem counter and numbered historical-note environment |

Every span has an inclusive line range and normalized UTF-8/LF span hash in the JSON. All three raw textual diffs were read in full; the table additionally records surrounding source reads. This is not a full rereview of the monograph or of unrelated earlier chapter claims.

The applicable `Analysis/FabiusFunction/AGENTS.md`, its local incoming-intake guide, and `docs/incoming/README.md` rule11 were read. The latter requires retaining wrong claims with explicit refutations and crediting unresolved claims with their gaps. The new historical note reproduces the original false directional sentence, labels it false, cites the source, and points to the numbered counterexample. The corrected general statement remains a conjecture and its missing contour/inverse obligations are explicit. No repository files were edited by this reviewer.

## Mathematical correction

The old assertion identified every pole-free convergent directional Borel sum with the same exact normalized function. Pole avoidance alone does not justify this: rotating between two pole-free rays may cross poles inside the intervening wedge. The displayed example with `m=1, a=e^{-1}` addresses that precise failure, rather than merely exhibiting a divergent integral or a ray through a pole.

I checked the self-contained argument against its normalization and the cited source section. The coth partial fraction gives the stated rational kernel after the singular and constant terms are removed. Its Borel transform is the normally convergent sum of the paired profiles `F(±iu_j)`, weighted by `-1/(4π²j²)`. The poles have nonzero imaginary part `2πj`, so different j cannot cancel a pole; the upper wedge between0 andπ/4 contains exactly the points `4π²jn+2πij`, j,n positive. Neither boundary ray contains one. The residue is `i/(2πj)`.

On the positive ray, the correctly weighted summands are dominated by the absolutely convergent product of the geometric a-series and the j-squared reciprocal series. Fubini then recovers the exact normalized function. On the diagonal, both profile rays avoid the denominator zeros; the profiles tend to0 and-1 at infinity and are bounded on their remaining compact portions. This gives an integrable, j-summable bound.

For each paired j-term, the vertical closing contour at `Re u=(2M+1)π` makes both profile arguments negative real and bounds their quotients by1. For positive real t the exponential decay dominates its linearly growing length. The counterclockwise orientation gives the minus-residue sign printed in the source, hence the positive coefficient1/j in the jump. Summing the absolutely convergent residues gives the stated dual-product logarithm. At t=1/N every phase is1, so the jump is positive. For sufficiently small positive t, the j=n=1 contribution dominates the O(Q²) remainder and the jump cannot vanish. These steps establish the claimed counterexample without relying on the reported mpmath experiment.

The new status paragraph correctly separates the fixed compact-parameter regime from a moving parameter `a=q^alpha` approaching the boundary. For fixed `|a|<1`, the cited Borel section supplies the explicit pole set, uniform Gevrey remainder bound and positive-ray identity. Its finite set of residue-class profiles also justifies convergence on each fixed admissible ray. General contour-rotation estimates and the parameter-dependent resurgent inverse are nevertheless left open in the publication; this review does not upgrade those claims.

For the moving real parameter `0<alpha<1`, the two cited completion statements have the same normalization and lateral orientation as the editorial summary: an upper/lower lateral sum needs the corresponding opposite-sign phase dual product. The selected kernel statements allow only the real-axis pole locations, with removable poles when their residues vanish. At alpha=1/2 all these sine residues vanish but `log(-Q;Q)_infinity` is nonzero for0<Q<1. Thus the distinction between a jump and the extra exact completion is meaningful. I checked those statements, definitions and kernel passages, **not the entire Mellin completion proofs** or the cited external literature.

## Finding CYCL-1: a missing exponent in the positive-ray bound

At immutable chapter07 line958, the source prints

```
|a exp(r xi/omega_j)| = a^r.
```

With `a=e^{-1}`, real xi and purely imaginary omega_j, the left side is a. Taking xi=0 and r=2 already contradicts the printed equality. The intended expression is

```
|a^r exp(r xi/omega_j)| = a^r.
```

Line959 uses `a^r` correctly in the actual double series. This is a local transcription error, not a defect in the counterexample or its Fubini justification. The immutable incorrect line is retained in this review with the concrete counterexample. Root was notified and owns any later source correction and rebuild.

## Provenance, labels and limits

The primary source is `docs/incoming/complex_transseries_q_cusps (2).zip`, at arrival `516049bf9` and at the reviewed commit. Its bytes are identical at both revisions:639,854 bytes, SHA-256 `c82002e6672c463a71d415a025a8b1245f49af3ea211c12bc5273c5beaf4f87d`. I read its entire497-line member `complex_transseries_q_cusps/sections/03_borel.tex`, including the general Borel transform, bounds, concrete counterexample, and inverse limitations. The corrected monograph gives an adapted self-contained proof; byte-identical body transfer is not claimed.

The additional selected archival reads are:

| Archive/member | Exact lines | Coverage |
|---|---:|---|
| `critical_stokes_q_reversion.zip` / `critical_stokes_q_reversion/critical_stokes_q_reversion.tex` |500–716|Moving-product definition and normalization; Borel kernel and its bounds; exact lateral-completion statement; not its whole proof |
| `transseries_q_stokes_reversion.zip` / `stokes_q_reversion/article.tex` |114–342|Scope, conventions, normalizations, Borel-kernel passages and exact-completion statement; not its whole proof |

The JSON pins all three archive blobs and the three selected member bytes/read spans. Other archive members were not mathematically reviewed or comprehensively inventoried. The destination named in the bibliography has no files in the reviewed commit; the README explicitly describes the source as being filed, and the unchanged incoming archive supplies the immutable provenance. This is a placement-status observation, not a claim that the source was absent or that its proof was unavailable.

The chapter label count changes27→30. Every old label remains in the same order, including `conj:cyclotomic-resurgent-inverse`; the additions are the counterexample remark and its two equations. The master TeX's old label sequence is unchanged, and all three new citation keys have unique bibliography entries. These are source-level checks; no claim is made to have reproduced rendered numbering, page totals, validator output, the45-digit quadrature, font inspection or builds.

The mathematical content concerns complex analytic functions, infinite Borel/Laplace representations, convergent residue sums and sectorial asymptotics. It supplies neither a fixed-arity existential integer encoding nor an emitted integer straight-line program whose additions and multiplications are fully counted. In particular, exact exponentially small completion data cannot simply be discarded because two functions share an all-orders expansion. This correction changes an analytic identification claim; it does not change the existing Diophantine compiler bounds.

Only the fresh metadata collector `review_cyclotomic_7389d7de4.py` was executed. No supplied, archived, committed, frozen or copied predecessor program, numerical experiment, validator, Lean/Lake command, TeX builder or makeindex invocation ran. The companion JSON is the exact authentication/read-scope record.
