# Bounded publication review: Polish arithmetic Parts XVI–XVII

Immutable publication `9a8894d0a0393b00513529ad1d6b3693a9674018`, parent
`9c7d03c7300699cafa1a63d78a5ae2d38f78f2b6`.

Three guide hypothesis corrections are required below. I found no defect in the
selected article theorem/proof interfaces: the article includes the hypotheses
omitted by those guide summaries. This is a bounded publication and mathematical
interface review, not certification of all new proofs or supplied diagnostics.
No finite ordinary-integer evaluator, paid integer circuit, or arithmetic cost
improvement follows from the interfaces reviewed here.

## Authentication and actual coverage

The host is
`Algebra/SurrealNumbers/docs/foundations-and-computation/polish-models-of-omnific-arithmetic/`.
The companion JSON pins both versions of all three changed files, exact Git
blobs, byte sizes, SHA-256 hashes, both full textual diffs, and every recorded
read span. Its snapshot is the publication commit, not later working edits.

| Immutable after-file | SHA-256 | Coverage |
|---|---|---|
| README.md | `86048d64e33601bfe43372b7db0e995ee91c7a19de12ed4680e32a2ddf1670b3` | All 608 lines of its diff read; 324 added / 43 removed lines |
| article.tex | `04b626e2c1e69c40a49b1c56beb25862bad24efdb64388cbea4a76a3a8428777` | Whole diff authenticated; selected 3,407 source lines read, not the whole 4,771-line diff |
| article.pdf | `f5b3f6a59527df9003a550ac219d082704f6a63a19eec7e124920063a542a18a` | Hash/bytes only; no build or visual/page-count validation |

The TeX diff adds 4,462 and removes 21 lines (the informal 4,483 figure counts
both). The exact selected after-source spans are 32418–32522, 32823–32840,
33013–33900, 33954–34372, 34427–34588, 34610–35833, 36045–36147,
36272–36728, and 37726–37756. These cover the new introductions, category and
flag/Hilbert chain, operators, relevant arithmetic boundaries, matrix/slice
summability and derivation chain, rank-one integration, positive-gain
exponential/logarithm, finite evaluation and effective questions, both new merge
sections, and the inherited KS interface. Exact hashes distinguish each span.

Fresh metadata checks authenticate both arrival ZIPs from immutable
`2faa3b37a1c7a1cf0d7080f8b5d2dfccc4dd3844`: all 17 regular members and all nine
ancillary placements. Every placement equals its archive member and is unchanged
in this publication. Both delivery READMEs were read completely. The 62 Hilbert
and 64 summability source labels all occur under `pma:hbo:` and `pma:bsd:`.
This is label/byte mapping, not full manuscript-body textual equivalence.

There are 1,344 distinct article labels, up from 1,156: all 188 additions are
new, no old label is removed, and none is duplicated. All 3,793 literal internal
reference occurrences recognized by the fresh parser resolve. The parser handles
optional cleveref label types and excludes external `replabel` references;
generated numbering, macro-generated references and rendered PDF links are not
certified. The delivery verification/build claims remain source claims; none of
their programs or recorded runs was replayed.

The existing `review_polish_thresholds_4af6f191d` concerned Parts XIII–XV, not
these two new Parts. The earlier `review_polish_borel_placement_5e4d8eed8` was a
nine-file byte-placement review and explicitly did not read body proofs. Neither
is silently promoted here. Their immutable pins are in the JSON.

## Retained corrections to the guide

The incoming standing rule, immutable `docs/incoming/README.md` 425–439, requires
wrong claims to remain on record with a numbered counterexample. The following
numbered review remarks preserve the original guide clauses. The corresponding
article statements are correctly scoped; no article correction or rebuild is
requested by these findings.

**Review Remark R1 — the zero derivation.** README 867–868 says:

> in rank one D = aE with kernel R and image `{g : ct(g/a) = 0}`

Article Corollary 231.3, 35771–35799, inserts **if `a != 0`** before the kernel
and image assertions. For the rank-one exponent group `Gamma=Z`, choose `a=0`.
Then `D=0`, its kernel is the entire Laurent field, its image is `{0}`, and
`g/a` is undefined. Thus the unqualified guide formula is false. Replace its
two lines by:

> (Theorem 231.1); in rank one D = aE, and for a ≠ 0 it has kernel R and image
> `{g : ct(g/a) = 0}` (Corollary 231.3); coefficient continuity is the

**Review Remark R2 — the zero ordinal.** README 834–838 describes the models
`M^{ell2}_theta` and concludes:

> additive omnific realizations, and no compatible discretely ordered ring

Article Theorem 220.2, 34321–34325, explicitly assumes `theta>0`. At `theta=0`,
`H_0={0}`, its lexicographic group is `Z`, and its nonnegative cone is `N`.
Ordinary multiplication is compatible with the specified addition, unit and
order. Replace the ending by:

> additive omnific realizations, and, for θ > 0, no compatible discretely
> ordered ring (Theorems 218.1, 218.3, 218.4, 219.1, 220.2).

**Review Remark R3 — nonzero spaces and the measure behind `L^p`.** README
832–834 says:

> a real Polish vector space with zero dual, such as `L^p`, 0 < p < 1, carries
> no Borel order

README 844–847 also says:

> no complete metrizable real vector space with zero dual, separable or not,
> carries a Baire-property order, and `L^p(μ)`, 0 < p < 1, has zero dual for
> every nonatomic μ

The no-order statements require a **nonzero** space, as Article 34001–34005 and
34654–34668 state. The zero vector space is Polish, has zero dual, and has the
unique total order with empty strict positive cone; that cone is Borel. The
unqualified `L^p` example also hides the measure hypothesis: for a one-point
space of mass one, `L^p` is `R` even when `0<p<1`, and the usual positive ray
defines a Borel additive order. The article's original corollary uses Lebesgue
`L^p([0,1])`; its generalization assumes nonatomic `mu` and `L^p(mu)!=0`.
The assertion that a nonatomic zero `L^p` has zero dual is itself true, but it
does not imply the no-order conclusion. Suggested replacements are:

> need not be Borel (Proposition 217.1); a nonzero real Polish vector space
> with zero dual, such as `L^p([0,1])`, 0 < p < 1, carries no Borel order
> (Theorem 217.2, Corollary 217.3).

and

> recursion and θ is the cone closure rank ρ (Proposition 224.1); no nonzero
> complete metrizable real vector space with zero dual, separable or not,
> carries a Baire-property order. For every nonatomic μ with `L^p(μ) ≠ 0`,
> `L^p(μ)`, 0 < p < 1, has zero dual and satisfies this obstruction
> (Proposition 224.2, proving 22's abstract);

Root was notified of all three corrections. This review preserves the wrong
unqualified clauses and their failure even if the current guide is repaired.

## Mathematical and computational boundary checked

The Hilbert classification is for translation-invariant orders whose cones
have the stipulated Borel/hereditary Baire regularity. The category argument
is applied to each closed-subspace trace; merely having the ambient Baire
property is insufficient, as the supplied `R^2` construction explicitly shows.
The canonical recursion terminates at a countable ordinal using second
countability, rather than assuming it ends at `omega`. Orthogonal complements
then produce the unique oriented basis. The selected convex-subgroup,
ordinal-embedding, oscillation and operator proofs are consistent with that
scope. The operator theorem starts with a bounded operator; a formal infinite
matrix with positive pivots alone is not enough. The supplied arithmetic lift
is Presburger addition on a real Hilbert carrier. Its omnific realization is
additive, uses transported topology, and supplies no multiplication or
ordinary-integer encoding. Effective flag extraction, uniform coding and
foundational strength remain questions. The 2012 Hilbert-order paper was not
read here; no priority comparison or finding about that external paper follows.

The summability theorem concerns **countable** subgroups of the real exponent
group, real coefficients, **left-finite** supports, and the specified coefficient
Borel structure. Its proof does not falsely apply Polish automatic continuity
to the whole field: it uses Polish coefficient slices, finite-coordinate
functionals, and a countable generic-noncancellation argument. Its column/cutoff
conditions yield valuation continuity and preservation of left-finite sums.
The derivation proof obtains a common lower bound by moving an arbitrary
exponent into one bounded interval using integer multiples of a fixed positive
group element; it does not assume the exponent group is divisible. Rank-one
integration is sound with the nonzero multiplier hypothesis in R1.

The finite evaluation formulas require supplied support/coefficient truncation
procedures and a gain/cutoff bound. Existence of a cutoff for a Borel map is not
an algorithm to extract it from an arbitrary Borel code. The text explicitly
leaves such extraction open. The generic Baire vector and Hamel/transcendence
bases are proof devices, not finite search routines. Even a finite sum of real
coefficients does not give an ordinary-integer circuit with a paid gate ledger.
No such ledger or fixed finite integer coding is supplied by these results.

The KS forward/inverse distinction is preserved. The inherited Part XV
substitution construction provides embeddings from forward-summable characters;
it does not make them automatically onto. Its rational example has
`t -> t+t^2`, while `t -> -1-t` fixes the image and moves `t`. That elementary
obstruction is independently clear from the printed formulas. New Remark
239.4 adds **uniform positive gain**, then proves an inverse by a convergent
Neumann series and supplies a logarithm. The exponential/logarithm proof uses
finite coefficient identities at each cutoff and the common positive gain;
it does not replace that hypothesis by individual positive gains or mere
forward summability. Its necessity is explicitly left open. The separate
Euler flow preserves supports coefficientwise but its Taylor series need not
converge in the valuation topology, a distinction the new proof also states.
The external KS preprint/journal text and the full infinite-rank counterexample
chain were not independently reread here; this is a local interface check, not
a new certification of the external-paper correction.

## Limits and execution record

Unselected proofs include much of coefficient-continuity classification, wild
derivation construction, and appendices; external classical foundations
(separation, category, quantifier elimination, surreal normal forms and measure
splitting) were not independently formalized. The older ATR0 claims remain
outside this review. The new Lean comparison is a narrowly identified Laurent
residue clause, not formalization of these classifications; its Lean file was
not checked in this turn. Selected proof reading does not certify every theorem
or every novelty claim in either manuscript.

Only fresh standard-library metadata code and inert Git/source/ZIP reads ran.
No supplied, archived, committed/frozen or copied predecessor program was run or
imported. No builder, PDF rendering, repository edit or Git mutation occurred.

Fresh metadata helper:
`review_polish_borel_9a8894d0a_metadata.py`, SHA-256
`80442f377634f0bbdb0fc2dc03fe2ff28bf76d38c059415e592e7af67a0ddf96`.
Receipt: `review_polish_borel_9a8894d0a.json`, SHA-256
`8369c3fe61d9dcbaff643beb32b76abacfdf0bba17548a5bc66e600bd91e2e16`.
The fresh audit completed with 3 changed files, 17 archive members, 9 exact
placements, 126 preserved source-label mappings, 1,344 unique article labels,
and no unresolved literal internal references in its stated parsing scope.
