# Series and transseries

This group holds two documents: the canonical volume, and the companion
volume on combinatorial transseries consolidated from the three arrivals of
2026-09-04 (see the end of this file). Beside them are fifty-five unmerged
arrivals, fifty of 2026-09-29, one of 2026-09-30, one of 2026-10-01 and
three of 2026-10-02, each filed whole with its PDF, the first fifty-two
then amended editorially (see "Arrivals of 2026-09-29 to 2026-10-02"
below).

The transseries Lean inventory and zero-gap result are computed by
`Analysis/FabiusFunction/scripts/doc_audit.py --root
Analysis/Transseries/Lean/Transseries` and pinned in
[`../doc_audit_baseline.json`](../doc_audit_baseline.json). The 970/12,051 and
967/12,001 inventories are historical joint Fabius/transseries checkpoints.
The generic modules now use `Transseries.Transseries*` import paths. The
Fabius-specific Wright omega bridge retains its `FabiusFunction` import path.
The flatness module now includes both its vector-valued API and the scalar
submodule, absorption, and inverse-power-scale interfaces (4 definitions and
22 theorems). The differential-block module contains one definition and 20
theorems.

The new Bell derivation-tower and ordinary-Bell normalization results have
exact source counterparts. The Touchard definitions and coefficient identities
are also formalized. The arbitrary-power coefficient recurrence is now exact
through a generic commutative-ring differential equation and a unit-series
rational-algebra instance. The displayed Touchard Euler-operator equation is
exact as well. The wider Wright-omega, differential-closure, harmonic,
Cayley, derangement, Lambert-correction, core-inversion, remainder-transport,
and staircase statements still have the qualifications recorded in the source;
the least-term-index lemmas are supporting results, not a complete
optimal-truncation theorem.

> [`Transseries_And_Inversion/`](Transseries_And_Inversion) —
> *Transseries: the polynomial–logarithmic calculus, series reversal at
> infinity, and the inversion of rapidly growing functions*. The local
> 704-page and incoming 711-page A4 PDFs are historical publication
> checkpoints. The incoming branch later reached 55,985 source lines and 3,125
> distinct labels, and the merged canonical source is newer still. The moved
> source was rebuilt in three `pdflatex` passes as a 720-page A4 PDF, with no
> undefined references and 110 overfull-box warnings. Its title and provenance
> pages were visually checked. No current source-size or label-count claim is made.

## What was merged

Forty-two independently written articles, filed between 1 and 3 September
2026, in five groups. Thirty of them had already been consolidated once, into
two volumes; those two and the remaining twelve articles are now a single
volume, and all five source directories have been deleted. Git history is the
archive, and the volume's provenance appendix lists every source with the part
that absorbed it.

| Group | Articles | Absorbed as |
| --- | --- | --- |
| `transseries-tutorials/` | 4 | Part I, Orientation |
| `polynomial-logarithmic-transseries/` | 6 | the calculus parts |
| `special-function-inversion/` | 24 | the inversion parts |
| `lambert-inverse-transseries/` | 3 | reversing `x + W(x)` |
| `sequence-transseries/` | 5 | the Bell and Fubini chapters |

## The comparison this group had left open

The previous version of this README recorded, as explicitly unmade, the
comparison between the polynomial–logarithmic calculus and the inversion
calculi that the special-function and Lambert-inverse articles each extract.
The merge makes it, and the volume's concordance chapter states it pair by
pair.

The result is **less overlap than a title-level comparison suggests**. Of six
apparent overlaps, one is a genuine duplicate (the exponential partial Bell
polynomials, the same definition in two notations), one is a strengthening in
the inversion apparatus's favour (a two-sided residual bracket with a
root-existence certificate, now machine-checked as
`Fabius.exists_eq_in_residual_interval`, against a one-sided mean-value bound),
one item has no counterpart at all (the ordinary Bell family), and three are
different theorems about the same subject — most notably the two results both called
Lagrange–Bürmann, which are the near-identity *operator* form and the classical
*coefficient* form, neither implying the other without a genuine argument.

Shared vocabulary turned out to be a weak signal, and an intermediate stage of
this merge was misled by it; the volume records the correction rather than
quietly fixing it.

The source also carries a statement-level Lean crosswalk for the abstract
asymptotic-scale and Poincaré-expansion core, flatness and invisible functions,
the Hahn-series order foundations, polynomial--logarithmic height estimates,
Wright omega, differential-block integration, staircase inversion, and
residual/error transport. These scoped matches do not turn unrelated human
proofs or frontier statements into Lean results.

What the inversion apparatus genuinely adds over the calculus is the
exponential–power model and its axiomatized dominant core, the monomial
α-reduction, perturbed inversion around an exactly invertible core, the
two-sided backward-error certificate, and — with no analogue anywhere in the
calculus — the theory of inverting a **sequence**: three distinct inverse
objects, the staircase theorem, and the separation condition under which an
asymptotic inverse determines an integer one. The calculus is a theory of
functions on a scale; that last group is about the passage to a sequence.

## Lean crosswalk

The current corpus census and zero-gap result are maintained by
`scripts/doc_audit.py` and `docs/doc_audit_baseline.json`. Thirty-five
focused modules contain 304 explicit public commands; two named declarations
generated by `to_additive` bring that inventory to 306 named entries. Fourteen
of the first fifteen incoming leaves are directly relevant here; the later
Stirling, Wright-omega two-orders, and unit-series power leaves are also focused.
`TransseriesWellBased.lean` contributes seven written declarations plus its two
generated additive twins, and `WrightOmega.lean` contributes one definition
and thirteen theorems. `TransseriesMonomialUniqueness.lean` now has four
theorems, adding `tendsto_const_mul_plMonomial_div_one_iff` and
`isEquivalent_const_mul_plMonomial_iff` to its two compatibility wrappers.
The new `TransseriesWrightOmegaTerms.lean` leaf has ten theorems:
`plMonomial_one_zero_eventuallyEq`, `plMonomial_zero_one_eventuallyEq`,
`plMonomial_neg_one_one_eventuallyEq`, `exponents_of_wrightOmega`,
`exponents_of_wrightOmega_sub`, `exponents_of_wrightOmega_residual`,
`not_pure_of_wrightOmega_three_terms`,
`not_isEquivalent_pure_power_wrightOmega_sub`,
`tendsto_wrightOmega_div_plMonomial_zero_atTop`, and
`isLittleO_wrightOmega_residual_plMonomial_zero`. They now crosswalk the
following parts of this volume:

- Exact: the sequence-scale/Poincaré definitions, coefficient limits and
  uniqueness; flatness and the invisible-function proposition; Dickson's
  lemma; Neumann's lemma through literal `OrderDual` wrappers (the manuscript's
  total order is a specialization); the analytic power–log dominance
  trichotomy; the logarithmic block-class equivalence;
  `plt:prop:mot-omega-basic` over the reals only; the unique first three
  Wright-omega monomial terms and the real-`atTop` content of
  `plt:cor:mot-both-generators-needed` and
  `plt:prop:mot-one-generator-fails`; the abstract Bell derivation
  recurrence; the
  ordinary/exponential partial-Bell normalization; `p0:lem:bell-conversion`,
  `p0:lem:power-log`, and `p0:cor:exp-log-jets`; the integer block derivative
  equations `plt:eq:mot-block-derivative` and `plt:eq:dif-block` for a unit
  power generator; and `p6:prop:quadratic-core-catalan`.
- Partial with an explicit boundary: the two displayed height estimates are
  exact but the general nested height/depth prose has no datatype; the
  harmonic-increment theorem has only its leading term; the compound
  `plt:lem:mot-block-antiderivative` and `plt:prop:dif-block` remain without
  the concrete Laurent-series ambient and remaining faithful-evaluation and
  uniqueness links even though their integer equations and conditional
  nonresonant primitive API are exact; the real
  linear–log and `r = 1` power–log cores omit their asymptotic, complex, and
  general-`r` clauses; remainder transport includes its displayed explicit
  error law but omits the closing asymptotic clause; the three abstract
  differential-minimality assertions are exact but the concrete germ growth
  and algebraic-independence clauses are not; both concluding Wright-omega
  equivalences are exact, but the four-term quantitative expansion and an
  abstract transseries-scale construction are not packaged;
  staircase inversion omits the Fourier/interpolation layer; the nearest-
  integer theorem omits its real-argument and branch-family claims; and the
  quadratic coefficient recurrence is checked without the assembled square-
  root/deepest-pole construction.

The focused module/count inventory and per-result caveats are in the package
README and adjacent “Formal crosswalk” remarks in the canonical TeX.

## Residue audit

Deletion followed an audit of the twelve newly merged sources against the
assembled volume, and of the two consolidated volumes by direct containment.
The two volumes are absorbed verbatim: 32 of 32,874 substantive lines of the
calculus and 4 of 14,980 of the inversion volume differ, and every difference
is a transformation made deliberately at assembly — the sectioning shift, with
its 49 consequent "this section" → "this chapter" rewrites, and three retitled
chapters.

For the twelve articles, matching every named result against the volume's 768
titled results left six with no close counterpart; all six were checked
individually and are covered under other names, are alternative derivations of
a theorem the volume does state (a Lipschitz–Poisson route and a
Bose–Einstein-kernel route to the same pole expansion), or were demoted on
purpose. The audit's first pass left ten such results, and the four that were
genuinely missing — the saddle-localization lemma, the certified pole-tail
bounds, the linear pole budget, and the weighted Fubini polynomials — were
absorbed before deleting. Numeric residue is sequence values, numerical-table
mantissas and worked-example integers, none of them a result.

## The companion volume: combinatorial transseries (three arrivals of 2026-09-04, consolidated)

[`Combinatorial_Transseries_Inverses/`](Combinatorial_Transseries_Inverses)
is *Combinatorial Transseries and Their Inverses: Gamma quotients, finite
exponential sums, moment sectors, moving saddles, arithmetic sheets, and
q-products* (126 A4 pages in the rebuilt PDF; 5,616 source lines; nine parts, 20 chapters;
21 theorems, 10 propositions, 4 lemmas, 4 corollaries, every one with a
proof; loads `Analysis/FabiusFunction/docs/fabius-notation.tex`; labels `ct:` for the merge and
`t1:`, `t2:`, `t3:` for the absorbed sources).  It applies the canonical
volume's inversion architecture to combinatorial families the volume does
not treat, with three inversion engines proved once: phase-coordinate
inversion of an exactly invertible dominant phase with a closed formula for
every multiplicative-sector coefficient in signed Stirling numbers; a scaled
Lagrange–Bürmann reversion for corrections that are unbounded but small
relative to the core; and a convergent inverse-transseries theorem for an
analytic exponential tail on a quadratic, linear, or logarithmic phase, with
a finite nonrecursive coefficient formula and a geometric remainder.  The
families: balanced gamma quotients (Catalan, Fuss–Catalan, central
multinomials, rectangular tableaux) with the `W_{-1}` core; fixed-column
Stirling-II and Eulerian numbers (convergent multiexponential inverses) and
fixed-cycle Stirling-I numbers (nested logarithms); endpoint moment
sequences (Motzkin and central trinomial at general exponent, Delannoy,
large Schröder) with exact oscillatory sectors; involutions with two finite
saddle formulas, the unbounded `sqrt(X)/log X` drift and the `exp(-2 sqrt x)`
lattice; alternating permutations with odd-integer ordered-factorization
sectors and prime Euler products; connected labelled graphs with every
exponential layer and a range inverse; necklaces, Lyndon words and
irreducible polynomials with the finite-grid obstruction, fixed-radical
analytic sheets and a two-candidate threshold theorem; the `q`-products of
finite-field enumeration (general linear, symplectic and unitary orders,
flags, fixed-rank and scaled Gaussian coefficients, `q`-Catalan numbers,
Galois numbers with root-lattice theta sectors) and the singular `q → 1`
transition; harmonic and finite-limit inversion.  Certification, three sets
of recorded numerical checks, a synthesis, and appendices (coefficient
table, involution coefficient audit, Wolfram recipes, notation
reconciliation, provenance) complete it.

- Source: `Combinatorial_Transseries_Inverses.tex`; PDF built by three
  `pdflatex` passes with 0 errors, 0 undefined references, 0 overfull boxes.
- Verification: the three sources' programs and their recorded outputs are
  retained unchanged under `verification/source1/` (`verify.py`, `audit.py`,
  `coefficients.wl`), `verification/source2/` (`verify.py`,
  `audit_symbolic.py`, `coefficient_tools.wl`), `verification/source3/`
  (`verify.py`, `reference_implementation.wl`); the volume's numerical tables
  are their recorded runs, which the consolidation did not rerun.

### Provenance of the companion

Three independently written articles arrived on 2026-09-04 and were filed
the same day as separate members beside the volume:
`combinatorial_transseries_and_inverses/` (*Further Families*, 1,519 lines,
29 pp.), `combinatorial_transseries_extension/` (*Combinatorial Transseries
and Their Inverses*, 2,241 lines, 42 pp.), and
`combinatorial_transseries_extension-2/` (*q-Products, Finite Fields, Theta
Sectors, and Arithmetic Sheets*, 1,970 lines, 39 pp.).  The first two overlap
on most of their families and on all of their machinery; the third overlaps
with them only on central Gaussian binomial coefficients and on necklaces.
Every shared formula was compared symbol by symbol before one statement was
kept — the Catalan inverse coefficients through `X^{-3}`, the Fuss–Catalan
constants, the Stirling-column inverse coefficients in falling-factorial and
generalized-binomial form, the Motzkin block coefficients and first inverse
displacement, the involution amplitude through `t^5` and the inverse
coefficients `v_0, v_1, v_2` against `z_0, z_1, z_2`, the zigzag gamma block
and its first parity sectors, the central Gaussian-binomial logarithmic and
inverse coefficients — and no discrepancy was found.  Notation was reconciled
once (the involution blocks `A_±` and amplitude `B(t)`, the zigzag gamma
block `𝒢`, one spelling per coefficient-extraction and `q`-binomial symbol),
and the volume's notation chapter records every source variant.  The three
directories and their arrival PDFs were deleted after a residue audit of
every titled result (the six titles absent from the volume are all covered
under other names: the Stirling-column theorem, the sector-transport
theorem, the local certificate, the Motzkin beta decomposition, the
involution dominant inverse, and the zigzag Dirichlet factorization); git
history is the archive, and the volume's provenance chapter records what
each source contributed.

Nothing in the three articles is contained in the canonical volume, whose
combinatorial case studies (rooted trees, double and swing factorials,
partitions, Bell and Fubini numbers) are disjoint from theirs.  The companion
is kept beside the volume rather than folded in because the volume is under
concurrent formalization edits; folding it in as further parts is the
natural follow-up.  Note for future filing: on Windows a directory named
`Combinatorial_Transseries_And_Inverses/` is the same directory as the
deleted `combinatorial_transseries_and_inverses/`, which is why the
companion's directory omits the "And".

## Arrivals of 2026-09-29 to 2026-10-02 (unmerged)

Fifty-one research packages arrived through the repository drop zone
`docs/incoming/`: fifty on 2026-09-29, in nine deliveries (its batches 45
to 53; the eighth came in four drop-zone commits), and one on 2026-09-30,
in a tenth (batch 65).
Each is filed whole, with its PDF, verification program and recorded
outputs, in a directory named after the document. None has been reviewed
claim by claim, and none is merged into either volume; merging is deferred.
None contains Lean, and none of its statements is formalized. Ten of the
first twelve were written against the tree before the transseries split
and cite the volumes under
`Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/series-and-transseries/`;
the passages they cite are unchanged here apart from that path. The
gamma-core and residue-obstruction articles, and all articles of the third
to tenth deliveries, cite the current paths. No article of the first two
deliveries saw the others in the repository; where one continues another,
it read it from Vladimir's library, as noted below. The seven articles of
the third delivery were written after the first delivery was filed. Six
continue its regularity, moving-fold and inverse-harmonic articles
directly, and the seventh continues the companion volume; none saw another
article of its own delivery. Of the ten articles of the fourth delivery,
six were written before the third delivery was filed (two of them read the
critical Hahn article from Vladimir's library), and four after it. They
continue the regularity, finite-core, critical Hahn, inverse-harmonic,
Stokes-transport, reversion and residue-obstruction articles; none saw another article of its own delivery.
The five articles of the fifth delivery, which came in two parts, were
written against the same revision as the last four of the fourth, before
the fourth delivery was filed; two of them read endpoint articles of the
fourth delivery from Vladimir's library. They continue the critical Hahn,
marginal, finite-core and negative-ray articles, and none cites another
article of its own delivery, although two pairs of them answer the same
question. A sixth archive of that delivery, on the equilibrium of
hyperbolic Fekete designs, answers a question of the Fabius report
*Common-Digit Fabius Zonoids* and is filed beside it, under
`Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/representations/Elliptic_Equilibrium_Hyperbolic_Fekete_Designs/`;
the "transseries" of its title are convergent elliptic and modular
expansions. The five transseries articles of the sixth delivery were
written in one wave before the fifth delivery was filed, so none of them
saw a fifth-delivery article; the exact-degree article was written against
a revision from before the fourth delivery was filed. None cites Vladimir's library or
another article of its own delivery. They continue the regularity and
negative-ray articles (amplitudes), the critical Hahn article (slowly
varying tails), the residue-obstruction article (the exact logarithmic
degree), the finite-core article (its conjectured inverse law) and the
negative-ray article (natural boundaries for every slope degree); two of
them independently repeat fifth-delivery results, the inverse law and the
quadratic natural boundary. A sixth archive of that delivery, which shows
that a conjecture of the same Fabius report on small balls of polynomial
parameter jets (`conj:jet-small-ball`) is false as stated, is filed beside
that report, under
`Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/representations/Polynomial_Geometric_Small_Deviations_Fabius_Jets/`.
The two articles of the seventh delivery were written against the
revision that recorded the editorial pass over the first five deliveries,
and finished before the sixth delivery was filed, so neither saw a
sixth-delivery article. Neither cites Vladimir's library or the other.
One continues the critical Hahn article (its lower endpoint `α ↓ 1`); the
other answers no named question and starts from the action-accumulation
article's flat oscillations. The eighth delivery brought twelve archives.
Its eight transseries articles were written against three revisions, all
from before the seventh delivery was filed: six against the revision that
brought the sixth delivery's archives, one against the revision that
recorded the editorial pass over the first five deliveries, and one
against the revision that brought the seventh delivery's archives, whose
tree has the sixth delivery unamended. So none saw a seventh-delivery
article or another article of its own delivery, and only the
subexponential-cost article could see the sixth. None cites Vladimir's
library. Two continue the weighted-type article (arbitrary weights; the
subexponential cost), two the critical Hahn article (the lower endpoint on
the boundary-critical path, independently of each other), three the
Hahn–Fuchsian article (smaller input supports, and two nonlinear
counterparts), and one the resonance-block article (its critical line).
Its four other archives are not transseries work and extend reports of the
research-report collection under `SetTheory/Cardinals/docs/reports/`:
optimal Kummer atlases for the radical-solvers report, two independent
articles on the macroscopic jump law of adjacency-bounded 132-avoiding
permutations, and finite-output open-query games. The ninth delivery
brought two archives. Its transseries article, the triangular article, was
written against the revision that brought the eighth delivery's second
group of archives, whose tree has the sixth delivery amended but no
seventh- or eighth-delivery package; it continues the exact-degree article
and does not cite Vladimir's library. The other archive is not transseries
work: it answers the endpoint half of a question of the research-report
collection's *Shifted Catalan Hankel Polynomials* (uniform endpoint limits
of Catalan Hankel determinants) and becomes that report's Part IV, under
`SetTheory/Cardinals/docs/reports/hankel-determinants/catalan-and-ballot/shifted-catalan-hankel-polynomials/`.
The tenth delivery brought five archives. Its transseries article, the
finite-jet article, was written against the revision that brought the
archives of the drop zone's batch 63, whose tree has all nine earlier
deliveries amended; it continues the subexponential-cost article and does
not cite Vladimir's library, the exact-type article or the condensation
articles of the regularity unit. The other four archives are not
transseries work. Three continue the Fabius frontier drafts under
`Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/`
(the growth of prefix Rényi information above the critical order, the
natural boundary of the q-Fabius transform, and conditioned extremes of
uniform random series), and one, on closure-word duality for open-query
games, becomes Part IV of the research-report collection's
*Open-Query Membership Games*, under
`SetTheory/Cardinals/docs/reports/ordinals-and-order-types/games-on-ordinals/open-query-membership-games/`.

The eleventh delivery (2026-10-01, the drop zone's batch 73) brought one
transseries package among sixty-two archives, the factorial-transseries
article on OEIS A006014 below. It cites no repository revision and no
package of this group, and does not cite Vladimir's library. The other
sixty-one archives are not transseries work.

The twelfth delivery (2026-10-02, the drop zone's batch 77) brought three
transseries packages among seventy-one archives, the late-coefficient
articles on A395976, A274600 and A260879 below. Three cite the repository
revision `4b874cea0` as the snapshot of a bounded overlap search; none
cites a package of this group except that the A260879 article credits the
canonical volume's Fubini chapter. The other sixty-eight archives went to
the research-report collection under `SetTheory/Cardinals/docs/reports/`.

All fifty-two packages of the nine deliveries, the Fekete and
small-deviation ones included, were then amended in place by an editorial
pass on 2026-09-29. Unnumbered "Editorial note (ProveIt, 2026-09-29)"
blocks, which leave each article's own numbering unchanged, record
corrections, related repository results that the author
did not cite, and later packages that answer or overlap its questions. The
verification programs now write LF line endings and keep partial reruns
away from the recorded outputs, retired checksum ledgers are no longer
listed, figures with Type 3 fonts were regenerated, and every PDF was
rebuilt from its amended source. Every change to an article source is
marked by a `% ed.` comment, each package README lists its amendments, and
the delivered archives remain in the repository history
(`docs/incoming/README.md`, batches 45 to 53). Page and line counts and line
citations below refer to the amended files; the volumes are unchanged.
The sixth delivery was amended in the same way after it was filed, and
notes recording it were added to eight earlier packages. The seventh
delivery was amended in the same way after it was filed, and notes
recording it were added to three earlier packages (the critical Hahn,
confluent and logarithmic-endpoint packages). The eighth delivery was
amended in the same way after it was filed, and notes recording it were
added to eight earlier packages (the weighted-type, near-linear, critical
Hahn, lower-endpoint, confluent, logarithmic-endpoint, Hahn–Fuchsian and
resonance-block packages); the critical-line article needed no note. The
ninth delivery was amended in the same way after it was filed, and notes
recording it were added to two earlier packages (the exact-degree and
residue-obstruction packages).
The tenth delivery was amended in the same way on 2026-09-30, and notes
recording it were added to one earlier package (the subexponential-cost
package).
The eleventh delivery was amended in the same way on 2026-10-01; no
earlier package needed a note recording it.

[`Support_Controlled_Reversion_One_Exponential/`](Support_Controlled_Reversion_One_Exponential/)
holds *Support-Controlled Reversion and the Exact One-Exponential
Substitution Group* (25-page A4 PDF, 1,701-line source, an exact SymPy and
100-digit mpmath check program). It continues the canonical volume's
extension chapter and answers three of its open-problem remarks. For
`plt:rmk:ext-open-burmann` (`transseries_and_inversion.tex:29941-29952`) it
shows that the ordinary positive-integer Lagrange–Bürmann sum stays valid on
a Hahn power–log class with a dense exponent group, with a finite outer
index bound for each coefficient. For `plt:rmk:ext-open-denominators`
(`:29955-29969`) it shows that every Newton iterate stays in the input
Puiseux lattice, so `σ(s) = s`. It answers the formal, algebraic part of
`plt:rmk:ext-open-resurgence` (`:30002-30015`) negatively for unrestricted
"verbatim" closure. It gives an exact admissibility criterion (`P(L) = aL + b`
with `μa ∈ Γ`), a maximal substitution group, and exact-core inversion. It
proves the leading block of every inverse exponential sector (coefficients
`n^{n−1}/n!`) and works through the inverse of `X + log X + e^{−X}`.
Resurgence and Borel summability are not claimed. It names no commit; it
read the pre-split `main` source on 2026-09-29.

[`Critical_Transseries_Moving_Fold/`](Critical_Transseries_Moving_Fold/)
holds *Critical Transseries at a Moving Fold: a uniform two-sheet atlas,
large-sector crossover, and resonant action splitting* (25-page A4 PDF,
1,737-line source, an exact SymPy and 100-digit check program). It
continues the reversion article directly above, filed with it. It answers
that article's Research question 11.8 ("Sharp complex transition near the
core critical point", `reversion_and_one_exponential.tex:1562-1568`) for
`δ + log(1 + δ/w) + wz e^{−δ} = 0` in the independent-parameter local chart.
The results are an exact holomorphic two-sheet atlas, the moving critical
value `z_c(s) = s²/2 + s³/3 + 5s⁴/8 + ⋯` (`s = w + 1`), all-order profiles
with a geometric error bound at the branch point, and the crossover
`a_n(τ/n)/a_n(0) → e^{−2τ/3}`. For analytic folds driven by finitely many
exponential actions (the article's question on several actions and
resonances, `:1448-1456`) it gives a convergent, resonance-aware
representation with a finite positive support grid. The fixed-coupling
specialization `z = e^{−w}/w` at its core critical point is explicitly not
covered. It read the reversion article from Vladimir's library before
either was filed, and cites
`Analysis/FabiusFunction/Lean/FabiusFunction/QuadraticCoreCatalan.lean`
(the finite Catalan core of the volume's `p6:prop:quadratic-core-catalan`)
as related finite algebra only.

[`Reversion_Beyond_Archimedean_Valuations/`](Reversion_Beyond_Archimedean_Valuations/)
holds *Reversion Beyond Archimedean Valuations: strong Hahn convergence,
sharp Newton depth, and minimal finite coefficient certificates* (30-page
A4 PDF, 2,082-line source, an exact rational and SymPy check program with
its recorded output). It answers the reversion article's research question
"Beyond Archimedean exponent groups"
(`reversion_and_one_exponential.tex:1493-1502`) for Hahn power–logarithmic
series over an arbitrary ordered exponent group, given a fixed positive
shift `h` and an additive character `χ` with `χ(h) = 1` that define the
derivative. "Non-Archimedean" refers to the exponent group, not to an
absolute value. The finiteness invariant is the maximum length of a
positive support word, which Higman's argument keeps finite without an
Archimedean hypothesis. With it the article keeps the reversion article's
ordinary Lagrange–Bürmann sum and its Newton recursion, now measured in
word depth; that recursion is the reversion article's own rate
(`:524-527`), which the article presents as sharper without citing it;
an editorial note now credits it. New are the proof that the depth
`2^{n+1} − 1` is attained, by `u + z/(1 + u) = 0`, and the criterion that
valuation convergence holds uniformly exactly when the multiples of the
least support exponent are cofinal; strong Hahn convergence holds in every
case. It also answers the algebraic part of that article's
support-certificate question (`:1589-1594`): every finite coefficient
request factors through a minimal finite-rank quotient, and finite
supports have rational weight certificates. A rank-two support of depth
`n² + k + 1` has no positive real grading, and every superadditive depth
profile occurs in rank two. It could not fetch the canonical volume, so it
does not cite `plt:rmk:ext-archimedean`
(`transseries_and_inversion.tex:28303-28320`), which shows the same
phenomenon, or `plt:rmk:ext-neumann-general` (`:28140-28164`), where the
volume quotes the all-word lemma that this article proves. Nor does it cite
the surcomplex analysis volume's Hahn reversion lemma `e:lem-reversion`
(`Algebra/SurrealNumbers/docs/surcomplex/analysis/article.tex:4791-4828`),
which already has the same Lagrange sum over a non-Archimedean group
without logarithmic blocks, or its machine-checked word lemmas
`Surreal.HahnSeries.finite_words_of_sum_eq` and
`Surreal.HahnSeries.finite_wordsWithSum`
(`Algebra/SurrealNumbers/Surreal/HahnSeries/Neumann.lean`,
`NeumannWords.lean`). Editorial notes of 2026-09-29 in the article now
record all of these. Derivations with monomial-dependent shifts, such as
those of full logarithmic–exponential transseries fields, are not covered;
nor are analytic realization, Borel summability or resurgence. It cites the
Neumann declarations of
`Analysis/Transseries/Lean/Transseries/TransseriesWellBased.lean` as related
foundations only. It joins the reversion article's merge unit.

[`Exponential_Feedback_Regularity_Classification/`](Exponential_Feedback_Regularity_Classification/)
holds *A Sharp Regularity Classification for Countable Exponential-Feedback
Transseries* (25-page A4 PDF, 1,798-line source, an exact standard-library
coefficient program with NumPy/SciPy envelope diagnostics). For
`U(q) = Σ_{j≥1} q^j exp(λ_j U(q))` it proves the following: the solution
converges exactly when `λ_j = O(j)`; there is an exact factorial-normalized
Gevrey-type identity with constant `((s+1)/s)^{s+1}` times
`limsup λ_j/(j log j)^{s+1}`; regularly varying slopes give logarithmic
coefficient asymptotics and concentration; and the quadratic model's Borel
transform is entire but not Laplace-summable on the positive ray. It also
constructs left-sector analytic realizations and transfers the Gevrey class
to compositional inverses. The canonical volume motivates it, and it
answers none of that volume's questions by name. The nearest passages are
the formal-versus-analytic remarks `q0:rem:euler` and `q0:rem:beyond`
(`transseries_and_inversion.tex:487-507`), the Gevrey-1 hypothesis of
`p0:thm:optimal-truncation` (`:39359-39399`), and the open realization and
resurgence remarks (`:29986-30015`).

[`Near_Linear_Boundary_Exponential_Feedback/`](Near_Linear_Boundary_Exponential_Feedback/)
holds *The Near-Linear Boundary of Exponential Feedback: a self-consistent
Lambert law, coefficient large deviations, and a cascade of Borel-growth
resonances* (26-page A4 PDF, 1,645-line source, an exact-rational check
program with 467 assertions and floating normalizer diagnostics). It
answers the regularity article's question "The near-linear transition"
(`Exponential_Feedback_Regularity_Classification/article.tex:1519-1525`)
for slopes `λ_j = jL(j)` with `L` slowly varying and unbounded, and with
exponentially controlled positive amplitudes `c_j`, a restricted case of
that article's amplitude question (`:1569-1582`). With
`b e^b = L(n/(1+b))` it proves `u_n^{1/n} ~ c_1 e^{b_n}`, zero factorial
type at every Gevrey order, and a large-deviation principle for the
Lagrange composition length with rate `r − 1 − log r`. Every
factorial-normalized Borel transform is entire, with `log B_σ(t)`
determined by one more implicit inversion; this growth rules out
positive-direction Laplace summation of every finite Gevrey order. For
`L(j) = exp((log j)^γ)` it gives every nonvanishing term of the Borel
growth, constants `e^{1/m}` at `γ = 1 − 1/m`, and a uniform profile through
each such resonance. A multiplicative equivalent for `u_n` is not claimed.
Through the exact-type article (an editorial deduction recorded in both),
the inverse has `limsup |q_n|^{1/n} e^{−b_n} = 1`; a root limit remains
open.

[`Finite_Core_Universality_Exponential_Feedback/`](Finite_Core_Universality_Exponential_Feedback/)
holds *Finite-Core Universality and Sharp Large Order for Countable
Exponential-Feedback Transseries* (27-page A4 PDF, 2,104-line source, exact
standard-library coefficient checks through order 300, NumPy/SciPy saddle
diagnostics and a table program). The regularity article leaves open a
local limit theorem, the fluctuation scale and a full multiplicative
asymptotic (`article.tex:768-771`, `:1488-1495`), and its reversion theorem
transfers only the Gevrey class (`:1544-1549`). For `λ_j = a j^p`, `p > 1`,
with finitely many nonnegative changes, this article keeps `M` actions in
an analytic core and one further action by linear response. The resulting
coefficients are asymptotic to `u_n` exactly when `M(p − 1) > 1`. A coupled
saddle then gives a multiplicative equivalent with its determinant
prefactor, a conditional local Gaussian law and an unconditional central
limit theorem for the largest action. For `p = 2` a factor
`exp((1 + 1/a) r_n²)` survives. For `p > 2` the inverse coefficients
satisfy `v_n = −u_n + (n+1)u_2 u_{n−1} + o(n u_{n−1})`. The corresponding
inverse law at `p = 2` is stated only as a conjecture. The data files hold
`n!` times the coefficients.

[`Negative_Ray_Summation_Exponential_Feedback/`](Negative_Ray_Summation_Exponential_Feedback/)
holds *Negative-Ray Summation of Countable Exponential-Feedback
Transseries* (25-page A4 PDF, 1,679-line source, an exact-rational check
program with rational enclosures, and a majorant diagnostic). The
regularity article proves neither a uniform Gevrey remainder nor a
directional Borel summation (its `README.md`, and the questions at
`article.tex:1445-1452` and `:1617-1629`). For unit amplitudes and any
slopes `λ_j ≥ 0`, this article proves five equivalent conditions:
`λ_j = O((j log j)²)`; `U` is Gevrey-1; its compositional inverse `Q` is
Gevrey-1; `U` is finely Borel–Laplace summable in direction `π`; and so is
`Q`. "Fine" means a fixed-width half-strip, not an open sector. The sums are
inverse functions and satisfy the literal convergent kernel near the
negative axis. An explicit Bessel-kernel series continues the inverse Borel
transform to `|ζ| + Re ζ < 1/(2A)`, `A = limsup λ_j/(j log j)²`, and is
entire when `A = 0`. For `λ_j = j²` it proves a uniform remainder on a
closed left half-disc with an explicit majorant and an error bound
`exp[−(1/4 − o(1)) log²(1/r)/r]`; this is an upper bound, not a sharp
least error. Angular summability and resurgence are not claimed. Its
threshold agrees with the regularity article's Gevrey-type identity at
`s = 1`, and it applies with `A = 0` to the near-linear slopes above.

[`Critical_Hahn_Transseries_Beyond_Finite_Action_Folds/`](Critical_Hahn_Transseries_Beyond_Finite_Action_Folds/)
holds *Beyond Finite-Action Folds: Critical Hahn Transseries, Stable
Sector Asymptotics, and Sharp Action Budgets* (26-page A4 PDF, 1,858-line
source, exact checks, 75-digit constants and a probability recurrence
through `n = 4096`). It extends the moving-fold article's finite-action
critical inversion (`Critical_Transseries_Moving_Fold/article.tex:1051`)
to countably many actions, for the feedback kernel with linear slopes and
power-law amplitudes `a_j = a j^{−1−α}`, `1 < α < 2`. At the critical
coupling the boundary is not analytic, and its exponent is `1/α`, not a
square root. The article constructs a convergent Hahn chart
`x = T V(T, T^{2−α})` with a closed coefficient formula, finite
ramification exactly when `α` is rational, and an all-orders large-sector
expansion through stable-density derivatives, matched coefficient by
coefficient to the Hahn chart. Truncating the actions at `M_n` preserves
the `n`-th coefficient asymptotically exactly when `M_n/n^{1/α} → ∞`; at the
critical scale an explicit infinitely divisible profile gives the loss. It
also computes the critical-value and curvature drift of the finite folds. It
does not settle the moving-fold article's higher-multiplicity question
(`:1490-1496`), and it does not cite the regularity article's amplitude
question, of which it treats the case `λ_j = j`; an editorial note now
records it. An editorial note at its Question 4 now records the
lower-endpoint article's partial answer, and the answer on the
boundary-critical path by the Cauchy-cutoff and uniform-coefficient
articles.

[`Microscopic_Condensation_Exponential_Feedback/`](Microscopic_Condensation_Exponential_Feedback/)
holds *Microscopic Condensation in Exponential-Feedback Transseries: sharp
coefficients, Gaussian–Poisson limits, finite-perturbation universality,
and refined Borel growth* (24-page A4 PDF, 1,647-line source, an exact
integer-recurrence program with coefficients through degree 256 for four
slope sequences, and mpmath ratio diagnostics). It answers the regularity
article's question "Beyond logarithmic coefficient asymptotics"
(`Exponential_Feedback_Regularity_Classification/article.tex:1488-1495`)
for slopes `λ_j = j² + αj + ηj/log j + o(j/log j)` with arbitrary
nonnegative initial slopes. With `r_n(r_n+1)e^{2r_n} = n` and
`b = 1 + λ_1` it proves
`u_n ~ exp((2r_n+1) n r_n/(r_n+1) + b r_n² + α r_n + η/2)/√(2r_n²+4r_n+1)`,
with relative error `O((log n)²/√n)` when the slopes are eventually `j²`.
Typical configurations have exactly one part of size at least three. The
largest part and the number of twos are jointly close in total variation
to an independent discrete Gaussian and `Pois(r_n²)`, with a
two-dimensional local limit and a central limit theorem for the number of
factors. Changing only `λ_1` multiplies the coefficients by
`exp((λ_1 − λ̃_1) r_n²)`. It also gives multiplicative equivalents for the
positive-axis Borel transform and for the least term `min_n u_n tⁿ`. It was
written before the finite-core article above was filed; its author text
does not cite it, and an editorial note now does. For eventually exact `j²`
its coefficient equivalent is the `p = 2`, `a = 1` case of that article's
first-correction formula
(`Finite_Core_Universality_Exponential_Feedback/article.tex:1106-1111`),
and its least-term index is that article's. New here are the `α` and `η`
terms, the rate, the Poisson law of the twos at diverging intensity (which
that article asks for at `:1779-1791`), the Borel equivalent and the value
of the least term. Negative-direction summability, an analytic remainder
theorem and the inverse series are not claimed.

[`Poisson_Layers_Finite_Core_Boundary/`](Poisson_Layers_Finite_Core_Boundary/)
holds *Poisson Layers at the Finite-Core Boundary of Exponential-Feedback
Transseries* (20-page A4 PDF, 1,433-line source, an exact-rational check
program with 288 assertions, and NumPy/SciPy saddle and coefficient
diagnostics). It continues the finite-core article's questions on the
finite background cloud and on critical boundaries
(`Finite_Core_Universality_Exponential_Feedback/article.tex:1752-1791`), for
`λ_j = a j^p` outside a finite core of `M` actions. Marking each occurrence
of the first omitted action `M + 1` by `s`, it proves
`u_n(s) = w_{n,M} exp(s ν_{n,M})(1 + o(1))` throughout `(M+1)(p − 1) > 1`,
uniformly on compact parameter sets, with the core-independent intensity
`ν_{n,M} = (n r/(1+r)) e^{−Mpr}` and `r(1+r)^{p−1} e^{pr} = a n^{p−1}`. At
the boundary `p = 1 + 1/M` the missing factor is `exp(r_n^{M+1}/a^M)`,
which grows like the exponential of `(log n)^{M+1}`. This agrees with the
finite-core article's statement that the ratio tends to zero there
(`:228-245`), and sums that article's one-occurrence lower bound
(`:1011-1021`) exactly. A finite Poisson limit occurs only in the moving
window `p_n = 1 + 1/M + ((M+1) log log n + θ)/(M log n)`, above the
boundary and outside that article's fixed-parameter theorem, with parameter
`e^{−θ}/(a^M (M+1)^{M+1})`. The article also proves total-variation
convergence for bounded intensity, a central limit theorem and large
deviations for diverging intensity, and asymptotic independence from the
Gaussian largest action. At `p = 2` it splits the finite-core factor
`exp((1 + 1/a) r_n²)` into a core part and a layer of twos. It does not
treat logarithmically corrected tails, the whole cloud vector, a growing
core or the signed inverse. It does not claim total-variation Poisson
approximation at diverging intensity; the microscopic-condensation article
above proves that for `λ_j = j²`.

[`Sharp_Negative_Direction_Summability_Exponential_Feedback/`](Sharp_Negative_Direction_Summability_Exponential_Feedback/)
holds *Sharp negative-direction summability for countable exponential
feedback: a coefficient-to-remainder principle, optimal logarithmic
scales, and sectorial inversion* (20-page A4 PDF, 1,365-line source, an
exact standard-library program through degree 120 and mpmath finite-action
diagnostics). It answers the regularity article's question on uniform
Gevrey remainders for the sectorial solution
(`Exponential_Feedback_Regularity_Classification/article.tex:1617-1629`)
for all slopes `λ_j ≥ 0`: for every `s > 0`,
`|U(q) − Σ_{n<N} u_n qⁿ| ≤ C Aᴺ (N!)ˢ |q|ᴺ` holds on every proper left
sector exactly when `λ_j = O((j log(j+1))^{s+1})`. After the change of
unknown `U = qV` the kernel is analytic on a fixed disc, and positivity
ties its Taylor coefficients to the Lagrange coefficients. For every
`k > 1` a classical sectorial characterization, which the article imports,
then gives `k`-summability in direction `π` exactly when
`λ_j = O((j log(j+1))^{1+1/k})`, with sum the canonical solution; this
answers the directional question (`:1445-1452`) in the subquadratic range.
For slopes comparable to `j^p (log(e+j))^β` it finds the optimal
factorial–logarithmic weight and truncation-error bounds. The same holds
for the compositional inverse. The Gevrey and convergence criteria are
proved again, independently of the regularity article. It leaves the
quadratic case `k = 1` open and does not cite the negative-ray article
above, which its snapshot contains and which proves fine Borel summability
in direction `π` for `λ_j = O((j log j)²)`; it proposes that article's
inversion-first method as future work. Editorial notes now record the
negative-ray article and the natural-boundaries article below. Neither
article settles summability in an open sector of directions; for `λ_j = j²`
the natural-boundaries article below shows that it fails. Sharp constants
and lower bounds for the remainder are not claimed.

[`Sharp_Weighted_Type_Formal_Reversion/`](Sharp_Weighted_Type_Formal_Reversion/)
holds *Sharp Weighted Type Under Formal Reversion: zero-loss inversion,
exact Borel radii, and non-D-finiteness in countable exponential feedback*
(24-page A4 PDF, 1,775-line source, a standard-library exact-rational check
program and floating-point diagnostics labelled as such). It answers the
regularity article's question "Exact type under compositional inversion"
(`Exponential_Feedback_Regularity_Classification/article.tex:1544-1549`),
citing only that package's README sentence that reversion transfers class
membership, not the numerical type. Its core theorem does not depend on the
kernel: for a positive log-convex weight `M` with `M_0 = 1`,
tangent-to-identity reversion preserves the weighted coefficient type
`limsup (|a_n|/M_n)^{1/n}` exactly when `M_n^{1/n} → ∞`, by a finite
Lagrange majorant with subexponential overhead applied in both directions;
it adds an exact scaling law under analytic coordinate changes. It imports
two forward theorems of the regularity article, whose constants it
restates verbatim, and obtains the inverse Gevrey type
`((s+1)/s)^{s+1} limsup λ_j/(j log j)^{s+1}`, the inverse Borel radius
`1/(4A)` with `A = limsup λ_j/(j log j)²`, and the refined inverse type
`a(p/(p−1))^p` for `λ_j ~ a j^p (log j)^β` (`4` for `λ_j = j²`). For
integer `p` it gives the growth of both Borel transforms, whose forward half
is the regularity article's `thm:borelintro` (`:301-316`), and it proves
that `U` and its inverse are not D-finite. The radius is consistent with
the negative-ray article's continuation region `|ζ| + Re ζ < 1/(2A)`. It
does not cite the finite-core article above, although its snapshot
contains it; an editorial note now does. For `p > 2` that article's
`v_n ~ −u_n`
(`Finite_Core_Universality_Exponential_Feedback/article.tex:376-380`)
already implies the refined inverse type. At `p = 2` the conjectured inverse
equivalent (`:1705-1710`) differs from the forward one by a factor
`e^{o(n)}`, so this article neither settles nor contradicts it; it does
settle the exponential scale for `1 < p ≤ 2`, which that article leaves
open. Limits (as opposed to limsups), coefficient signs, angular summability
and differential transcendence are not claimed. Two articles of the eighth
delivery below continue its questions: the exact-type article answers
"Weights beyond log-convexity", answers "Two divergent composition
arguments" as far as types go and "Multivariate and operator-valued
inversion" in part, and the subexponential-cost article answers "Optimal
subexponential cost of reversion" for factorial weights. Editorial notes
at those questions now record this.

[`Exact_Weighted_Type_Beyond_Log_Convexity/`](Exact_Weighted_Type_Beyond_Log_Convexity/)
holds *Exact Type Beyond Log-Convexity: a complete reversion criterion,
sharp distortion, and dimension-free nonlinear calculus* (28-page A4 PDF,
2,107-line source, a standard-library exact-rational check program with
5,443 counted checks and floating-point diagnostics labelled as such). It
answers the weighted-type article's question "Weights beyond
log-convexity" (`Sharp_Weighted_Type_Formal_Reversion/article.tex:1497-1505`):
for an arbitrary positive weight, written in excess degree as
`N_n = M_{n+1}`, tangent-to-identity reversion preserves the weighted type
universally exactly when `N_n^{1/n} → ∞` and `log(S_n/N_n) = o(n)`, where
`S_n` is the largest product `N_{j_1}⋯N_{j_k}` over compositions of `n`,
the least supermultiplicative majorant. When the roots tend to infinity,
`Δ(N) = limsup (S_n/N_n)^{1/n}` is the optimal distortion constant; the key
estimate is that the positive extremal inverse has coefficients
`S_n e^{o(n)}`. For log-convex weights `S_n = N_n` eventually, so `Δ = 1`
and the weighted-type theorem is recovered. Explicit weights show that a
log-convex or root-monotone representative is not necessary, that every
finite distortion `c > 1` occurs, and that a type-zero series can have an
inverse of infinite type; the last also shows that the weighted-type
article's polynomial test needs its log-convexity hypothesis, which it
states. It answers "Two divergent composition arguments" (`:1507-1515`) as
far as types alone go (`T(f∘g) ≤ max`, equality for unequal types, every
value in `[0,T]` at equal types), and "Multivariate and operator-valued
inversion" (`:1517-1525`) in part: an exact tangent calculus on Banach
spaces with the multilinear operator norm, and sharp bounds
`T(F)/‖A‖ ≤ T(F⁻¹) ≤ ‖A⁻¹‖T(F)` for a general derivative, which one scalar
type cannot sharpen. The subexponential-cost article below, written
independently, proves the factorial case of the same composition law and
settles for factorial weights the next question this article poses, the
optimal overhead. Analytic realization, summability, Hahn supports, root
limits and Lean formalization are not claimed.

[`Sharp_Subexponential_Cost_Gevrey_Reversion/`](Sharp_Subexponential_Cost_Gevrey_Reversion/)
holds *Sharp Subexponential Reversion: exact extremal cost, a Gevrey
transition, and composition of two divergent series* (23-page A4 PDF,
1,446-line source, a standard-library exact check program with 5,338
scalar checks, and extended-precision diagnostics labelled as
uncertified). It answers the weighted-type article's question "Optimal
subexponential cost of reversion"
(`Sharp_Weighted_Type_Formal_Reversion/article.tex:1424-1433`) for its
named target, factorial weights: over the ball
`|a_{j+1}| ≤ C A^j ((j+ν)!/(1+ν)!)^s` one negative saturating series
maximizes every inverse coefficient, and the normalized amplification
satisfies `log R_n ~ C n^{1−s}` for `0 < s < 1`, `R_n ~ exp(C n^{1−s})` for
`s > 1/2`, `R_n ~ exp(C√n + 3C²/4 + C√(ν+2))` at `s = 1/2`, and
`R_n → exp(C e^{−t})` at `s = 1 + t/log n`. The fixed ball is therefore
stable under inversion exactly for `s ≥ 1`, although the type is preserved
at every order, and the weighted-type article's overhead `exp(O(n/√r_n))`
is not sharp. For "Two divergent composition arguments" (`:1507-1515`) it
proves, for factorial weights,
`τ_s(f∘g) ≤ max(τ_s(g), |g′(0)| τ_s(f))` with equality for unequal types,
the factorial case of the exact-type article's law, by a different
majorant. It also gives a positive series with a full normalized root
limit whose inverse has infinitely many zero coefficients. It re-proves
the weighted-type theorem only in its factorial case and says so; the
local-quotient version for general weights is left open. It was written
before the exact-type article above was filed, and neither cites the
other; editorial notes in both now link them.

[`Finite_Jet_Pressure_Laws_Gevrey_Reversion/`](Finite_Jet_Pressure_Laws_Gevrey_Reversion/)
holds *Finite-Jet Pressure Laws for Gevrey Reversion and Condensation:
complete multiplicative asymptotics, explicit critical constants, and
Poisson centering* (24-page A4 PDF, 1,706-line source, a
standard-library exact check program with 1,066 scalar checks, and
double-precision diagnostics through degree 10,000 labelled as
uncertified). It answers the subexponential-cost article's question
"Complete multiplicative cost below one half"
(`Sharp_Subexponential_Cost_Gevrey_Reversion/article.tex:1215-1223`),
the gap that article states at `:138-140`: for positive weights equal to
`D_* Γ(j+ν+1)^s` from some index on, with an arbitrary positive finite
head, and the family `F_θ(z) = z(1 − θ C W(z))^{1/θ}` (`θ ≥ −1`;
`F_0 = z e^{−CW}`), the normalized inverse coefficient satisfies
`log R_n = Σ_{k ≤ J} p_k n^{1−ks} + o(1)` with `(J+1)s > 1` and
`p_k = [t^k] Ψ_{ks}(B(t))/k`, where `B = tA′/(1 − θA)`, `A` is the
weight polynomial through degree `J` and
`Ψ_a(u) = ∫_0^u (1−v)^{−a} dv`. So every positive order, including every
reciprocal integer, has a complete multiplicative equivalent; at
`s = 1/3` it gives the constant `6^{1/3}C + (5/3)2^{1/3}C² + 7C³/9` that
the question asks for, and at `s ≥ 1/2` it recovers that article's
formulas. `θ = 1` is that article's coefficient-ball extremum and
`θ = −1` the partition function of superexponentially weighted plane
trees. It also proves a finite-jet universality law (only
`w_1, …, w_{⌊1/s⌋}` matter), every critical window `s = 1/r + t/log n`,
which answers that article's question "Uniform transitions at the lower
thresholds" (`:1236-1241`) although the article does not say so, and
the approximation of the small-part counts by independent Poisson
variables with explicit centering corrections of every order. The
Poisson approximation, the leading centering and the first two terms of
the tree expansion are credited to Janson, Jonsson and Stefansson
(2011), whose weights `((n−1)!)^α` are the case `θ = −1`, `C = 1`,
`ν = 0`; the all-order formulas are the article's. It re-proves the
subexponential-cost article's extremality and exact Lagrange sum for
every `θ` and says so. Only eventually exact shifted-factorial tails
with positive weights are treated, uniformly on compact positive-order
sets but not as `s → 0`, and the `o(1)` is not effective. It was
written after the exact-type article was filed and amended, but does
not cite it; for eventually factorial weights it extends that article's
question "Optimal subexponential overhead"
(`Exact_Weighted_Type_Beyond_Log_Convexity/article.tex:1918-1928`) to an
arbitrary positive head. Editorial notes now record these relations: in
this article, its uncited neighbours (the exact-type article and the
finite-core, microscopic-condensation and Poisson-layer articles, which
use its Poisson small-part mechanism for another kernel) and the second
answered question; in the subexponential-cost article, the gap and both
questions.

[`Logarithmic_Critical_Endpoint_Lambert_Charts/`](Logarithmic_Critical_Endpoint_Lambert_Charts/)
holds *The Logarithmic Critical Endpoint: Convergent Lambert Charts,
All-Order Sector Laws, and Sharp Action-Cutoff Corrections* (29-page A4
PDF, 2,001-line source, exact symbolic checks, and floating-point
diagnostics through sector index `n = 65536` checked against an 80-digit
recurrence). It treats the upper endpoint `α = 2` of the critical Hahn
article above, weights `a_j = a j^{−3}` outside a finite prefix, and
answers the fixed-endpoint half of that article's Question 4
(`Critical_Hahn_Transseries_Beyond_Finite_Action_Folds/article.tex:1509-1514`);
the joint limit `α ↑ 2` with `n` stays open. It read that article from
Vladimir's library before it was filed. The pole of `Γ(−α)` cancels a
divergent quadratic coefficient and leaves `x² log(1/x)`, and the critical
inverse is a convergent analytic function of two coordinates over a
`W_{−1}` Lambert core, with no finite Puiseux chart. The sector coefficients
have an all-order Gaussian–logarithmic expansion in `1/ℓ_n`, with `ℓ_n` an
exact Lambert logarithm. The fluctuation scale `√(n log n)` and the action
budget `√n` separate: the retained fraction tends to `exp(−1/(2s²))` at
`M = s√(nβa)`, with an explicit first correction. Conditioned large actions
form a Poisson process with intensity `x^{−3} dx`. The finite-fold drift is
given to all inverse-logarithmic orders, with an explicit condition for
exponentiating it, which answers that article's Question 7 at this endpoint
(`:1586-1591`); a leading-order extension covers `a_j ~ a j^{−3}(log j)^r`,
`r ≥ −1`. Its constants agree with the `α → 2` limits of the critical Hahn
article's normal form, budget and fold drift. The Gaussian and
extreme-value mechanism is credited to Janson. Numerical values are
diagnostics, not interval certificates, and no certified cutoff algorithm
is claimed. An editorial note at its Question 8 records the lower-endpoint
article's partial answer, and the answer on the boundary-critical path by
the Cauchy-cutoff and uniform-coefficient articles.

[`Marginal_Critical_Transseries_Action_Budgets/`](Marginal_Critical_Transseries_Action_Budgets/)
holds *Marginal Critical Transseries: Convergent Lambert-W Charts,
Universal Cutoff Corrections, and Certified Action Budgets* (26-page A4 PDF,
1,777-line source, 111 finite exact checks and 50-digit floating-point
diagnostics). It studies the same endpoint `α = 2` as the article directly
above, independently of it, and also read the critical Hahn article from
Vladimir's library; it answers the same half of Question 4 without citing
it by number. An editorial note now names that question and compares the
two endpoint articles. Its chart coefficients, fold series and inverse
diagnostics coincide with those of the article above, and its sector
constants and critical cutoff correction are that article's rewritten in
another logarithmic normalization (`H_n = log B_n` in place of `ℓ_n`). It
adds explicit contraction radii for the chart, a convergent three-generator
logarithmic grid, a two-term formula for the minimal action budget, and a
proved finite inequality that bounds the retained fraction from below on the
sharp `√n` scale. Its "certified" budgets are that inequality; the recorded
evaluations use no directed rounding. The all-order expansion is not claimed
to converge, and prefix independence is claimed only at the displayed order.

[`Confluent_Critical_Transseries_Exponent_Two_Boundary/`](Confluent_Critical_Transseries_Exponent_Two_Boundary/)
holds *Confluent Critical Transseries Across the Exponent-Two Boundary: A
Uniform Inverse Chart, Conditional Poisson Limits, and Sharp Action
Budgets* (24-page A4 PDF, 1,756-line source, an exact SymPy check program
with 160-digit inverse-chart and floating-point coefficient diagnostics).
It treats the joint limit that the two endpoint articles above leave open:
the upper endpoint of the critical Hahn article's Question 4
(`Critical_Hahn_Transseries_Beyond_Finite_Action_Folds/article.tex:1509-1514`)
with `α = 2 − ε_n`, where `ε_n → 0` at any rate and from either side, for
the exact tail `a_j = j^{−3+ε}/ζ(2−ε)`. This is also the
logarithmic-endpoint article's Question 1
(`Logarithmic_Critical_Endpoint_Lambert_Charts/article.tex:1636-1642`),
which it does not cite by number (an editorial note now does); it read
both endpoint articles from
Vladimir's library before they were filed. One convergent holomorphic
chart in the three variables `r`, `ε` and `1/h_ε(1/r)`, with
`h_ε(x) = (x^ε − 1)/ε`, covers the fractional, logarithmic and
finite-variance sides, with a geometric truncation bound. With
`A_n = (nc_ε)^{1/(2−ε)}` and `B_n² = nc_ε h_ε(B_n)`, `A_n/B_n → 0` for
every `ε_n → 0`. A triangular local limit gives
`u_n ~ ρ_{ε_n}^{−n}/(√(2π) n B_n)`, with an explicit window factor when
`ε_n log n` stays bounded; the retained fraction at `M ~ sA_n` tends to
`exp(−1/(2s²))`; and conditioned large actions converge to a Poisson
process with intensity `y^{−3} dy`, under exact lattice conditioning. At
`ε = 0` these are the two endpoint articles' formulas (`A_n` and `B_n` are
the marginal article's `N_n` and `B_n`). The coefficient law is leading
order only; uniform cutoff corrections, the lower endpoint `α ↓ 1` and
resurgence are not claimed. Its coefficient diagnostics need an
extended-range `long double` and stopped with an error when rerun on
Windows. An editorial note at its Question 10 records the lower-endpoint
article's partial answer, and the answer on the boundary-critical path by
the Cauchy-cutoff and uniform-coefficient articles.

[`Stable_Gaussian_Endpoint_Uniform_Critical_Transseries/`](Stable_Gaussian_Endpoint_Uniform_Critical_Transseries/)
holds *Through the Stable–Gaussian Endpoint: Uniform Critical Transseries,
Prefix-Independent Cutoff Corrections, and Conditional Extremes* (21-page
A4 PDF, 1,518-line source, 17 exact SymPy checks with long-double
recurrence and Fourier diagnostics). It answers the marginal article's
Question 1 ("A uniform transition as the stable exponent approaches two",
`Marginal_Critical_Transseries_Action_Budgets/Marginal_Critical_Transseries.tex:1563-1570`),
which it read in Vladimir's library, and so the same crossover as the
confluent article directly above, independently of it. It works in the
window `|2 − α| log n ≤ K`, on both sides, for tails
`c_ε j^{−3+ε}` after an analytic finite prefix. Its scales and window
formulas are the confluent article's. Inside the window it goes one order
further: a two-term uniform inverse, the first correction of the central
coefficient law, a uniform first cutoff correction
`exp(−ℓ^{−α}/α)[1 + (r/4){log(2/(rℓ²)) + 1 − γ − 2/ℓ²}]` at `M = ℓN`, in
which no finite-prefix moment appears, and a two-term minimal action
budget. At `α = 2` the correction is exactly that of the two endpoint
articles. Conditioned large actions converge to a Poisson process, and on
the finite-variance side the total variance need not give the central
scale. It does not cite the logarithmic-endpoint article, whose Question 1
is the same, or the confluent article; editorial notes now relate it to
both. Its default run needs an
extended-range `long double` and stopped with an error when rerun on
Windows; its tables are typed into the article.

[`Slowly_Varying_Action_Tails_Critical_Transseries/`](Slowly_Varying_Action_Tails_Critical_Transseries/)
holds *Slowly Varying Critical Transseries: Universal action budgets,
convergent Lambert charts, and an effective-index expansion* (23-page A4
PDF, 1,503-line source, 552 exact algebra checks with floating-point
coefficient diagnostics through `n = 65536` checked against a 65-digit
recurrence). It answers the critical Hahn article's Question 1, "Slowly
varying action tails"
(`Critical_Hahn_Transseries_Beyond_Finite_Action_Folds/article.tex:1462-1467`),
at a fixed exponent `1 < α < 2`, for `a_j ~ a j^{−1−α} ℓ(j)`. The critical
inverse scale is an asymptotic inverse of `y^α/ℓ(y)`, written with a de
Bruijn conjugate; the stable local limit, the cutoff profile and the
criterion `M_n/b_n → ∞` for a lossless cutoff are that article's, with
`ℓ` absorbed into the scale, and the profile has a strictly positive
`s`-derivative. The tail `2 + sin(log log j)` has no
power–iterated-logarithm leading monomial, so slow variation alone does
not preserve the Hahn grid. For exact tails `a j^{−1−α}(log j)^m` it gives
a convergent three-coordinate chart over a `W_{−1}` Lambert core, all
fixed orders of an expansion of the coefficients and retained fractions in
`1/log b_n`, whose first correction is the effective index
`α − m/log b_n` (not at second order), and a two-term minimal action
budget. Its stable scale omits the factor `Γ(−α)` that the critical Hahn
article puts into `b_n`; with that dictionary its profile at `ℓ ≡ 1` is
that article's, digit for digit. It does not cite the
logarithmic-endpoint article's log-weighted theorems at `α = 2`, which it
could see; an editorial note now does, and one in the critical Hahn article
now records this answer to its Question 1. The endpoint limit, growing
windows and certified budgets are left open.

[`Lower_Critical_Endpoint_Landau_Transseries/`](Lower_Critical_Endpoint_Landau_Transseries/)
holds *Through the Lower Critical Endpoint: Exponentially Coalescing Folds,
Landau Transseries, and Conditional Action Budgets* (26-page A4 PDF,
1,791-line source, 43 exact assertions, 24 high-precision normal-form
comparisons, and floating-point coefficient and cutoff diagnostics through
`n = 2048`). It answers the lower half of the critical Hahn article's
Question 4
(`Critical_Hahn_Transseries_Beyond_Finite_Action_Folds/article.tex:1509-1514`),
which that article's editorial note and README recorded as open (they now
record this partial answer), for the pure tail `c j^{−2−ε}`,
`α = 1 + ε ↓ 1`, on the interior-fold side only.
Normalizing by the exact fold `e^{−δ}` removes the apparent pole at `ε = 0`
and gives a convergent normal form, uniform however `ε` and `δ` vanish. At
`ε = 0` the fold distance is `δ = −log(1 − e^{−1/c}) ~ e^{−1/c}`, the
coefficients cross over at `λ = ncδ`, and their profile is an explicit
transform of the Landau density, with every finite order of correction in
`δ`. The inverse has a convergent chart over a `W_0` Lambert core, hence a
convergent expansion in `E = e^{−1/c}`, and a uniform two-sheet chart
through the fold; the Landau formula meets the Gaussian regime with the
factor `e^{ℓ/4}` when `λδ → ℓ`. Truncating the actions at `M` preserves the
coefficient exactly when `Mδ → ∞`, and the loss at scaled cutoff `m` is
doubly exponential, `√(λ/2π) exp(−m/(2λ) − λe^{m/λ})/(H(λ)m²)`, so the
scaled budget for a small loss `h` grows like `λ log log(1/h)`. At `ε > 0`
the model is the critical Hahn article's with `a = 1`, `β = c` and no
prefix; its exact fold reduces to that article's emerging-fold law, and its
Gaussian law has the shape of that article's supercritical law, which that
article states only for `1 < α < 2`. Its author text does not cite the same
question as posed by the confluent article (Question 10,
`Confluent_Critical_Transseries_Exponent_Two_Boundary/Confluent_Critical_Transseries.tex:1491-1498`)
and the logarithmic-endpoint article (Question 8,
`Logarithmic_Critical_Endpoint_Lambert_Charts/article.tex:1713-1717`), which
it partly answers on the same side; an editorial note now does, and notes
at those questions record the answer. It was written before the
slowly-varying article above was filed; an editorial note now relates its
slowly varying question to that article, and another gives the dictionary
to the critical Hahn article (its `δ` is the fold distance, not
`δ_β = 1 − βd_1`). The boundary-critical and subcritical paths, slowly
varying tails and certified budgets are left open. The boundary-critical
path is now answered by the two articles below, as an editorial note
records; the matching with this article's chart is not done.

[`Lower_Critical_Endpoint_Cauchy_Cutoff_Condensation/`](Lower_Critical_Endpoint_Cauchy_Cutoff_Condensation/)
holds *The Lower Critical Endpoint: Arbitrary-Rate Condensation, Cauchy
Cutoff Laws, and Degenerating Transseries* (25-page A4 PDF, 1,706-line
source, 62 exact algebra assertions and floating-point coefficient,
cutoff and chart diagnostics). It answers the lower half of the critical
Hahn article's Question 4
(`Critical_Hahn_Transseries_Beyond_Finite_Action_Folds/article.tex:1509-1514`)
on the boundary-critical path: tail `j^{−2−ε}` after a fixed finite prefix
`P`, coupling exactly `c_ε = 1/(ζ(1+ε) + P'(1))`, and `ε_n → 0` at any
rate. There `[q^n]U ~ ρ^{−n} ε/(n d_n)` with
`d_n = (nc_ε/ε)^{1/(1+ε)}`, which is the critical Hahn article's critical
coefficient law, proved uniformly as `α ↓ 1`. The coefficient comes from
one exceptional action of size `~ d_n`; deleting it leaves the
unconditioned Poisson configuration in total variation, and when
`nc_ε → ∞` the rest is a compensated `1`-stable (Landau) cloud of scale
`b_n = (nc_ε)^{1/(1+ε)}`, jointly with a Poisson `x^{−2}dx` process of
residual extremes. The least cutoff retaining a fraction `r` is
`D_n + b_n F^{−1}(r) + o(b_n)`, with the exact truncated-mean centre `D_n`,
which exceeds `d_n` by about `b_n log(1/ε)`, so a cutoff at `d_n` plus any
fixed number of widths retains nothing; bounded intensity gives a
compound-Poisson deficit, and at `ε log n → τ` the condensate carries the
fraction `e^{−τ}`. A convergent critical chart is uniform through `ε = 0`,
where the equation degenerates to `U = 0`. It does not cite the same
question as posed by the confluent article (Question 10) and the
logarithmic-endpoint article (Question 8), which it answers on this path;
an editorial note now does.
Its stable law is the lower-endpoint article's Landau law shifted by
`1 − γ`. The subcritical side, slowly varying tails and moving prefixes are
left open.

[`Lower_Critical_Endpoint_Uniform_Coefficients_Compound_Poisson/`](Lower_Critical_Endpoint_Uniform_Coefficients_Compound_Poisson/)
holds *The Lower Critical Endpoint of Exponential-Feedback Transseries:
uniform coefficient asymptotics, deletion of the largest action, Landau
cutoff profiles, and the compound-Poisson boundary* (21-page A4 PDF,
1,528-line source, 385 exact rational assertions, 55-digit Hankel checks
and an 80-digit recurrence comparison). Written independently of the
Cauchy-cutoff article above, from the same revision, it treats the same
family on the same path. By a branch-cut integral that keeps the vanishing
factor `ε` in the error, `u_n = ρ^{−n}J_0/(nB) (1 + O(εn/B² + n²e^{−ηn}))`
uniformly for all large `n` and small `ε`, with `B = (nK_ε)^{1/(1+ε)}`,
`K_ε = Γ(−α)/(ζ(α) + P'(1))` and `J_0 = −1/Γ(−1/α) ~ ε`, the same law;
every fixed order follows, and the first correction is asymptotic to
`−(3/2) εn/B²` for the pure tail. That correction reproduces the
Cauchy-cutoff article's recorded exact-recurrence ratios to three or four
digits. Deletion holds in total variation; for `nε → ∞`,
`(J − B)/(εB) + log ε` tends to minus a standard Landau variable, the
cutoff window of the article above written in other coordinates, with
Poisson residual extremes; for bounded `nε` the deficit is
compound-Poisson, and the two limits match. The critical chart is
convergent and uniform, and `U(ρz)/ε → Li_2(z) + P(z)`. It is the natural
base for this path: its coefficient theorem is quantitative and of every
fixed order, while the article above adds the joint limit of the cloud and
the extremes and the explicit centre. It poses as open the unnormalized
model at `α = 1`, which the lower-endpoint article treats for the pure
tail (a note records this; the matching is not done). It cites neither the
confluent nor the logarithmic-endpoint question (an editorial note now
does).

[`Quadratic_Exponential_Feedback_After_Reversion/`](Quadratic_Exponential_Feedback_After_Reversion/)
holds *Quadratic Exponential Feedback after Reversion: Cancellation,
Finite-Core Universality, and Sharp Borel Growth* (26-page A4 PDF,
1,897-line source, exact integer recurrences through degree 240 for
`a = 1` and 180 for `a = 2`, with 70-digit mpmath ratios). It claims a
proof of the finite-core article's conjecture `conj:quadratic-inverse`
(`Finite_Core_Universality_Exponential_Feedback/article.tex:1704-1710`):
for `U = Σ q^j exp(a j² U)` the inverse coefficients satisfy
`v_n ~ −S_n exp(−(1 + 1/a) r_n)`, with that article's `r_n` and `S_n`.
The proof inverts the kernel first, groups the exact tree expansion by
large actions, and merges multiple large actions in a positive majorant.
For finitely many nonnegative changes of weights and slopes, and slopes
eventually `a j² + dj + e`, the factor is `exp((d − μ) r_n/a)` with
`μ = λ_1 + w_2`. For every fixed core of at least two actions, the first
omitted action gives the relative error exactly; a slope perturbation
`κj/log j` multiplies the constant by `e^{κ/(2a)}`; and the
factorial-normalized inverse Borel transform is entire, with an explicit
double-exponential equivalent on the positive ray. Its constants agree
with those of the microscopic-condensation article (the `α r_n` and
`e^{η/2}` factors), the Poisson-layer article (its error term is the
layer intensity divided by `r_n`) and the weighted-type article
(`v_n/v_{n−1} ~ 4an/(log n)²`), none of which it could see. It thus
settles the `p = 2` inverse law that the weighted-type article neither
settles nor contradicts. It does not cite the negative-ray article, whose
question on signed inverse asymptotics
(`Negative_Ray_Summation_Exponential_Feedback/article.tex:1429-1438`) it
answers, or the regularity article; editorial notes now relate it to
these two and to the weighted-type and signed-inversion articles. Its
forward/inverse Borel comparison
uses the finite-core article's forward theorem. At `a = 1` its diagnostic
ratio `v_n/L_n` is still 0.85 at `n = 240`; the finite checks are not
evidence of the rate.

[`Signed_Quadratic_Feedback_Inversion/`](Signed_Quadratic_Feedback_Inversion/)
holds *Signed Quadratic-Feedback Inversion: A Finite-Core Resolution and
Sharp Entire Borel Growth* (21-page A4 PDF, 1,446-line source, exact
integer recurrences through degree 220 in four models, 80-digit mpmath
ratios and six SymPy identities). It is a second, independent claimed
proof of the finite-core article's conjecture `conj:quadratic-inverse`,
by the route that article proposes after it (`article.tex:1720-1722`):
resum an analytic inverse core, then bound the remaining signed tail,
here by an exact quadratic merger defect. Its exact coefficients are
those of the quadratic-inverse article directly above, and its Borel
equivalent is the same. Its hypotheses differ: after finitely many
exceptions the weights are `1` and the slopes exactly `a j²`, but the
exceptional weights and slopes may be any real numbers, so some weights
may be negative; the factor is `exp(−b r_n)` with
`b = (λ_1 + w_2)/a`. It also proves that two actions are the smallest
core that gives the leading term (one suffices exactly when `w_2 = 0`),
that the Borel transform's maximum modulus on `|z| = R` has the same
equivalent as its value on the positive ray, and the root and factorial
laws `log(|v_n|/n!) = −2n log log n + n log(4a) + o(n)`, which match the
weighted-type article's inverse type. The article above allows affine and
borderline slope tails and gives the sharp error of every fixed core;
this one allows signed exceptions. Neither author text cites the other,
the negative-ray article or the regularity article; editorial notes in
both now do. Its diagnostic ratio at
`n = 220`, `a = 1`, is 0.845; it claims no onset.

[`Natural_Boundaries_Quadratic_Exponential_Feedback/`](Natural_Boundaries_Quadratic_Exponential_Feedback/)
holds *Natural Boundaries of Quadratic Exponential Feedback: an exact
obstruction to angular Borel summation, analytic-curve rigidity, and a
rational-amplitude dichotomy* (23-page A4 PDF, 1,635-line source, an exact
standard-library program through degree 16 with 120-digit mpmath
diagnostics). It answers the negative-ray article's question "Angular
summability of the quadratic model"
(`Negative_Ray_Summation_Exponential_Feedback/article.tex:1370-1380`)
negatively. For `λ_j = j²` the literal inverse `Q` on `|u| ≤ 1/32`,
`Re u ≤ 0` is smooth up to the imaginary diameter, and every point `it`
with `|t| < 1/32` is a natural-boundary point. Its Borel transform is
entire and exponentially bounded on every fixed-width tube around the
negative ray (the negative-ray article's fine summability, which it
credits), but in no wedge around it. So neither `Q` nor `U` is angularly
1-summable in direction `π`, and `U` has the image arc, which is nowhere
real-analytic, as a natural boundary. The mechanism is a noncancellation
theorem for meromorphic heat expansions along analytic curves, applied at
rational imaginary times. For rational amplitude series with eventually
quadratic slopes, finite support, convergence, continuation through zero
and angular summability are equivalent. It also gives an explicit bound
for truncating the actions. It thereby answers the regularity article's
directional question (`Exponential_Feedback_Regularity_Classification/article.tex:1445-1452`)
in the angular sense, and the open-sector question that the
sectorial-summability article leaves open. It does not determine the
individual admissible rays or the growth in shrinking sectors, and it
warns that the obstruction is not a failure of resurgence. Its inverse
coefficients are those of the two inverse articles above at `a = 1`.

[`Amplitude_Slope_Compensation_Feedback_Transseries/`](Amplitude_Slope_Compensation_Feedback_Transseries/)
holds *Amplitude–Slope Compensation in Feedback Transseries: sharp
regularity, negative-ray summation, and damping-induced condensation*
(29-page A4 PDF, 1,919-line source, an exact standard-library program
with 1,353 assertions and a rational inverse certificate, and NumPy/SciPy
diagnostics through degree 512 labelled as such). It answers the
regularity article's amplitude question
(`Exponential_Feedback_Regularity_Classification/article.tex:1569-1582`)
for integer actions, and the negative-ray article's question on joint
amplitude–slope thresholds
(`Negative_Ray_Summation_Exponential_Feedback/article.tex:1480-1491`).
For `c_1 = 1`, `0 < c_j ≤ 1` (or positive, exponentially bounded
amplitudes after rescaling) and `d_j = −log c_j`, the solution converges
exactly when `λ_j = O(j + d_j)`, and for every `s > 0` the solution, its
inverse and a uniform inverse remainder on a closed left half-disc are
Gevrey-`s` exactly when `λ_j^{1/(s+1)} = O(j log(j+1) + d_j)`; at `s = 1`
this is also equivalent to fine summability of both series in direction
`π`. Under strong damping, `d_j/(j log j) → ∞`, the forward type is
`(s+1)^{s+1} limsup λ_j/d_j^{s+1}`; for `d_j ~ b j^β`, `λ_j ~ a j^p`,
`p > β > 1`, it is a root limit, and one action of size
`((p/β)n/b)^{1/β}` carries the amplitude cost. At `c_j = 1` its criteria
are the regularity and negative-ray articles'; its type theorem does not
specialize there. It does not cite the near-linear article, which covers
one of its examples, or the weighted-type article, whose zero-loss
theorem gives the equality of forward and inverse types that it leaves
open; editorial notes now cite both and record that equality, and notes in
the regularity and negative-ray articles now record its answers. General
real actions, angular summability, resurgence and
multiplicative asymptotics are not claimed.

[`Signed_Condensation_Sharp_Quadratic_Reversion/`](Signed_Condensation_Sharp_Quadratic_Reversion/)
holds *Signed Condensation in Quadratic-Feedback Transseries: sharp
reversion, universal cancellation, and inverse Borel growth* (22-page A4
PDF, 1,540-line source, exact integer recurrences through degree 320 for
`a = 1` and 160 in four further models, with 90-digit mpmath ratios). It
is a third independent claimed proof of the finite-core article's
conjecture `conj:quadratic-inverse`
(`Finite_Core_Universality_Exponential_Feedback/article.tex:1704-1711`),
written after the two above had been written but before they were filed,
and without sight of them. Its hypotheses and inverse law are those of
the quadratic-inverse article above, with that article's `d, e, μ`
written `b, d, β`: `v_n ~ −S_n exp((b − β) r_n/a)`, and its finite-prefix
and Borel theorems are that article's. After a large fixed analytic core
it bounds all configurations with two or more remaining actions
absolutely, before cancellation, by `S_n n^{−A}`, and evaluates the
one-action response on the core. New here is the least inverse term:
`min |v_n| tⁿ ~ exp(−R²/(at) + γR)/√(1 + 4R + 2R²)`, `R = ½ log(1/t)`,
`γ = (b − β)/a`, with the minimizing index to `o(√m)`; at `a = 1` its
constant `1/4` is that of the negative-ray article's remainder bound, and
it is a statement about formal terms, not a lower bound for the
truncation error. Its exact coefficients equal those of both inverse
articles above at every common degree. Its forward/inverse ratio uses the
finite-core article's forward theorem. Two of its research questions
(the smallest sufficient core, slowly varying departures) are already
answered by the two inverse articles above, and a third (signed primitive
data) in part. Editorial notes in it and in the finite-core, negative-ray
and both inverse articles now record these relations.

[`Natural_Boundaries_Survive_Nonlinear_Feedback/`](Natural_Boundaries_Survive_Nonlinear_Feedback/)
holds *Natural Boundaries Survive Nonlinear Feedback: moving-parameter
partial theta series, sharp half-plane realization, and the failure of
angular Borel summation* (22-page A4 PDF, 1,421-line source, an exact
standard-library program through degree 24 for `d = 2, 3, 4` with
110-digit mpmath diagnostics). For every integer `d ≥ 2` and
`U_d = Σ q^j exp(j^d U_d)` it proves that the literal inverse `Q_d` on a
small left half-disc is smooth up to the imaginary diameter and has that
whole diameter as a natural boundary, and that `U_d` has the image arc,
`it + 2t² − i(9/2 − 2^d)t³ + O(t⁴)`, as a natural boundary. The mechanism
is an all-orders estimate for periodic geometric moments along an
arbitrary holomorphic curve, with a mean-square argument for tied nearest
poles; for `d ≥ 3` it needs `|q_0| < e^{−d}`. The boundary survives
analytic forcing, analytic finite-core changes, periodic tail amplitudes,
finitely many changed slopes and affine-quadratic exponents. For `d = 2`
it answers the negative-ray article's question "Angular summability of
the quadratic model"
(`Negative_Ray_Summation_Exponential_Feedback/article.tex:1370-1380`)
negatively, as the natural-boundaries article above does independently,
with the same heat-expansion rigidity; that article has the explicit
radius `1/32`, the nowhere-analytic arc, the rational-amplitude dichotomy
and the action-truncation bound, and this one has every `d ≥ 3`, which
answers that article's higher-degree question
(`Natural_Boundaries_Quadratic_Exponential_Feedback/article.tex:1452-1458`)
for integer `d`; editorial notes in both articles, and in the negative-ray
article, now record this. It also gives a block-remainder majorant for
every `d` whose optimized scale has, at `d = 2`, the negative-ray article's
constant `1/4`. Its `d = 2` coefficients are those of the
natural-boundaries and inverse articles above. It does not classify
individual Borel rays, and its recorded run output is a second copy of
its verification record.

These twenty-five articles and the regularity article study one kernel,
`U = Σ c_j q^j exp(λ_j U)`, in complementary regimes, and form one unit for
the deferred merge; the regularity article is its host, and the critical
Hahn article also joins the moving fold. Six pairs and one triple
overlap, and later articles complete earlier ones. The amplitude–slope
article extends the regularity, Gevrey and negative-ray criteria to
positive amplitudes, with the joint budgets `j + d_j` and
`j log(j+1) + d_j`. The slowly-varying article extends the critical Hahn
article to slowly varying tails inside `1 < α < 2`; at `ℓ ≡ 1` its
profile and budget are that article's, and its logarithmic tails are the
interior counterpart of the logarithmic-endpoint article's log-weighted
theorems. Three articles treat `α ↓ 1`. The lower-endpoint article covers
the pure tail above the boundary-critical coupling: it reaches `α = 1`
through a normal form uniform in `ε`, and at `ε > 0` its fold law reduces
to the critical Hahn article's emerging-fold law and its Gaussian law has
the shape of that article's supercritical law. The Cauchy-cutoff and
uniform-coefficient articles prove, independently, the same theorems on
the boundary-critical path with a finite prefix: the critical Hahn
article's critical coefficient law holds uniformly, one action condenses,
and the cutoff window is a Landau law shifted by `b_n log(1/ε)`. The
second is the base (a quantitative theorem of every fixed order); the
first adds the joint limit of cloud and extremes. The three share the
Landau law; the subcritical side stays open. The
logarithmic-endpoint and marginal articles prove the same endpoint core;
the logarithmic-endpoint article, which covers more of the critical Hahn
article's questions, is the natural base, the marginal article's
certificate and budget sections enter beside it, and the confluent and
stable–Gaussian articles supply, independently, the crossover through `α = 2` (the second one order further in a bounded
window, the first at any rate). The exact-type, subexponential-cost and
finite-jet articles do not study the kernel; they join the unit through the weighted-type article, whose
kernel-independent reversion theorem the first extends from log-convex to
arbitrary weights, the second sharpens below the type for factorial
weights, and the third completes to a multiplicative equivalent at every
positive order for eventually factorial weights. In a merge they form one
reversion chapter with it, the exact-type criterion as the base, the
composition law stated once, in general, and the finite-jet pressure law
as the subexponential cost. The finite-jet article's Poisson small-part
counts are the reversion counterpart of the condensation mechanism of
the finite-core, microscopic-condensation and Poisson-layer articles, in
a different kernel. For eventually exact `j²` the
microscopic-condensation article's coefficient theorem is the finite-core
article's, and the quadratic-inverse, signed-inversion and
signed-condensation articles are three independent claimed proofs of that
article's conjectured inverse law: the first and third share their
hypotheses, the second allows signed exceptions, and the third adds the
least formal inverse term. The negative-ray and
sectorial-summability articles complement each other: fine summability at
order one in the first, remainders of every Gevrey order and summability
of every order `k > 1` in the second; the two natural-boundaries articles
show independently that for `λ_j = j²` summability at order one cannot be
angular, the second also for `λ_j = j^d`, `d ≥ 3`. Their
notations collide (`a` is the first amplitude, the slope constant or the
amplitude constant; `d_j` is the amplitude cost `−log c_j` in the
amplitude–slope article, while the eventual slope is `aj² + dj + e` in the
quadratic-inverse article and `aj² + bj + d` in the signed-condensation
article; the inverse is `Q`, `V̂`, `Q` with coefficients `q_n`,
or `V` with coefficients `v_n`; the endpoint articles use different
logarithms, the slowly-varying article's stable scale omits the factor
`Γ(−α)` that the critical Hahn article puts into `b_n`, the lower-endpoint
article's `δ` is the fold distance, not the critical Hahn article's
coupling mismatch `δ_β = 1 − βd_1`, and its `A = cΓ(1 − ε)δ^ε` is not that
article's action generating function `A(t)`; the Cauchy-cutoff article's
`δ = 1 − ε` is neither; its `b_n = (nc_ε)^{1/α}` is not the critical Hahn
article's `b_n`, which is asymptotic to its `d_n` and to the
uniform-coefficient article's `B`; its `Z` is the other articles' Landau
variable plus `1 − γ`; the exact-type article's `S_n` (an envelope) and
`N_n` (the weight) are the subexponential-cost article's composition sum
and Poisson variables,
the finite-jet article's `S_n` is a third sum (the finite-jet table sum),
its `A` both the ball radius and the weight polynomial `A(t)`, and its
`a_j = C w_j` are weights, not the subexponential-cost article's forward
coefficients `a_{j+1}`, the two crossover articles write `α = 2 − ε`, and
the inverse exponent is `(d − μ)/a`, `−b` or `(b − β)/a`), so a notation
dictionary must come first.

[`Uniform_q_Multinomial_Certified_Inversion/`](Uniform_q_Multinomial_Certified_Inversion/)
holds *Uniform q-Multinomial Transseries and Certified Inversion* (26-page A4
PDF, 1,627-line source, a 240-digit mpmath check program that also writes
the table the article inputs). It continues the companion's chapter "The
singular transition `q → 1`" (`Combinatorial_Transseries_Inverses.tex:4076`).
There, `t3:prop:double-A` (`:4103-4114`) holds only for `τ ≥ τ₀ > 0`, and
the text after `t3:eq:Slarge` (`:4205`) leaves "matching it uniformly
all the way to `τ = 0`" to "a different error analysis". The article
supplies that analysis for every positive multinomial ray: a signed
Bernoulli remainder bounded by the first omitted term for every `h ≥ 0`, the
Borel transform with nearest poles `±2πi a_*`, the least-term bound
`2r e^{−2π a_* x}`, sharp `h = 0` and resonant (`h = 2π/m`) equivalents, and
inverse enclosures that are not outward-rounded.

[`Uniform_Resurgent_Crossover_Gaussian_Binomials/`](Uniform_Resurgent_Crossover_Gaussian_Binomials/)
holds *Uniform Resurgent Crossover for Gaussian Binomial Coefficients: exact
remainders, a sharp modular-visibility threshold, and certified inversion*
(23-page A4 PDF, 1,587-line source, an exact SymPy and 110-digit check
program). It answers the same gap as the q-multinomial article directly
above (`Combinatorial_Transseries_Inverses.tex:4103-4114`, `:4205`),
for the central Gaussian coefficient only. Its interpolation is the
`r = 2`, `a = (1, 1)` case of that article's. It adds the sharp uniform
optimal remainder `e^{−2πx}/(π√x)·(1 + O_T(1/x))` for `0 ≤ hx ≤ T`, with
minimizing index `K = πx + O(1)`, and the modular-visibility boundary layer
`τ = 2π − (log x)/(2x) + s/x`. It also gives a convergent modular inverse
series about the Borel-summed carrier. The two articles share their method
(a Bose-kernel partial-fraction remainder) and their `h = 0` constant, and
should be merged together into the companion's `q → 1` chapter. They also
bear on the `τ ≥ τ₀` restriction of the Gaussian-binomial double scaling in
`Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/combinatorial-coefficient-calculus/Gaussian_Coefficient_Calculus/`
(`q3:thm:double-scaling`), which neither article's author text cites;
editorial notes now relate it (term by term for the q-multinomial
article).

[`Theta_Resolved_Optimal_Truncation_q_Multinomial/`](Theta_Resolved_Optimal_Truncation_q_Multinomial/)
holds *Theta-Resolved Optimal Truncation of q-Multinomial Transseries*
(26-page A4 PDF, 1,760-line source, a 75-digit check program, an
independent 150–400-digit endpoint check and a plotting script). It
continues the q-multinomial article above, which it read from Vladimir's
library before either was filed. It answers that article's questions Q1,
the lattice-to-integral transition of the least remainder, and Q2, a
uniform first hyperasymptotic correction
(`uniform_q_multinomial_transseries.tex:1375-1390`). It proves an
all-order expansion of the exact positive remainder at bounded
saddle-scaled mesh, governed by a Gaussian lattice (theta) sum in the
lattice phase and order tilt. It optimizes over all integer orders, which
gives a phase-dependent order shift of size `√z` and the corrected
minimum. At fixed nonresonant mesh it finds an exact arithmetic action
above the first unresolved pole, with a periodic prefactor, and it proves
a mesoscopic overlap between the two laws. Resolving `L` pole components
exactly moves the first unresolved action to `2π(L+1)a_min x`. Finite and
inverse certificates follow from positive tail bounds. General resurgent
completion, complex sectors and a growing pole count are not claimed.

[`Certified_Inversion_q_to_1_Transition/`](Certified_Inversion_q_to_1_Transition/)
holds *Certified Inversion Through the q→1 Transition: signed remainders,
optimal truncation, and a modular cancellation window* (25-page A4 PDF,
1,808-line source, an exact-rational and 80-digit check program). It
answers the same gap of the companion (`t3:prop:double-A`,
`Combinatorial_Transseries_Inverses.tex:4103-4114`; `:4205`) for the same
central Gaussian interpolation as the Gaussian-binomial article above. It
gives an exact positive-kernel remainder with signed first-omitted-term
bounds for every `h, x > 0`, a determinate Stieltjes measure with
convergent two-sided Padé bounds, and the optimal remainder
`(−1)^{M+1} e^{−2πx}/(π√x)` at `M = πx + O(1)` with its first relative
correction. Its principal new result is the additive law for inverse
errors against the modular term `e^{−4π²/h}`, with a parity-sensitive
cancellation window at `hx = 2π + (h log h)/(4π) + O(h)`: even orders
cancel there and odd orders reinforce. A shortest-block law extends the
leading remainder to Gaussian multinomials. The optimal remainder and the
window agree with the Gaussian-binomial article's theorem, which this
article re-derives independently under the narrower hypothesis that `hx`
stays in a compact subset of `(0, ∞)`. The fixed-`h`, `hx → ∞` regime is
not covered.

[`Gamma_Core_q_to_1_Crossover/`](Gamma_Core_q_to_1_Crossover/)
holds *A Gamma Core Across the q → 1 Crossover: uniform exponential
accuracy, inverse stability, and arithmetic convergence* (31-page A4 PDF,
1,510-line source, 100-digit main and supplementary check programs with
exact SymPy coefficient audits). It answers the same gap for the same
interpolation by a different truncation family: it keeps the Gamma
quotient `Γ(2x+1)/Γ(x+1)²` exact and expands the rest in `h = log q`.
With `K = max(2, ⌈2π²/h⌉)` terms, the logarithmic error is at most
`(8 + o(1)) e^{−4π²/h}` uniformly for all real `x ≥ 0`. A modular lower
bound shows that this action is sharp for the family. The inverse error
is at most `(24π² + o(1)) e^{−4π²/h}`, including the degenerate endpoint.
At a fixed index the `h`-series converges exactly when `2x` is an
integer; on every nonintegral half-integer sheet its sum misses the same
flat term `4M(h) − 2M(h/2)`, a combination of modular Euler products.

These three articles and the two above them answer the companion's
`q → 1` gap together and form one unit for the deferred merge into its
chapter "The singular transition `q → 1`". The q-multinomial article is the
most general of them. The five use different normalizations of the same
interpolation, so a notation dictionary must come first.

[`Inverse_Harmonic_Stokes_Transport/`](Inverse_Harmonic_Stokes_Transport/)
holds *Exponential Accuracy and Stokes Transport for Inverse Harmonic
Transseries* (24-page A4 PDF, 1,144-line source, a 190-digit check program,
an exact-rational certificate program and a figure script). It continues
the companion's harmonic-inverse section, `t2:thm:harmonic-inverse`
(`Combinatorial_Transseries_Inverses.tex:4285-4303`), whose coefficient
series "remains generally divergent" with "no convergence claim"
(`:4325`), and `t2:thm:general-harmonic-inverse` (`:4352-4368`). It
proves the complete large-order expansion
`h_n ∼ 2(−1)^n Γ(2n)/(2π)^{2n}`, exact-rational inverse certificates, and
the sharp error `(−1)^M √X e^{−2πX}(1 + O(1/X))` for the root of the
forward expansion truncated at `M = πX + O(1)`. It gives an explicit
convergent expansion of every inverse Stokes sector, and credits Borel
summability to Sauzin's closure theorems. The sharp remainder of a direct
partial sum of the inverse series is not claimed. The Lean module
`TransseriesHarmonicIncrement.lean` concerns the unrelated harmonic
increment `plt:lem:mot-harmonic`.

[`Nonlinear_Stokes_Transport_Logarithmic_Inversion/`](Nonlinear_Stokes_Transport_Logarithmic_Inversion/)
holds *Nonlinear Stokes Transport under Logarithmic Inversion: convergent
sector expansions, exact-core resurgence, real reconstruction, and
curvature-shifted fold scaling* (25-page A4 PDF, 1,123-line source, an
exact SymPy and 100-digit check program and a figure script). The canonical
volume motivates it, and it answers questions it poses itself. It proves an
inverse-transport theorem for an analytic map perturbed by finitely many
actions, with every mixed coefficient and a tail bound, and a weighted
countable extension. For one action it has the form of the inverse-sector
expansion that the inverse-harmonic article proves for its function, and
the two should be merged together. For `z + a log z` plus finitely many Euler terms it proves that
the inverse correction in the core coordinate `y + a log y = x` is Gevrey-1
and resurgent, by verifying Sauzin's closure hypotheses with an explicit
Borel kernel. It determines the finite inverse Stokes jump, and it shows a
sign-definite `O(e^{−2x}x^{2a})` defect between averaging and inversion. It
also recovers primitive amplitudes at nonlinear resonances and locates the
real fold of the amplitude expansion near `e^{−1}` with its curvature
shift. That model result bears on the reversion article's question on
analytic subclasses stable under exact-core inversion
(`reversion_and_one_exponential.tex:1472-1479`), and the fold on the
moving-fold article; its author text cites neither, and editorial notes
now do. The real core
`aX + b log X` is machine-checked in
`Analysis/FabiusFunction/Lean/FabiusFunction/LinLogCoreInversion.lean`.

[`Direct_Optimal_Truncation_Inverse_Harmonic/`](Direct_Optimal_Truncation_Inverse_Harmonic/)
holds *Direct Optimal Truncation of Inverse Harmonic Transseries:
reflection, positive tail densities, and eventual enveloping* (25-page A4
PDF, 1,713-line source, a 190-digit check program with six exact-rational
sign certificates, and a symbolic amplitude program). It answers the
inverse-harmonic article's problem `prob:direct`
(`inverse_harmonic_transseries.tex:976-980`) for the direct partial sums
`S_N` of the inverse series of `ψ(W + 1/2) = log X`. From an exterior
dispersion representation with an eventually positive tail density and a
retained convergent correction, it proves that `W` lies strictly between
consecutive partial sums for all `X ≥ X₀`, `N ≥ N₀`, with an explicit
sufficient criterion but no numerical threshold. At `σ = N + 1 − πX`
bounded, `S_N − W = (−1)^N √X e^{−2πX}(1 + B_1(σ)/X + ⋯)` to all orders, with
`B_1 = (2σ² − 3σ + 7/12)/(2π) − π/12` and `B_2` explicit. That is half the
first omitted term. The ratio to the first omitted term is `1/(1 + r²)` for
every fixed `r = (N + 1)/(πX)`, and the profile is `exp(τ²/π)` on the
square-root window. The inverse-harmonic article's forward-truncation root
has `+π/12` in place of `−π/12`, so the two procedures differ by
`(π/6) X^{−1/2} e^{−2πX}`.

[`Inverse_Digamma_Spectral_Representation/`](Inverse_Digamma_Spectral_Representation/)
holds *A Spectral Representation for the Inverse Digamma Function: direct
optimal truncation, eventual enveloping, and inverse Borel boundary
singularities* (24-page A4 PDF, 1,125-line source, an exact SymPy and
240-digit check program, a contour-quadrature check and a figure script).
It answers the same `prob:direct` by the route that problem suggests: an
exact spectral decomposition of `W(z) − z` with a positive density and a
convergent inner-contour correction. Its direct remainder, its eventual
enveloping and its comparison with the forward truncation coincide with
the article above: the coefficients `B_0`, `B_1`, `B_2`, and the density
coefficients through the fourth, agree term by term. The two are
independent proofs of one theorem. It adds an inverse cosine
representation of the Borel transform on `|Im ξ| < 2π`, the complete
one-sided singular expansion at the nearest Borel singularities with every
logarithmic coefficient (for the nearest points of the inverse-harmonic
article's problem on local singularities, `:985-988`), and a general
transfer theorem from a boundary-phase defect to such data. Continuation to
further sheets is not claimed.

[`Optimal_Truncation_After_Nonlinear_Reversion/`](Optimal_Truncation_After_Nonlinear_Reversion/)
holds *Optimal Truncation after Nonlinear Reversion: a sharp cutoff-transfer
theorem and the inverse harmonic function* (23-page A4 PDF, 1,109-line
source, a 312-digit numerical check program, a standard-library
exact-rational program with six error enclosures, and a SymPy coefficient
program). It is a third answer to the inverse-harmonic article's
`prob:direct` (`inverse_harmonic_transseries.tex:976-980`), written before
the two articles above were filed. Its general theorem (`article.tex:403`)
controls the difference between the root of a truncated logarithmic
correction and the direct partial sum of its inverse, for any coefficients
with a two-sided `Γ(2j)` envelope and no sign assumption, by a finite
diagonal formula at every fixed relative order. For `ψ(W + 1/2) = log X` it
gives the direct remainder at bounded `σ = M + 1 − πX` (`:592`); its `D_1`
and `D_2` agree term by term with `B_1`, `B_2` of both articles above, and
its forward-minus-direct difference `π/6` with their comparison results.
New are the second coefficient `σ²/6 − σ/4 + 25/144` of that difference,
the explicit second forward coefficient, corrected adjacent-partial-sum
averages that gain any fixed algebraic power (with
`θ_1 = (1 − 4σ)/(8π)`, `:755`), and exact-rational error enclosures for
partial sums and midpoints. Its enveloping result holds only on the window
`|M − πX| ≤ K` and is weaker than the theorems above. Global enveloping,
explicit thresholds and complex sectors are not claimed; its floating
checks are not interval computations.

[`Resonance_Block_Summation_Transseries/`](Resonance_Block_Summation_Transseries/)
holds *Resonance-Block Summation of Transseries: small divisors, coalescing
Stokes actions, and nonlinear inversion* (26-page A4 PDF, 1,801-line
source, 36 exact and 15 high-precision numerical checks). It continues the
Stokes-transport article's countable inverse
(`Nonlinear_Stokes_Transport_Logarithmic_Inversion/article.tex:241-249`),
whose hypothesis is a finite sum of individual perturbation norms, for the
Borel kernels `t^d / ∏ sin(π ω_j t)`. Their actions lie in a finitely
generated, locally finite monoid, yet nearby poles of different lattices
have residues with small denominators. Grouping poles closer than a fixed
threshold into blocks of at most `d` nodes, each block is a confluent
divided difference with a bound independent of the internal separations;
the block series equals the lateral Stokes jump, converges normally on the
right half-plane and has an explicit action-cutoff tail (`article.tex:495`).
For two lattices the ungrouped residue series has absolute-convergence
abscissa exactly `limsup (1/n) log(1/‖nα‖)` (`:655`), and an explicit
Liouville-type period makes it diverge everywhere while the series stays
Gevrey one (`:724`). Finite-cut expansions stay valid and unique,
coalescing poles have a uniform divided-difference profile, and a finite
single-base rational-exponential form exists exactly for rational period
ratios. Its inverse theorem is the Stokes-transport article's contour
inversion in core coordinates, with the block norm as its data, as it
says. It answers, without citing it (an editorial note now records it),
the forward half of that article's problem on countably many resurgent
input poles
(`Nonlinear_Stokes_Transport_Logarithmic_Inversion/article.tex:1026-1028`);
the resurgent structure of the inverse is not claimed. Its "resonances" are
near-collisions of Borel poles, not the equal-action resonances of the
Stokes-transport and moving-fold articles. An editorial note after its
Question 1 now records the critical-line article's answer.

[`Critical_Line_Continued_Fractions_Riesz_Summation/`](Critical_Line_Continued_Fractions_Riesz_Summation/)
holds *At the Critical Line: Continued Fractions and Sharp Riesz Summation
of Resonant Transseries* (23-page A4 PDF, 1,686-line source, 192 exact and
49 numerical assertions at 110 digits, and two table inputs). It answers
the resonance-block article's Question 1, "The boundary of the raw-series
half-plane" (`Resonance_Block_Summation_Transseries/article.tex:1534-1541`).
For two irrationally related sine lattices, numerator degree `D ≥ 2` and
`0 < b = β(α) < ∞`, with convergents `p_k/q_k` and
`A_k = q_k^D q_{k+1} e^{−b q_k}`, raw increasing-action convergence on
`Re z = b` holds exactly when `A_k → 0` and absolute convergence exactly
when `Σ A_k < ∞`, while the two separately indexed lattice sums converge
exactly when `Σ (−1)^{p_k+q_k+k} A_k e^{−i Im(z) q_k}` does. Explicit
continued fractions realize absolute and conditional convergence,
opposite divergent separate sums, two-point cluster sets and unbounded
spikes at every positive abscissa, and the `j`-th derivative has the same
criteria with `q_k^j A_k`. For `d` fixed lattices, integer Riesz means of
order `m ≥ d − 1` recover the block sum on the whole half-plane, with a
finite derivative bias and a uniform `O(T^{D−m} e^{−σT})` remainder,
without a Diophantine condition; the order is sharp for period-uniform
control, one more order gives continuity at a collision on the cutoff,
Richardson extrapolation removes the bias, and a local inverse stability
theorem carries the accuracy through inversion. Off the critical line its
criterion reproduces the resonance-block article's abscissa.

These five articles, the inverse-harmonic article and the Stokes-transport
article form one unit for the deferred merge. The direct-truncation
article covers every truncation ratio and is the natural base for the
direct result, which the spectral and optimal-truncation articles prove
again by other routes. The spectral article's Borel boundary data and
transfer theorem, the optimal-truncation article's general cutoff theorem,
corrected averages and enclosures, the Stokes-transport theorem for several
actions and the resonance-block estimate enter as further sections. The two
direct-truncation articles use different normalizations of the density and
of the contour correction; the optimal-truncation article uses the
direct-truncation article's `σ` and index. The critical-line article enters
after the resonance-block article's abscissa theorem, as its boundary case
and its Riesz alternative to grouping.

[`Action_Accumulation_Nonlinear_Inversion/`](Action_Accumulation_Nonlinear_Inversion/)
holds *Action Accumulation and Nonlinear Inversion: a Laplace–measure
calculus, hidden oscillations, and limits of Hardy-field realization*
(29-page A4 PDF, 1,272-line source, a 120-digit check program). It gives a
composition and inversion calculus for exponentially weighted action
measures, with the explicit inverse `−Σ s^{n−1}μ^{*n}/n!`, geometric
remainders and no positive action gap required, and a rooted-tree bound
for compact support. The function `A(x) = Σ_{j≥1} j^{−2} e^{−x/j}` has an
exact Poisson–Bessel resolution; `A(x) − 1/x` is smaller than every power
but has zeros `x_m = (π/4)(m + 5/8)² − 3/(32π) + O(1/m)`. Hence `A` lies
in no Hardy field with the identity and is not definable in any
o-minimal expansion of the reals; the zeros survive inversion of
`x + κe^{−ax}A(x)`, and at zero gap the inverse has a convergent Catalan
expansion yet is not its sum. It poses its own questions. It is an
analytic counterpart to the companion's necklace frontier, where actions
accumulate at `log q` (`Combinatorial_Transseries_Inverses.tex:2848-2852`,
`:4971`), and to the inverse-harmonic article's problem on action
accumulation (`inverse_harmonic_transseries.tex:1010-1013`). It does not
retain divisibility indicators, so it does not supply the arithmetic
algebra those passages ask for. It cites the Neumann well-basedness
declarations of `Analysis/Transseries/Lean/Transseries/TransseriesWellBased.lean`
(its bibliography now gives the current path beside the pre-split
one) only to note that its supports lie outside
them.

[`Moment_Determinacy_Nonlinear_Transseries/`](Moment_Determinacy_Nonlinear_Transseries/)
holds *Moment Determinacy and Nonlinear Transseries: A sharp Gevrey
threshold, exact flat defects, convergent ambiguity sectors, and
Lambert–W folds* (26-page A4 PDF, 1,905-line source, a 130-digit check
program with exact inverse-coefficient, lattice-moment and flat-defect
checks). It answers no named question. Starting from the flat oscillations
of the action-accumulation article above, and from that article's note on
the canonical volume's open `plt:rmk:ext-open-realization`
(`Transseries_And_Inversion/transseries_and_inversion.tex:29986-30000`), which
it leaves open, it asks whether all inverse coefficients and positivity of
a representing measure determine the inverse `T = yS(T)` of a Stieltjes
transform `S(t) = ∫(1 + tλ)^{−1} dμ(λ)`. They do exactly when the Stieltjes
moment problem of `μ` is determinate. A cancellation-free Lagrange formula
gives the inverse coefficients the Gevrey order of the moments, so order at
most two forces uniqueness, while for every order above two a generalized
gamma family gives a continuum of realizations of one formal inverse. The
flat defects are exact: `πα t^{−β} exp(−sec(πα) t^{−α})/Γ(β/α)` for the
gamma family, and `(q;q)_∞³/(MΘ_q(t))` for the even and odd `q`-lattices,
whose log-periodic amplitude keeps it comparable to the least moment bound.
Shifted lattices satisfy the same exact `q`-Euler equation and still differ,
and their inverses cross infinitely often, so the two cannot lie in one
Hardy field. Through the inversion it gives the first relative gap
corrections, a coefficient-only error floor, and convergent expansions in
the hidden parameter with explicit tails, whose radius is
`t_0/(e p y D_0)`: the rescaled deformation map tends to `v e^{−v}`, the
coefficients tend to the Cayley numbers `k^{k−1}/k!` of the canonical
volume's tree function `p1:def:cayley`, and a real fold keeps the first
gamma or theta correction. Its author text does not cite the repository's
determinate instances, the canonical volume's Bell transform `p8:thm:bell`
and the certified `q → 1` article's Stieltjes measure; an editorial note
now does (the Bell measure has Gevrey order at most one, so it is unique;
the `q → 1` measure is at the factorial-square boundary), and another names
the Lean modules its formalization section alludes to. The classical
moment theory is attributed, and the numerics are not interval-certified.

[`Arithmetic_Transseries_Beyond_Accumulation_Cut/`](Arithmetic_Transseries_Beyond_Accumulation_Cut/)
holds *Arithmetic Transseries Beyond an Accumulation Cut: divisibility,
summable inversion, and curvature-lifted resonances* (26-page A4 PDF,
1,799-line source, a check program with 964 exact assertions and 48
inverse-error checks at 400 digits). It answers the companion's third
research direction, an arithmetic transseries algebra for divisor sums
that retains the divisibility indicators, permits the action accumulation
at `log q`, and states which products and inverses remain summable
(`Combinatorial_Transseries_Inverses.tex:4971-4973`, with the benchmark
`t2:prop:necklace-cutoff`, `:2810`). It builds an arithmetic Hahn ring with
lcm-convolution multiplication, and weighted Banach algebras in which the
whole accumulating block is summable on expanding families of analytic
sheets. The elementary block is admitted exactly when
`Σ_d |c_d| e^{−ad} < ∞`. For `e^{ax}(1 + E_n(x))/x`, which covers necklaces
and primitive necklaces on their exact ranges, it proves a convergent
inverse over all actions at each fixed label, with explicit coefficients
and a geometric remainder. The first inverse sector beyond the primitive
action cut has action `a`, but its pure-exponential amplitude cancels,
leaving a curvature factor of order `X^{−1}`; an exact coefficient
transformation explains this at every homogeneous order and for cores
`e^{ax}x^{−b}`. Idempotent and profinite obstructions show why the inverse
is stated sheet by sheet. A canonical global interpolation, fractional
shifts of the indicators, and resurgence are not claimed. It is the
arithmetic algebra that the action-accumulation article above does not
supply, and it also answers the inverse-harmonic article's problem on
arithmetic action accumulation (`inverse_harmonic_transseries.tex:1010-1013`),
which it does not cite; an editorial note now records it. The two articles
form one unit for the deferred merge into the companion's necklace chapter.
It reads the Dickson and Neumann declarations of
`Analysis/Transseries/Lean/Transseries/TransseriesWellBased.lean`
as interfaces only; none of its theorems is formalized.

[`Residue_Obstructions_Logarithmic_Depth_Promotion/`](Residue_Obstructions_Logarithmic_Depth_Promotion/)
holds *Finite Residue Obstructions and Logarithmic-Depth Promotion in Hahn
Transseries* (28-page A4 PDF, 1,211-line source, an exact-rational block
and matrix check program). It extends
`Analysis/Transseries/Lean/Transseries/TransseriesBlockAntiderivative.lean`
(the canonical volume's `plt:lem:mot-block-antiderivative`) from
polynomial blocks to well-based Hahn blocks. In the real Hahn field of
`x, log x, …, log_n x`, the image of the `m`-th derivative is cut out by
exactly `m` residue moments. For `P(xD)` perturbed by terms that lower the
outer exponent uniformly, solvability at fixed depth reduces to a finite
residue matrix with an explicit cutoff, and kernel and cokernel have
dimension `r − rank M`. One more logarithm removes every obstruction:
particular solutions have degree at most `s` in it and homogeneous ones at
most `s − 1`, where `s` counts the distinct real roots. A Jordan-shift
family attains both bounds. Its `m = 1` case sharpens the canonical
volume's `plt:thm:ext-tower-strict`
(`transseries_and_inversion.tex:29092`) to an exact sequence; the article
does not cite that theorem, and an editorial note now credits it. It
concerns differential operators, not the compositional inverses of
`plt:rmk:ext-open-depth` (`:29918-29938`).

[`Hahn_Fuchsian_Resonance_Analytic_Normalization/`](Hahn_Fuchsian_Resonance_Analytic_Normalization/)
holds *Finite Resonance Certificates and Sharp Analytic Normalization for
Hahn–Fuchsian Systems: accumulating exponents, unavoidable logarithms, and
a summability-threshold crossover* (25-page A4 PDF, 1,644-line source,
exact SymPy gauge checks on finite systems and 85-digit crossover checks).
It continues the residue-obstruction article directly above, which it knew
through that package's README, from scalar operators to first-order
systems `xY' = (A_0 + A_+(x))Y` over the log-free Hahn field with `log x`
adjoined, with real-spectrum `A_0` and well-ordered positive exponents that
need not be locally finite. A unique normalized gauge
`Y = H x^S exp(B log x)` exists (`hahn_fuchsian.tex:442`); the solutions of
logarithmic degree at most `d` form a space of dimension `dim ker B^{d+1}`
(`:526`); and the resonant matrix depends polynomially on finitely many
input coefficients even when infinitely many exponents lie below the
largest resonance (`:629`). Every absolutely convergent semigroup-supported
input has an absolutely convergent normalized gauge exactly when the
nonresonant exponents stay a uniform distance from the eigenvalue
differences (`:780`); otherwise rank-one square-zero inputs give
arbitrarily small counterexamples. For exponents `2 − 1/n` with weights
`n^{−p}` the normalizer converges exactly when `p > 2`, although a
renormalized solution realizes every finite prefix for `p > 1`. For its
class and without citing them (an editorial note now does), it answers the
article above's questions on recovering the logarithmic filtration from
matrix ranks (homogeneous part) and on the invariant for matrix systems with
Jordan chains (`residue_fredholm.tex:1040`, `:1077-1079`): it is the
nilpotency index of `B = N + ΣR_ρ`. It is the depth-0 counterpart of that
article, not its generalization: the article above needs depth `n ≥ 1`, and
forced equations, iterated-logarithm coefficients and nonreal spectrum are
not treated here. Its constants lemma is the depth-0 case of the canonical
volume's `plt:thm:ext-tower-strict` (`transseries_and_inversion.tex:29092`),
which it could not read; an editorial note now cites it. Another records
the path-sensitive article's answer to its questions 11.1 and 11.2. The two
articles, the exact-degree article and the four articles after it form one
unit for the deferred merge, on differential equations over Hahn fields;
the residue-obstruction article is its host, the exact-degree article
supplies its degree classification, and this article its depth-0 system
counterpart. Their conventions (large variable in the first and third,
small `x` here; the
residue functional on the full field in the first, on lower blocks in the
third) need a dictionary first. It cites the Neumann declarations of
`TransseriesWellBased.lean` and the module
`TransseriesBlockAntiderivative.lean` as related only.

[`Exact_Logarithmic_Degree_Smith_Invariants/`](Exact_Logarithmic_Degree_Smith_Invariants/)
holds *The Exact Logarithmic Degree of Hahn-Transseries Solutions: Finite
jets, Smith invariants, and cancellation-sensitive resonance* (30-page A4
PDF, 1,282-line source, 1,383 exact SymPy assertions and an independent
exact operator check). It answers the residue-obstruction article's
question "The exact minimal power of the promoted logarithm"
(`Residue_Obstructions_Logarithmic_Depth_Promotion/residue_fredholm.tex:1039-1042`)
for that article's whole class, and its question on cancellation-sensitive
resonance (`:1052-1055`) for a residue-weighted scalar subclass. Letting
`z` stand for differentiation in the added logarithm lifts that article's
residue matrix to a series `M(z)` whose Smith exponents satisfy
`Σν_i = r`, `0 ≤ ν_i ≤ s`. They give the dimension of the solutions of
each degree and the least degree for each forcing, and block Toeplitz
ranks of the jet `M_0, …, M_{s−1}` decide them, with rational
certificates of impossibility. For operators `P(E) + σ Σ x^{−η} q_η(E)`
with simple real roots the series is exactly `zD_P + N`, and every
partition of the order is realized. The residue-obstruction article's
Jordan-shift family is the case `q_1 = 1` (a single Jordan block), whose
coefficients it reproduces. A fourth-order family has one resonance graph
but different degrees for `a = ±1`. It was written before the
Hahn–Fuchsian article above was filed, and does not cite it (an editorial
note now does); that article's homogeneous formula `dim ker B^{d+1}` at
depth 0 has the form of its pencil case. It restates the
residue-obstruction article's fixed-depth theory without citing its labels;
editorial notes now name them, and notes in that article now record its
answers. It concerns formal solutions only. Notes in it and in the
residue-obstruction article now record the triangular article's partial
answers to their questions on perturbations small only in logarithms and
on matrix systems.

[`Path_Sensitive_Small_Divisors_Hahn_Fuchsian/`](Path_Sensitive_Small_Divisors_Hahn_Fuchsian/)
holds *Path-Sensitive Small Divisors in Hahn–Fuchsian Systems: exact
convergence criteria, resonance amplification, and stable analytic
renormalization* (21-page A4 PDF, 1,431-line source, 2,363 exact rational
checks and 96 numerical crossover cases at 75 digits). It answers the
Hahn–Fuchsian article's questions "Universal convergence for a fixed
smaller input support" and "Weighted convergence in the zero-gap case"
(`Hahn_Fuchsian_Resonance_Analytic_Normalization/hahn_fuchsian.tex:1395-1412`)
for every finite acyclic matrix pattern with a real diagonal constant term,
well-ordered positive edge supports and independently variable edge
coefficients, exact resonances allowed. With `E_p` the exponent sumset and
`ρ_p` the endpoint spectral difference of a directed path, the normalized
gauge converges universally exactly when no `ρ_p` is a left accumulation
point of its own `E_p`; otherwise arbitrarily small bounded-support inputs
diverge at every radius. For independent weighted inputs the exact
criterion is finiteness of explicit polynomial-logarithmic path-kernel
norms. Three- and four-dimensional examples separate the path test from
the whole-semigroup and the edge-by-edge tests and show that correlated
inputs can do better. A rank-`r` resonant chain needs
`Σ n^{r−1}|c_n| < ∞` although its input needs only `Σ|c_n| < ∞`, and a
basepoint-normalized analytic solution realizes every finite prefix under
the weaker condition, with a uniform `N ≍ log(1/x)` crossover. At `r = 2`
the chain is the Hahn–Fuchsian article's accumulation model: its
threshold `p > 2`, its renormalized solution, and a second-order form of
its crossover, which the article does not say (an editorial note now
does). The path criterion
specializes to that article's universal theorem when every edge carries
the whole semigroup; nontriangular inputs and fixed Jordan blocks are not
treated. It cites the Neumann declarations of `TransseriesWellBased.lean`
as related only.

[`Nonlinear_Hahn_Dulac_Finite_Resonance_Control/`](Nonlinear_Hahn_Dulac_Finite_Resonance_Control/)
holds *Finite Resonance Control of Nonlinear Hahn–Dulac Transseries: exact
logarithmic slopes, analytic realization, and accumulation thresholds*
(28-page A4 PDF, 1,935-line source, exact SymPy block and coefficient
identities, random coupled systems and 80-digit tail-bound illustrations).
It poses its own question, extending the Hahn–Fuchsian and
residue-obstruction articles to `(x d/dx − A)y = F(x, y)` with real
spectrum and a well-ordered monoid of actions that need not be locally
finite. The right global invariant is the degree-to-action slope
`sup deg P_γ/γ`, not a finite logarithmic degree: it equals the maximum
over the finitely many resonant actions, is computed from a finite
divisor-closed set of input coefficients, has algebraic sublevel sets and
is invariant under logarithm-free changes of coordinates. Every absolutely
convergent input has an absolutely convergent normalized solution exactly
when the nonresonant actions stay a uniform distance from the eigenvalues
of `A` (not their differences); otherwise linear forcing gives small
counterexamples. For `(D − 2)y = ax + bx² + cy² + Σ t_n x^{2−1/n}` the slope
is `0` or `1/2` according as `b + ca²` vanishes, independently of the tail,
while convergence holds exactly when `Σ n|t_n| < ∞`, the Hahn–Fuchsian
article's threshold `p > 2` surviving the nonlinearity. It was written
before the exact-degree article above was filed and does not cite it; an
editorial note now does.

[`Nonlinear_Hahn_Fuchsian_Algebraic_Convergence_Loci/`](Nonlinear_Hahn_Fuchsian_Algebraic_Convergence_Loci/)
holds *Algebraic Convergence Loci for Nonlinear Hahn–Fuchsian Systems*
(23-page A4 PDF, 1,462-line source, 21 finite systems and 670 exact SymPy
equalities). It poses its own question: can infinitely many small divisors
impose a nonalgebraic convergence condition on the finite resonant
parameters of a positive, logarithm-free Hahn solution of
`Dy = Ay + F(x, y)`? No: all divergence is confined to a bounded window
of exponents, formal compatibility is a finite algebraic condition with a
sharp degree bound, and the parameters giving absolutely convergent
solutions form an affine algebraic set even at zero spectral gap, with a
common radius on compact parameter sets; conversely every affine algebraic
set occurs. It proves, independently of the Hahn–Dulac article above, the
same universal criterion (distance from the monoid to the eigenvalues of
`A`), for arbitrary complex `A`, with genuinely quadratic counterexamples.
For `(D − 3)y = ax + Σ_{n≥3} n^{−p}x^{2−1/n} + by² + 2b²y³` every forcing
exponent stays more than `1` from the resonance, yet the products
`y_1 y_{2−1/n}` create small divisors, and convergence holds exactly when
`p > 2` or `ab = 0`: the nonlinear counterpart of the path-sensitive
article's two-edge example. No finite set of input coefficients
determines the convergence locus. It cites `NeumannWords.lean` as related
only. Editorial notes in it and in the Hahn–Dulac article now record their
common criterion.

[`Triangular_Hahn_Differential_Systems_Without_Smallness/`](Triangular_Hahn_Differential_Systems_Without_Smallness/)
holds *Triangular Hahn Differential Systems Without Smallness: rank-one
descent, exact logarithmic degree, and finite residue certificates*
(27-page A4 PDF, 1,028-line source, 1,413 exact rational and symbolic
assertions and 36 high-precision illustrations). It takes up the
exact-degree article's questions "Perturbations that are small only in
logarithms" and "Matrix systems and nonreal modes"
(`Exact_Logarithmic_Degree_Smith_Invariants/exact_logarithmic_degree.tex:1137-1138`,
`:1157-1158`), which are the residue-obstruction article's
"Perturbations small only in logarithms" and "Matrix systems and nonreal
indicial roots"
(`Residue_Obstructions_Logarithmic_Depth_Promotion/residue_fredholm.tex:1062-1065`,
`:1077-1080`), and answers them in part: it replaces the outer-small
hypothesis by triangularity. For a system `diag(D − a_i) + N` over the
real Hahn field of `x, log x, …, log_n x`, with `N` strictly triangular and
no smallness assumption on any coefficient, a diagonal factor is split
(`a_i` a logarithmic derivative in the field) exactly when `a_i` is a real
combination of `ρ_j = 1/(x log x ⋯ log_j x)` plus a series below `ρ_n`, and
no greater finite logarithmic depth creates a new rank-one mode. With `r`
split factors and `q` the largest number of split vertices on a path of
the coupling graph, every solution in the whole finite logarithmic tower
is polynomial in `T = log_{n+1} x`, forced solutions have degree at most
`q` and the `r`-dimensional homogeneous space at most `q − 1`; a residue
series `M(z)` with diagonal `z` and determinant `z^r` has Smith exponents
`ν_i` with `dim S_d = Σ min(d + 1, ν_i)`, and finite Toeplitz systems in its
jet decide the least degree of each forcing, with positive and negative
rational certificates. It covers scalar operators that factor into
first-order factors over the field, so `x y' = (log x)^{−α} y` is split for
`α ≥ 1` but for `0 < α < 1` has no homogeneous solution at any finite
depth. In a three-dimensional example a nonsplit middle coordinate
transports a residue that a direct coupling cancels at `c = 1`, lowering
the least forced degree from 2 to 1, with actual solutions and signed
factorial error bounds. It does not decide triangularizability, treat
cyclic couplings or construct the exponential extensions of nonsplit
modes. It was written before the three articles above were filed and does
not cite them (an editorial note now does); its path bound is the
counterpart, for arbitrary Hahn coefficients at every depth, of the
path-sensitive article's degree lemma (degree of a path kernel = number of exact resonances), and its
cancellation example is the kind of correlation that article excludes by
independent edge coefficients. It names the block-antiderivative API of
the canonical volume as related only.

In that unit, the path-sensitive article refines the Hahn–Fuchsian
article's universal theorem for prescribed supports, and the Hahn–Dulac and
convergence-locus articles form its nonlinear part: they prove the same
universal criterion independently (the first with logarithms and a real
spectrum, the second logarithm-free with a complex one), and their
accumulation examples are complementary (accumulating forcing in the first,
accumulation generated by products in the second). The Hahn–Dulac slope is
the nonlinear counterpart of the exact-degree article's logarithmic degree,
and the convergence loci are a nonlinear counterpart of the algebraic
logarithmic strata whose geometry the Hahn–Fuchsian article asks about
("Geometry of the logarithmic strata"), not an answer to that question.
The triangular article extends the exact-degree article's Smith
classification from outer-small scalar operators to triangular systems
with arbitrary coefficients at every logarithmic depth; its degree bound
by split vertices on a path and its Smith formula `Σ min(d + 1, ν_i)` have
the form of the path-sensitive lemma and of the Hahn–Fuchsian
`dim ker B^{d+1}`. Their conventions (`Λ`, `A`, `A_0`; `P` for the gauge in
the first two, for a polynomial block in the third; `N`, `q`, `r` and `ρ_j`
in the triangular article) need a dictionary first.

[`Factorial_Transseries_OEIS_A006014/`](Factorial_Transseries_OEIS_A006014/)
holds *Factorial Transseries for OEIS A006014: hypergeometric
linearization, an exact A130032 bridge, a proof of the factorial
constant, all-orders late terms, and Lambert-W inversion* (22-page A4
PDF, 1,303-line source, an exact/80-digit check program and its recorded
output, an unsubmitted OEIS update draft). For `a_{n+1} = (n+1)a_n +
Σ_{k=1}^{n−1} a_k a_{n−k}` it proves `A = x U′/U` with
`U = ₂F₀(α, ᾱ;; x)`, `α = (1 + i√3)/2`, that `n![xⁿ]U` is A130032, that
`a_n/n!` increases to `C = 1/(Γ(α)Γ(ᾱ)) = cosh(π√3/2)/π` (the OEIS
estimate credited to Kotesovec, 2024, now with explicit global bounds), an
exact one-parameter transseries family `x (log(U + σ e^{−1/x} U(−x)))′`
with every sector `e^{−m/x}` and the Stokes jump `σ₊ = σ₋ − 2πiC`, the
all-orders factorial expansion `a_n ~ C Σ φ_j Γ(n+1−j)` with generator
`R/x + xR′`, `R = U(−x)/U(x)`, a Lambert-W inverse through `M^{−3}`, and
a one-parameter deformation. It is a new sequence case for the canonical
volume's Part "Inversion: the apparatus for a rapidly growing function"
(`Transseries_And_Inversion/transseries_and_inversion.tex:37288`,
`p0:sec:top`) and sits beside its chapter "The subfactorial" (`:53222`,
`p8:sec:top`), the volume's other factorially growing sequence; its
inverse re-derives that apparatus for its own core without citing it. An
editorial note there now cites it: the core `M(log M − 1) = X` is the
volume's factorial core (`p0:prop:factorial-core`, `κ = 1`, `d = −1`) and
the core of its gamma inverse (`p6:sec:gamma`); for `a_n = C n!` the
article's reversion returns `p6:thm:gamma`, and the factor `1 − 2/n + …` of
`a_n/(C n!)` turns its `1/(24Mq)` into `49/(24Mq)` and adds an `M^{−2}` term;
the general reversion is `p0:thm:perturbed-inversion` and the step to the
integer threshold `p0:thm:staircase`. The method is the volume's; the
A006014 coefficients are new to the repository. It
leaves the Borel singularities at actions 2, 3, … open (article.tex:621-623)
and is not formalized.

[`Late_Growth_Bessel_Counting_Coefficients/`](Late_Growth_Bessel_Counting_Coefficients/)
holds *Late growth of Bessel counting coefficients* (639-line source, its
PDF, an exact check suite). For A336293, `a_n = Σ C(n,k)² C(2k,k) (n−k)!`,
and its half-power coefficients `d_j` (A395976/A395977) it proves
`d_j = (2e²/(π 4^j)) {Σ_{m<M} 16^m c_m Γ(j−2m) + O(Γ(j−2M))}` with a finite
Bernoulli-polynomial generator, hence Kotěšovec's conjecture and eventual
positivity, both inverse constructions with rounding-aware enclosures, and
a fixed-colors corollary. It does not settle positivity for every `j > 5`.
It is a new sequence case for the canonical volume's Part "Inversion: the
apparatus for a rapidly growing function" (`p0:sec:top`); its
factorial-series algebra is Borinsky's; not formalized.

[`Late_Coefficients_Three_Letter_Abelian_Squares/`](Late_Coefficients_Three_Letter_Abelian_Squares/)
holds *Late coefficients of three letter abelian squares* (889-line source,
its PDF, check programs). It proves A274600's conjectured
`a_n ~ (2/log 3)^n (n−1)!/(π√3)` with every fixed correction, the exact
normalized Borel transform, the median-Laplace representation and a nonzero
Stokes jump of action `log 3/2`, Lambert inversions for the late
coefficients and for A002893, and a convergent Lagrange generator of the
inverse exponential sectors. It leaves the farther Borel sheets, optimal
truncation and Stokes smoothing open. Its Lambert inversions are instances
of `p0:thm:lambert-core`; not formalized.

[`Late_Coefficients_Factorially_Forced_Catalan_Recurrence/`](Late_Coefficients_Factorially_Forced_Catalan_Recurrence/)
holds *Late coefficients of the factorially forced Catalan recurrence*
(720-line source, its PDF, check programs). For A229741,
`a_n = n! + Σ a_i a_{n−1−i}`, it proves the A260879 conjecture
`c_k ~ Γ(k)/(log 2)^k` with every fixed correction, an exact positive
Stirling transform, smooth inverses and threshold enclosures for both
sequences, and, separately, the exact positive half-truncation remainder
with its parity-dependent scale and nine scalar corrections. Its
pole-lattice estimates overlap the volume's chapter "The Fubini numbers: an
exact pole lattice" (`q2:sec:fubini`, `q2:thm:fubini`, `q2:thm:weighted`),
which it credits; it sits beside the A006014 package, the other factorially
forced quadratic recurrence (a different sequence); not formalized.

The optimal-truncation articles (q-multinomial, Gaussian binomial,
theta-resolved, certified inversion, gamma core, inverse harmonic and the
three direct-truncation articles) are sharp instances of
the canonical volume's `p0:thm:optimal-truncation`
(`transseries_and_inversion.tex:39359`). Their inverse enclosures, and the
residual-transport enclosure of the negative-ray article, use the
mechanism that `Fabius.exists_eq_in_residual_interval`
(`Analysis/FabiusFunction/Lean/FabiusFunction/MeanValueBracket.lean`)
machine-checks. None of their author texts cites either; editorial
notes in the five `q → 1` articles and the inverse-harmonic article now
cite both. The moving-fold article has no least-term truncation; an
editorial note there cites the Lean lemma for the real monotone case of
its residual transport, of which its complex fold statement is not a
case. The truncation bounds of the
negative-ray, sectorial-summability and second natural-boundaries articles
are majorants, the least terms of the microscopic-condensation and
signed-condensation articles are formal, not remainder estimates, and the
moment-determinacy article's least moment bound is compared with its flat
defect, not with the actual truncation error; none of these is a sharp
instance.

Thirty checksum ledgers were verified in full on filing and not filed.
From the first delivery, these are the two `SHA256SUMS.txt` of the
regularity and inverse-harmonic packages and the `SHA256SUMS` of the
moving-fold package. From the second, they are the `SHA256SUMS` of the
gamma-core package, the `MANIFEST.sha256` of the certified-inversion
package, and the `SHA256SUMS.txt` of the Stokes-transport and
action-accumulation packages. From the third, they are the `SHA256SUMS.txt`
of the near-linear, direct-truncation, finite-core and critical Hahn
packages. From the fourth, they are the `SHA256SUMS` of the
logarithmic-endpoint and optimal-truncation packages and the
`SHA256SUMS.txt` of the marginal, resonance-block and Poisson-layer
packages. From the fifth, they are the `SHA256SUMS` of the confluent,
natural-boundaries and signed-inversion packages and the `SHA256SUMS.txt` of
the quadratic-inverse and stable–Gaussian packages. From the sixth, they
are the `SHA256SUMS` of the amplitude–slope package and the
`SHA256SUMS.txt` of the slowly-varying and exact-degree packages; the
signed-condensation and second natural-boundaries packages had none. From
the seventh, it is the `SHA256SUMS` of the lower-endpoint package; the
moment-determinacy package had none. From the eighth, they are the
`SHA256SUMS` of the exact-type and path-sensitive packages and the
`SHA256SUMS.txt` of the Hahn–Dulac package; the other five had none. From
the ninth, it is the `SHA256SUMS.txt` of the triangular package. The tenth
delivery's package had none. From the eleventh, it is the `SHA256SUMS.txt`
of the factorial-transseries package. From the twelfth, they are the
`SHA256SUMS` of the abelian-squares and Catalan-recurrence packages and the
`MANIFEST.sha256` of the Bessel package. The READMEs of the
inverse-harmonic, moving-fold, certified-inversion, Stokes-transport,
action-accumulation, near-linear and critical Hahn packages, and of the five
fourth-delivery and five fifth-delivery packages that had one, now record
that retirement instead of listing the ledger; those of the regularity,
gamma-core, direct-truncation and finite-core packages never mentioned
theirs, and those of the three sixth-delivery packages that had one now
record it too, as does, since its editorial pass, that of the
factorial-transseries package.
The build records of the Hahn–Fuchsian, microscopic-condensation and
weighted-type packages carry digests of their own PDF and source; they were
recomputed for the amended source and the rebuilt PDF, match the filed files
and are kept as data, and any later rebuild makes the PDF digest stale,
since pdfTeX embeds the build date. The exact-degree package's
`notes/validation.json` likewise carries digests of its own PDF and source,
recomputed for the amended source and the rebuilt PDF; they match the filed
files. The finite-core package's
`data/build_quality.json` keeps the digests and page count of the delivered
PDF and source, and other build and quality receipts, such as the
direct-truncation package's `verification/pdf_audit.json`, likewise describe
the delivered builds, as their package READMEs say. The lower-endpoint
package's README now records the retirement of its ledger; its
`notes/build_report.json` is kept as data, and its digests of the
verification program and results still match, while those of the source
and PDF describe the delivered build, as the README says. Of the eighth
delivery, the exact-type, path-sensitive and Hahn–Dulac READMEs now record
the retirement of their ledgers. The build reports of the exact-type,
path-sensitive, Hahn–Dulac and convergence-locus packages carry digests of
their source and PDF, recomputed for the filed files (with an
`editorial_rebuild` field), and all but the path-sensitive one also of
their program and results, recomputed where the program was amended; all
match the filed files. The subexponential-cost package's
`data/build_validation.json` records only its page count, recomputed, and
checks. The triangular README now records the retirement of its ledger,
and the digests of its own source and PDF in `notes/validation.json` were
recomputed for the amended source and the rebuilt PDF; they match the
filed files.
The finite-jet package's `data/build_validation.json` carries digests of
its source and PDF; they were recomputed for the amended source and the
rebuilt PDF and match the filed files.

Fifty-eight CSV tables written with CRLF line endings were normalized to LF
on filing: the reversion package's `numeric_checks.csv`, the regularity
package's `data/quadratic_*.csv`, the Stokes-transport package's
`figures/fold_scaling.csv`, the theta-resolved package's four `data/*.csv`,
the spectral package's three `data/*.csv`, the negative-ray package's
`data/majorant_diagnostics.csv`, the finite-core package's five
`data/*.csv`, the critical Hahn package's five `data/*.csv`, the arithmetic
package's two `verification/*.csv`, the optimal-truncation package's
`results.csv`, the microscopic-condensation package's two `data/*.csv`, the
Poisson-layer package's two `verification/results/*.csv`, the
sectorial-summability package's five `data/*.csv`, the weighted-type
package's two `data/*.csv`, the confluent package's two
`data/*_diagnostics.csv`, the quadratic-inverse package's two
`verification/results_a*/diagnostics.csv`, the stable–Gaussian package's
three `data/*.csv`, the signed-inversion package's
`data/diagnostics.csv`, the slowly-varying package's three
`verification/*.csv`, the signed-condensation package's six `data/*.csv`,
the second natural-boundaries package's three `data/*.csv`, and the
subexponential-cost package's two `data/recorded/*.csv`. Since the
editorial pass, every file that a program of the six deliveries writes
itself is written with LF line endings on every platform, so a rerun no
longer reintroduces CRLF. The slowly-varying package's filed
`verification/results.json` has no final newline, as delivered; its
program now writes one. The seventh delivery has no carriage return in any
file, and its programs write LF line endings on every platform. The
eighth delivery has no other carriage return, and since its editorial pass
all its programs write LF on every platform. The ninth
delivery has no carriage return in any file, and its program writes LF
line endings on every platform.
The tenth delivery has no carriage return in any file either, and since
its editorial pass its two programs write LF on every platform (as
delivered, their JSON and TeX outputs used the platform's line endings,
CRLF on Windows; the diagnostics CSV was always LF).
The eleventh delivery has no carriage return in any file, and since its
editorial pass its program writes LF on every platform (as delivered, it
used the platform's line endings, CRLF on Windows).
The twelfth delivery has no carriage return in any file; as delivered, its
programs use the platform's line endings (CRLF on Windows), so their byte
comparisons fail on Windows until an editorial pass makes them write LF.

The inverse-harmonic package's `verification/run.log` and
`verification/certification.log` are byte-identical to its `results.json`
and `certificates.json`. The spectral package's `data/contour_check.log` and
`data/verification.log` are recorded program output; the direct-truncation
package's `verification/run.log` is recorded program output, its
`verification/symbolic_run.log` is byte-identical to `amplitudes.json`, and
its `verification/latex_build.log` is the pdfTeX log of its delivered PDF.
The optimal-truncation package's `exact_checks.log`, `symbolic_checks.log`
and `verification.log` are recorded program output, as is the
signed-inversion package's `data/run.log`. All eleven were added past the
`*.log` ignore rule.
The sixth delivery has no `.log` file; the second natural-boundaries
package's `data/run_output.txt` is its redirected program output and is
byte-identical to its `data/verification.json`. The lower-endpoint package
of the seventh delivery adds a twelfth, `data/run.log`, the recorded output
of the run that wrote its `data/` files (with `--output data`, as its
README now says; the documented command writes under `build/`), likewise
added past the rule. The eighth delivery has no `.log` file. Nor has the
ninth. Nor has the tenth, nor the eleventh.

No `build.sh` reruns a verification program in place any more. Those of the
arithmetic, resonance-block, non-Archimedean reversion and Stokes-transport
packages write fresh output under an ignored `build/` directory, and the
arithmetic package's script only compares the regenerated table with the one
embedded in `arithmetic_transseries.tex` and stops if they differ, instead
of splicing it into the source. Partial and nondefault runs no longer
replace recorded outputs: the logarithmic-endpoint and stable–Gaussian
programs write a run with another `--max-n` into `data/max-n-<N>/`, the
natural-boundaries program writes by default into `rerun/`, the
quadratic-inverse program without `--out` into `verification/rerun_a<a>/`,
the quick, exact-only or other-precision runs of the moving-fold,
sectorial-summability, Gaussian-binomial and direct-truncation programs
into separate files or directories, and a bare run of the regularity
program now uses the recorded order. The recorded commands themselves, and
the `verify` targets of the Makefiles, still regenerate the recorded
outputs in place; the confluent
program writes into `data/` (including both tables its article inputs)
unless given `--output-dir`, and a run of a single part adds a new
`data/run_<part>.json`. The stable–Gaussian default run still needs an
extended-range `long double`; it now writes `data/run_summary.txt` itself
after a successful run, instead of having a redirection truncate it. Run the
programs on a copy, or with an output directory where they offer one.
The programs of the sixth delivery now write into `rerun/` by default and
need `--overwrite-recorded` to touch recorded outputs, and so do the
`verify` targets of its two Makefiles (the slowly-varying `make_tables.py`
takes `--input`); the signed-condensation default degree is now 320, that
of its recorded run. Its `build.sh` scripts and the Makefiles' `pdf`
targets only run pdfLaTeX (the exact-degree and second natural-boundaries
scripts leave `build-pass-*.log` files, which are ignored).
The lower-endpoint `verify.py` is as delivered. It writes into
`build/verification` below the working directory unless given `--output`,
so from the package root it leaves `data/` alone; its `make_figures.py` now
writes under `build/` and overwrites the shipped figures and
`data/figure_curve.json` only with `--output-dir .`. On Windows, where
NumPy's `longdouble` is double precision, a rerun reproduces the recorded numbers only up to the last
digits, although the build report records a byte-identical rerun on the
delivering platform. The moment-determinacy `verify.py` writes
`verification_results.json` into the working directory by default, so its
README's command run from the package root rewrites the recorded file
(with identical bytes at the recorded precision); a run at another `--dps`
without `--output` now writes `verification_results_dps<N>.json`. Both
`build.sh` scripts only run pdfLaTeX (the lower-endpoint one under
`build/`, then copying the PDF over `article.pdf`).
Since the eighth delivery's editorial pass, its programs write by default
under `build/` (the exact-type program below the working directory, the
others below their package) or, for both subexponential-cost programs,
into `data/rerun`; the Cauchy-cutoff, uniform-coefficient, critical-line,
path-sensitive, Hahn–Dulac and convergence-locus programs refuse to write
their recorded outputs without `--overwrite-recorded`. The
subexponential-cost default order is now 45, that of its recorded run, and
its diagnostics still need an extended-range `long double` and stop on
Windows; on Windows the Cauchy-cutoff numbers reproduce only to about
thirteen digits. The uniform-coefficient `make_tables.py` still rewrites
both table inputs from the recorded results, and its `build.sh` runs it
only with `--tables`. The triangular program writes into `rerun/` by
default (`--output-dir`) and refuses `verification/` itself unless given
`--overwrite-recorded`; a rerun of the amended program reproduced both
recorded files byte for byte; `rerun/` is not ignored, so delete it
afterwards. Its `build.sh` runs pdfLaTeX under the
ignored `build/` and copies the PDF over the filed one.
The finite-jet programs write into `data/rerun/` by default
(`--output`); only an explicit `--output` into `data/` overwrites
`data/verification.json` or `data/diagnostics.csv`,
`data/numeric_validation.json` and `data/numerical_table.tex` (the
article does not input the table; it embeds a copy), as the delivered
defaults did; `data/rerun/` is not ignored, so delete it afterwards. Its
diagnostics use double precision, not an extended `long double`, and run
on Windows; a rerun of the amended programs reproduced
`data/verification.json` and `data/numerical_table.tex` byte for byte and
the other recorded values to a relative difference below `10^{−12}`.
The factorial-transseries `verify.py` writes into `rerun/` by default
(`--output`); only `--output verification_output.txt` overwrites the
recorded file, as the delivered default did; `rerun/` is not ignored, so
delete it afterwards. Its symbolic stage takes minutes: on filing it did
not finish within 170 seconds, twice, and was not run to completion, so
allow more than three minutes for a full run. The four `PASS` lines at the head of
the recorded `verification_output.txt` are fixed text written with the
tables, so the file alone is not evidence that this stage ran; the amended
program reproduced the file byte for byte with the stage skipped, and the
coefficient lists the stage asserts were reproduced independently in exact
rational arithmetic (see the package README).

See [`../MANIFEST.md`](../../../FabiusFunction/docs/semi-formalized-research-frontiers/drafts/MANIFEST.md) for the group record.
