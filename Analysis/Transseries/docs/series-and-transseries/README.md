# Series and transseries

This group holds two documents: the canonical volume, and the companion
volume on combinatorial transseries consolidated from the three arrivals of
2026-09-04 (see the end of this file). Beside them are thirty-four unmerged
arrivals of 2026-09-29, each filed whole with its PDF and then amended
editorially (see "Arrivals of 2026-09-29" below).

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

## Arrivals of 2026-09-29 (unmerged)

Thirty-four research packages arrived through the repository drop zone
`docs/incoming/` on 2026-09-29, in five deliveries (its batches 45 to 49).
Each is filed whole, with its PDF, verification program and recorded
outputs, in a directory named after the document. None has been reviewed
claim by claim, and none is merged into either volume; merging is deferred.
None contains Lean, and none of its statements is formalized. Ten of the
first twelve were written against the tree before the transseries split
and cite the volumes under
`Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/series-and-transseries/`;
the passages they cite are unchanged here apart from that path. The
gamma-core and residue-obstruction articles, and all articles of the third
to fifth deliveries, cite the current paths. No article of the first two
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
expansions.

All thirty-five packages, the Fekete one included, were then amended in
place by an editorial pass on 2026-09-29. Unnumbered "Editorial note
(ProveIt, 2026-09-29)" blocks, which leave each article's own numbering
unchanged, record corrections, related repository results that the author
did not cite, and later packages that answer or overlap its questions. The
verification programs now write LF line endings and keep partial reruns
away from the recorded outputs, retired checksum ledgers are no longer
listed, figures with Type 3 fonts were regenerated, and every PDF was
rebuilt from its amended source. Every change to an article source is
marked by a `% ed.` comment, each package README lists its amendments, and
the delivered archives remain in the repository history
(`docs/incoming/README.md`, batches 45 to 49). Page and line counts and line
citations below refer to the amended files; the volumes are unchanged.

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
Transseries* (25-page A4 PDF, 1,788-line source, an exact standard-library
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
resonances* (26-page A4 PDF, 1,624-line source, an exact-rational check
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

[`Finite_Core_Universality_Exponential_Feedback/`](Finite_Core_Universality_Exponential_Feedback/)
holds *Finite-Core Universality and Sharp Large Order for Countable
Exponential-Feedback Transseries* (27-page A4 PDF, 2,098-line source, exact
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
Transseries* (24-page A4 PDF, 1,655-line source, an exact-rational check
program with rational enclosures, and a majorant diagnostic). The
regularity article proves neither a uniform Gevrey remainder nor a
directional Borel summation (its `README.md`, and the questions at
`article.tex:1445-1452` and `:1607-1619`). For unit amplitudes and any
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
Sector Asymptotics, and Sharp Action Budgets* (25-page A4 PDF, 1,799-line
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
records it.

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
that article asks for at `:1773-1785`), the Borel equivalent and the value
of the least term. Negative-direction summability, an analytic remainder
theorem and the inverse series are not claimed.

[`Poisson_Layers_Finite_Core_Boundary/`](Poisson_Layers_Finite_Core_Boundary/)
holds *Poisson Layers at the Finite-Core Boundary of Exponential-Feedback
Transseries* (20-page A4 PDF, 1,433-line source, an exact-rational check
program with 288 assertions, and NumPy/SciPy saddle and coefficient
diagnostics). It continues the finite-core article's questions on the
finite background cloud and on critical boundaries
(`Finite_Core_Universality_Exponential_Feedback/article.tex:1746-1785`), for
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
(`Exponential_Feedback_Regularity_Classification/article.tex:1607-1619`)
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
(23-page A4 PDF, 1,727-line source, a standard-library exact-rational check
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
and differential transcendence are not claimed.

[`Logarithmic_Critical_Endpoint_Lambert_Charts/`](Logarithmic_Critical_Endpoint_Lambert_Charts/)
holds *The Logarithmic Critical Endpoint: Convergent Lambert Charts,
All-Order Sector Laws, and Sharp Action-Cutoff Corrections* (29-page A4
PDF, 1,950-line source, exact symbolic checks, and floating-point
diagnostics through sector index `n = 65536` checked against an 80-digit
recurrence). It treats the upper endpoint `α = 2` of the critical Hahn
article above, weights `a_j = a j^{−3}` outside a finite prefix, and
answers the fixed-endpoint half of that article's Question 4
(`Critical_Hahn_Transseries_Beyond_Finite_Action_Folds/article.tex:1502-1507`);
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
(`:1551-1556`); a leading-order extension covers `a_j ~ a j^{−3}(log j)^r`,
`r ≥ −1`. Its constants agree with the `α → 2` limits of the critical Hahn
article's normal form, budget and fold drift. The Gaussian and
extreme-value mechanism is credited to Janson. Numerical values are
diagnostics, not interval certificates, and no certified cutoff algorithm
is claimed.

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
Budgets* (24-page A4 PDF, 1,705-line source, an exact SymPy check program
with 160-digit inverse-chart and floating-point coefficient diagnostics).
It treats the joint limit that the two endpoint articles above leave open:
the upper endpoint of the critical Hahn article's Question 4
(`Critical_Hahn_Transseries_Beyond_Finite_Action_Folds/article.tex:1502-1507`)
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
Windows.

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

[`Quadratic_Exponential_Feedback_After_Reversion/`](Quadratic_Exponential_Feedback_After_Reversion/)
holds *Quadratic Exponential Feedback after Reversion: Cancellation,
Finite-Core Universality, and Sharp Borel Growth* (25-page A4 PDF,
1,886-line source, exact integer recurrences through degree 240 for
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
(`Negative_Ray_Summation_Exponential_Feedback/article.tex:1423-1432`) it
answers, or the regularity article; editorial notes now relate it to
these two and to the weighted-type and signed-inversion articles. Its
forward/inverse Borel comparison
uses the finite-core article's forward theorem. At `a = 1` its diagnostic
ratio `v_n/L_n` is still 0.85 at `n = 240`; the finite checks are not
evidence of the rate.

[`Signed_Quadratic_Feedback_Inversion/`](Signed_Quadratic_Feedback_Inversion/)
holds *Signed Quadratic-Feedback Inversion: A Finite-Core Resolution and
Sharp Entire Borel Growth* (21-page A4 PDF, 1,438-line source, exact
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
rational-amplitude dichotomy* (23-page A4 PDF, 1,625-line source, an exact
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

These fifteen articles and the regularity article study one kernel,
`U = Σ c_j q^j exp(λ_j U)`, in complementary regimes, and form one unit for
the deferred merge; the regularity article is its host, and the critical
Hahn article also joins the moving fold. Four pairs overlap, and later
articles complete earlier ones. The logarithmic-endpoint and marginal
articles prove the same endpoint core; the logarithmic-endpoint article,
which covers more of the critical Hahn article's questions, is the natural
base, the marginal article's certificate and budget sections enter beside
it, and the confluent and stable–Gaussian articles supply, independently,
the crossover through `α = 2` (the second one order further in a bounded
window, the first at any rate). For eventually exact `j²` the
microscopic-condensation article's coefficient theorem is the finite-core
article's, and the quadratic-inverse and signed-inversion articles are two
independent claimed proofs of that article's conjectured inverse law,
under different hypotheses. The negative-ray and
sectorial-summability articles complement each other: fine summability at
order one in the first, remainders of every Gevrey order and summability
of every order `k > 1` in the second; the natural-boundaries article shows
that for `λ_j = j²` summability at order one cannot be angular. Their
notations collide (`a` is the first amplitude, the slope constant or the
amplitude constant; the inverse is `Q`, `V̂`, `Q` with coefficients `q_n`,
or `V` with coefficients `v_n`; the endpoint articles use different
logarithms, the two crossover articles write `α = 2 − ε`, and the
inverse exponent is `(d − μ)/a` or `−b`), so a notation
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
Stokes actions, and nonlinear inversion* (26-page A4 PDF, 1,799-line
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
Stokes-transport and moving-fold articles.

These four articles, the inverse-harmonic article and the Stokes-transport
article form one unit for the deferred merge. The direct-truncation
article covers every truncation ratio and is the natural base for the
direct result, which the spectral and optimal-truncation articles prove
again by other routes. The spectral article's Borel boundary data and
transfer theorem, the optimal-truncation article's general cutoff theorem,
corrected averages and enclosures, the Stokes-transport theorem for several
actions and the resonance-block estimate enter as further sections. The two
direct-truncation articles use different normalizations of the density and
of the contour correction; the optimal-truncation article uses the
direct-truncation article's `σ` and index.

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
Transseries* (27-page A4 PDF, 1,196-line source, an exact-rational block
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
a summability-threshold crossover* (24-page A4 PDF, 1,615-line source,
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
Jordan chains (`residue_fredholm.tex:1040`, `:1065-1067`): it is the
nilpotency index of `B = N + ΣR_ρ`. It is the depth-0 counterpart of that
article, not its generalization: the article above needs depth `n ≥ 1`, and
forced equations, iterated-logarithm coefficients and nonreal spectrum are
not treated here. Its constants lemma is the depth-0 case of the canonical
volume's `plt:thm:ext-tower-strict` (`transseries_and_inversion.tex:29092`),
which it could not read; an editorial note now cites it. The two articles
form one unit for the deferred merge, on linear differential equations over
Hahn fields; their conventions (large variable there, small `x` here) need a
dictionary first. It cites the Neumann declarations of
`TransseriesWellBased.lean` and the module
`TransseriesBlockAntiderivative.lean` as related only.

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
negative-ray and sectorial-summability articles are majorants, and the
microscopic-condensation article's least term is not a remainder estimate;
none of these is a sharp instance.

Twenty-one checksum ledgers were verified in full on filing and not filed.
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
the quadratic-inverse and stable–Gaussian packages. The READMEs of the
inverse-harmonic, moving-fold, certified-inversion, Stokes-transport,
action-accumulation, near-linear and critical Hahn packages, and of the five
fourth-delivery and five fifth-delivery packages that had one, now record
that retirement instead of listing the ledger; those of the regularity,
gamma-core, direct-truncation and finite-core packages never mentioned
theirs. The build records of the Hahn–Fuchsian, microscopic-condensation and
weighted-type packages carry digests of their own PDF and source; they were
recomputed for the amended source and the rebuilt PDF, match the filed files
and are kept as data, and any later rebuild makes the PDF digest stale,
since pdfTeX embeds the build date. The finite-core package's
`data/build_quality.json` keeps the digests and page count of the delivered
PDF and source, and other build and quality receipts, such as the
direct-truncation package's `verification/pdf_audit.json`, likewise describe
the delivered builds, as their package READMEs say.

Forty-four CSV tables written with CRLF line endings were normalized to LF
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
three `data/*.csv`, and the signed-inversion package's
`data/diagnostics.csv`. Since the editorial pass, every file that a package
program writes itself is written with LF line endings on every platform, so
a rerun no longer reintroduces CRLF.

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

See [`../MANIFEST.md`](../../../FabiusFunction/docs/semi-formalized-research-frontiers/drafts/MANIFEST.md) for the group record.
