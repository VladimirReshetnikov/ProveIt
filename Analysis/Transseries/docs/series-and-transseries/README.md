# Series and transseries

This group holds two documents: the canonical volume, and the companion
volume on combinatorial transseries consolidated from the three arrivals of
2026-09-04 (see the end of this file). Beside them are six unmerged
arrivals of 2026-09-29, each filed whole with its PDF (see "Arrivals of
2026-09-29" below).

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

Six research packages arrived through the repository drop zone
`docs/incoming/` on 2026-09-29 (its batch 45). Each is filed whole, with its
PDF, verification program and recorded outputs, in a directory named after
the document. None has been reviewed claim by claim, and none is merged into
either volume; merging is deferred. None contains Lean, and none of its
statements is formalized. All six were written against the pre-split tree,
so they cite the volumes under
`Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/series-and-transseries/`;
the passages they cite are unchanged here apart from that path.

[`Support_Controlled_Reversion_One_Exponential/`](Support_Controlled_Reversion_One_Exponential/)
holds *Support-Controlled Reversion and the Exact One-Exponential
Substitution Group* (23-page A4 PDF, 1,559-line source, an exact SymPy and
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
large-sector crossover, and resonant action splitting* (24-page A4 PDF,
1,661-line source, an exact SymPy and 100-digit check program). It
continues the reversion article directly above, filed with it. It answers
that article's Research question 11.8 ("Sharp complex transition near the
core critical point", `reversion_and_one_exponential.tex:1459-1465`) for
`δ + log(1 + δ/w) + wz e^{−δ} = 0` in the independent-parameter local chart.
The results are an exact holomorphic two-sheet atlas, the moving critical
value `z_c(s) = s²/2 + s³/3 + 5s⁴/8 + ⋯` (`s = w + 1`), all-order profiles
with a geometric error bound at the branch point, and the crossover
`a_n(τ/n)/a_n(0) → e^{−2τ/3}`. For analytic folds driven by finitely many
exponential actions (the article's question on several actions and
resonances, `:1396-1404`) it gives a convergent, resonance-aware
representation with a finite positive support grid. The fixed-coupling
specialization `z = e^{−w}/w` at its core critical point is explicitly not
covered. It read the reversion article from Vladimir's library before
either was filed, and cites
`Analysis/FabiusFunction/Lean/FabiusFunction/QuadraticCoreCatalan.lean`
(the finite Catalan core of the volume's `p6:prop:quadratic-core-catalan`)
as related finite algebra only.

[`Exponential_Feedback_Regularity_Classification/`](Exponential_Feedback_Regularity_Classification/)
holds *A Sharp Regularity Classification for Countable Exponential-Feedback
Transseries* (23-page A4 PDF, 1,659-line source, an exact standard-library
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

[`Uniform_q_Multinomial_Certified_Inversion/`](Uniform_q_Multinomial_Certified_Inversion/)
holds *Uniform q-Multinomial Transseries and Certified Inversion* (24-page A4
PDF, 1,521-line source, a 240-digit mpmath check program that also writes
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
(22-page A4 PDF, 1,495-line source, an exact SymPy and 110-digit check
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
(`q3:thm:double-scaling`), which neither article cites.

[`Inverse_Harmonic_Stokes_Transport/`](Inverse_Harmonic_Stokes_Transport/)
holds *Exponential Accuracy and Stokes Transport for Inverse Harmonic
Transseries* (23-page A4 PDF, 1,119-line source, a 190-digit check program,
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

The four remainder articles (q-multinomial, Gaussian binomial, inverse
harmonic and moving fold) are sharp instances of the canonical volume's
`p0:thm:optimal-truncation` (`transseries_and_inversion.tex:39359`). Their
inverse enclosures use the mechanism that
`Fabius.exists_eq_in_residual_interval`
(`Analysis/FabiusFunction/Lean/FabiusFunction/MeanValueBracket.lean`)
machine-checks. None of them cites either.

The packages retain their delivered layouts. Four checksum ledgers were
verified in full and not filed: the two `SHA256SUMS.txt` of the regularity
and inverse-harmonic packages and the `SHA256SUMS` of the moving-fold
package. Those packages' READMEs still mention them. The three CRLF CSV
tables (the reversion package's `numeric_checks.csv` and the regularity
package's `data/quadratic_*.csv`) were normalized to LF on filing. The
inverse-harmonic package's `verification/run.log` and
`verification/certification.log` are byte-identical to its `results.json`
and `certificates.json`, and were added past the `*.log` ignore rule.

See [`../MANIFEST.md`](../../../FabiusFunction/docs/semi-formalized-research-frontiers/drafts/MANIFEST.md) for the group record.
