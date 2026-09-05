# Series and transseries

This group holds two documents: the canonical volume, and the companion
volume on combinatorial transseries consolidated from the three arrivals of
2026-09-04 (see the end of this file).

The authoritative live Lean inventory and zero-gap result are computed by
`scripts/doc_audit.py` and pinned in `docs/doc_audit_baseline.json`; the
970/12,051 and 967/12,001 inventories are historical checkpoints.
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

> [`Transseries_And_Inversion/`](Transseries_And_Inversion/) —
> *Transseries: the polynomial–logarithmic calculus, series reversal at
> infinity, and the inversion of rapidly growing functions*. The local
> 704-page and incoming 711-page A4 PDFs are historical publication
> checkpoints. The incoming branch later reached 55,985 source lines and 3,125
> distinct labels, and the merged canonical source is newer still. No current
> source-size, label-count, or TeX/PDF parity claim is made; a fresh render is
> pending.

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

[`Combinatorial_Transseries_Inverses/`](Combinatorial_Transseries_Inverses/)
is *Combinatorial Transseries and Their Inverses: Gamma quotients, finite
exponential sums, moment sectors, moving saddles, arithmetic sheets, and
q-products* (127 A4 pages; 5,616 source lines; nine parts, 20 chapters;
21 theorems, 10 propositions, 4 lemmas, 4 corollaries, every one with a
proof; loads `docs/fabius-notation.tex`; labels `ct:` for the merge and
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

See [`../MANIFEST.md`](../MANIFEST.md) for the group record.
