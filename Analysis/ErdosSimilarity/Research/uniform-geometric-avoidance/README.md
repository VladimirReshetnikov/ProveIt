# Uniform geometric avoidance

Research report on the Erdős similarity problem: one closed set of large
measure that omits infinitely many terms of every affine copy `x + s aₙ`
(`s ≠ 0`) of whole families of null sequences at once. It holds four
AI-assisted, unrefereed manuscripts. Nothing here is formalized; no Lean
development concerns the similarity conjecture.

This README is a short reconciliation note (2026-10-09). The report's
article/README write, which will print the four sources as Parts I-IV, is
still pending. Delivered files are not edited; corrections and caveats are
recorded here.

## Sources

| No. | Prefix | Manuscript | Placed |
|---|---|---|---|
| 01 | unprefixed | *Uniform avoidance of geometric progressions and exponential-polynomial patterns* (Part I) | `277e8f5101` |
| 02 | `02-balanced-recurrences-` | *A common avoiding set for stable recurrences and balanced P-recursive sequences* (`01_universal_avoidance` of `ProveIt_Research_2026-10-08 (1).zip`) | `cd984a34c0`; its notices file in `0599fe867a` |
| 03 | `03-rational-observations-` | *Large Closed Sets Avoiding All Convergent Linear Recurrences* (`recurrence_avoidance` of `ProveIt_Research_2026-10-08.zip`) | `cd984a34c0` |
| 04 | `04-supergeometric-` | *Beyond Geometric Progressions: Supergeometric Sequences and All Infinite Linear Recurrences* (`supergeometric_and_recurrence_avoidance.zip`) | `cd984a34c0` |

The TeX sources and PDFs of 02-04 (980, 1,947 and 2,145 TeX lines; 23, 28
and 28 pages) and their delivery READMEs are not staged; they are
retrievable from the arrival commit `b28d0850b3`.

## Files

**01 (unprefixed, delivered layout)**

- `uniform_geometric_avoidance.tex`, `sections/01_context.tex`,
  `sections/02_synchronization.tex`, `sections/03_routing.tex`,
  `sections/04_uniformity.tex`, `sections/05_global.tex`,
  `sections/06_algebraic_families.tex`, `sections/07_effectivity.tex`,
  `sections/08_limits_and_questions.tex`, `sections/09_appendices.tex`
- `Makefile`, `SOURCE_AUDIT.md`
- `LICENSE-APACHE-2.0.txt`, `THIRD_PARTY_NOTICES.txt` (the adapted openai/math
  family 084 routing construction, Apache-2.0; they cover 02-04 too)
- `figures/make_figure.py`, `figures/synchronized_scales.pdf`
- `verification/README.md`, `verification/verify_exact.py`,
  `verification/results.json`

**02 `balanced-recurrences`**

- `02-balanced-recurrences-SOURCE_AUDIT.md`,
  `02-balanced-recurrences-code-README.md` (delivered `code/README.md`),
  `02-balanced-recurrences-THIRD_PARTY_NOTICES.txt` (the package's Apache
  change notice)
- `code/02-balanced-recurrences-verify_exact.py`,
  `code/02-balanced-recurrences-make_sampling_figure.py`
- `data/02-balanced-recurrences-verification_results.json`,
  `data/02-balanced-recurrences-provenance.json`
- `figures/02-balanced-recurrences-signed_block_sampling.pdf`,
  `figures/02-balanced-recurrences-signed_block_sampling.png`

**03 `rational-observations`**

- `03-rational-observations-verification-PROOF_AUDIT.md`,
  `03-rational-observations-verification-README.md` (delivered
  `verification/PROOF_AUDIT.md`, `verification/README.md`)
- `code/03-rational-observations-verify_recurrence.py`,
  `code/03-rational-observations-generate_figures.py`
- `data/03-rational-observations-results.json`
- `figures/03-rational-observations-signed_terms.pdf`,
  `figures/03-rational-observations-signed_terms.png`,
  `figures/03-rational-observations-sampling_envelopes.pdf`,
  `figures/03-rational-observations-sampling_envelopes.png`
- 03's package-level audit of record (its §2 and §5) was staged with its
  sibling manuscript as
  `SetTheory/Cardinals/docs/reports/convex-geometry/optimal-simplex-products/SOURCE_AUDIT.md`.

**04 `supergeometric`**

- `04-supergeometric-THEOREM_LEDGER.md`,
  `04-supergeometric-audits-README.md`,
  `04-supergeometric-audits-budget_audit.md`,
  `04-supergeometric-audits-recurrence_audit.md`,
  `04-supergeometric-audits-recurrence_independent_audit.md`,
  `04-supergeometric-audits-source_priority_check.md`
- `code/04-supergeometric-Makefile`,
  `code/04-supergeometric-verify_routing.py`,
  `code/04-supergeometric-verify_recurrences.py`,
  `code/04-supergeometric-verify_budget_and_examples.py`
- `data/04-supergeometric-provenance.json`,
  `data/04-supergeometric-routing.json`,
  `data/04-supergeometric-recurrences.json`,
  `data/04-supergeometric-budget_and_examples.json`,
  `data/04-supergeometric-build_validation.json`,
  `data/04-supergeometric-all_recurrences_source_notes.txt`,
  `data/04-supergeometric-SHA256SUMS`

## One theorem, three independent proofs

02, 03 and 04 each prove, independently and on the same day (8 October 2026),
the same common avoiding set: for every `0 < ε < 1` one closed, symmetric,
1-periodic set of density `> 1 − ε` omits infinitely many terms of every
affine copy of every convergent, non-eventually-constant real
constant-coefficient (C-finite) recurrence, with nonreal, repeated and
colliding roots and exact zeros allowed and no spectral separation. **None
of the three cites the others**; all three are credited for this result.
The proofs share one architecture: first crossing of a state-block norm, a
large actual scalar coordinate, full polynomial sign conditions including
zero signs, the inherited routing and repair of openai/math family 084, and
dyadic assembly.

**02 is the base** (the most general proof): an abstract hitting theorem for
compact *rational* parameter families with block non-collapse (degree growth
`log Δ_N = o(N)` suffices), giving one set for every non-eventually-zero,
exponentially decaying sequence with an eventual *balanced* polynomial
recurrence (`deg A₀ = deg A_d = max deg Aᵢ`). This class strictly contains
the stable C-finite sequences (e.g. `binom(2n,n)/8ⁿ`, Catalan`/8ⁿ`,
`ρⁿPₙ(t)`). 02 also proves effectivity for rational `ε`, perfect compact
sections and a subexponential degree criterion.

What the others add beyond 02 (the intake dossier's comparison, not
re-proved here):

- **03** proves the set property for a class *incomparable* with 02's:
  quotients `aₙ/bₙ` of C-finite sequences with `aₙ → 0` not eventually zero
  and `bₙ → b_∞ ≠ 0`, hence every non-eventually-constant rational
  observation `P/Q` of finitely many convergent C-finite sequences with `Q`
  nonzero at the limit (e.g. `qⁿ/(1+qⁿ)`, which is not P-recursive). It also
  gives a quadratic Lyapunov normalization with explicit uniform constants
  `K, α, β` for all companions with roots in an annulus, without root
  separation, and sharpens Part I's obstruction: every positive-measure set
  contains a translate of some `qⁿ(1+o(1))` whose consecutive ratios tend
  to `q`. One set for the classes of both 02 and 03 is the intersection of
  the two sets (hole densities add).
- **04** proves a *sequence-dependent* supergeometric theorem: a fixed
  positive sequence with decreasing blocks of length `L_j → ∞` and maximal
  logarithmic gap `G_j = o(log log L_j)` is avoided by a closed periodic set
  of density `> 1 − ε` (e.g. `exp[−n(log log n)^γ]`, `0 < γ < 1`, and
  `exp[−n log log log n]`). The compact section of the common set meets
  every infinite-range real C-finite pattern in infinitely many omitted
  points, so a C-finite value set is measure universal iff it is finite iff
  the sequence is eventually periodic; matrix-orbit images likewise. No
  common set for all supergeometric sequences is claimed.

Not claimed by any source: the general Erdős similarity conjecture, all
P-recursive null sequences, vanishing limiting denominators, `1/n!`,
`e^{−n²}`.

## Part I's research questions

Part I lists ten questions (`sections/08_limits_and_questions.tex`). The
deliveries claim, and the intake judged (dossier138_ERDOS; not re-proved
here):

| Part I question | Status | By |
|---|---|---|
| 5 *Oscillatory recurrences* | **Answered**: everything survives for stable real recurrences with nonreal, repeated or colliding roots and exact zeros; no spectral separation is needed. Beyond C-finite: balanced P-recursive (02), quotients and rational observations (03). | 02, 03, 04 |
| 9 *Beyond contracting geometric scales* | **Partly answered**: a *fixed* supergeometric sequence with `G = o(log log L)` is avoided. Compact families of them, `1/n!` and `e^{−n²}` remain open. | 04 |
| 10 *Uniform nonlinear images* | **Possibly answered for rational `φ`** (the intake's reading, to be confirmed at the write): for nonconstant rational `φ` regular at 0, `φ(qⁿ)` is a rational observation of the convergent C-finite `qⁿ`, so 03's set avoids all of them, for all `q ∈ (0,1)` at once. Analytic `φ` stays open. | 03 |
| 6 *A parameter-complexity threshold* | **Partial**: degree growth `log Δ_N = o(N)` suffices; the positive-rate case is open. | 02 |
| 4 *Bounds near cancellations and root collisions* | **Partial**: explicit, not sharp, uniform Lyapunov constants with no root separation. | 03 |
| 3 *Infinite mixtures* | Open. | — |

The last paragraph of Part I's `SOURCE_AUDIT.md` ("Nonreal characteristic
roots and unrestricted infinite mixtures remain outside the proved
results") is true of Part I but stale for the report: 02-04 settle the
nonreal-root half. Nothing in Part I was false.

## Notation clashes between the sources

- `ρ` is the unit-interval density in all four, and also the Legendre
  damping factor in 02.
- `α, β` are ratio bounds in 01, block/decay constants in 02 and 04, and
  Lyapunov constants in 03.
- The sampling scale is `Q` in 02 and 04, `τ` in 03 (whose script calls it
  `Q`).
- `d` is the recurrence order, but the tree height in 04's budget lemma and
  the parameter dimension in its `sr:lem:block` (with `m` the block length).
- "Balanced" (02) is an ad hoc condition on the endpoint degrees, unrelated
  to balanced (Saalschützian) hypergeometric series.
- Label names collide across the four (`thm:main`, `thm:normalized`,
  `lem:signs`, `cor:convergent`, ...); the write prefixes them per Part.

## Rerunning the prefixed scripts

The prefixed scripts still name their delivered paths. Do not run them in
place with their defaults:

- `code/02-balanced-recurrences-make_sampling_figure.py` imports
  `verify_exact` and writes an unprefixed figure into `figures/`;
  `code/02-balanced-recurrences-verify_exact.py` writes
  `data/verification_results.json` relative to the working directory.
- `code/03-rational-observations-generate_figures.py` imports
  `verify_recurrence`; `code/03-rational-observations-verify_recurrence.py`
  writes `results.json` beside itself.
- `code/04-supergeometric-verify_recurrences.py` and
  `code/04-supergeometric-verify_budget_and_examples.py` default to writing
  `verification/recurrences.json` and `verification/budget_and_examples.json`
  of this report, which is **Part I's `verification/` directory**;
  `code/04-supergeometric-Makefile` names `code/verify_*.py`.

Copy the scripts to a scratch directory under their delivered names, or pass
an explicit `--output` / `--json` path outside the report. At intake all
five delivered suites were rerun this way and reproduced their records as
data. The shipped audit and README texts also cite delivery paths, not the
names above.
