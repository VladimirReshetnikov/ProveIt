# Expanding Polynomial Dynamics over Surreal and Surcomplex Fields

**Exact symbolic fibers and the order-unit obstruction**
Single-source research report, 22 September 2026, prepared for Vladimir
Reshetnikov. It is placed from one AI-assisted manuscript, whose PDF metadata
say it was prepared with ChatGPT. The manuscript is pinned to repository
revision `a3124af`.

```
article.tex         the report, standalone LaTeX with an internal bibliography
article.pdf         the compiled report, 32 pages (title, contents, 30 numbered pages)
README.md           this guide
RESEARCH_STATUS.md  the manuscript's own audit note, kept as delivered
code/verify.py      the exact finite checks (Python 3.10+, standard library only)
code/Makefile       the delivered Makefile; run it from this directory, see below
data/verification.json  the recorded run of code/verify.py (38,139 checks, PASS)
```

Every label in `article.tex` carries the prefix `epd:`. No label of any other
report was renamed. `code/verify.py`, `code/Makefile`, `data/verification.json`
and `RESEARCH_STATUS.md` are byte-identical to the delivered files. The
delivered Makefile sat at the package root and now sits in `code/`. The
delivered PDF and README are not shipped. The PDF here is rebuilt from
`article.tex`.

## Provenance: one manuscript, not a merge

The report comes from the fifth manuscript of the collection's eighteenth
incoming batch (archive `surreal_symbolic_dynamics`). It has 24 pages and
40 theorem-like environments. There was no second source, and nothing was
selected: every theorem, proof, example, question and limitation is kept.
Section 1.3 lists what the placement changed:

1. It prefixed the labels with `epd:`.
2. It renamed one term, described below.
3. It added cross-notes to other reports (Section 1.4, Remark 12.3) and a
   pointer to the collection's Lean proof of the positive-support lemma
   (Section 13.3).
4. It adapted the reproduction instructions to the placed layout
   (Section 13.2).
5. It collected all non-claims in Appendix C.

At placement, no hypothesis, statement or proof was altered beyond the change
of word. The later proof review clarified degree preservation and formal
substitution, expanded noncompactness, separated the rank-one comparison
from the order-unit theorem, and updated Lean coverage.

The report is filed under `surcomplex` although the archive name says
*surreal*. Its theorems hold uniformly for `k = R` or `C`, and its explicit
theorem is stated in `No[i]`. **The real case stays explicit.** For `k = R`
the hypothesis asks for real, distinct residue roots. The centers of
`F(x) = ω(x² − 1)` are real surreal numbers, and the fibers in `No` are
obtained with real infinitesimal errors.

**Terminology (Remark 2.2).** The manuscript called an order unit a
*cofinal scale* and spoke of the "cofinal" and "noncofinal" cases.
`entire-functions-at-arbitrary-rank` reserves *cofinality* for `cf(Γ)`
(`ent:rem:one-name`), so this report says **order unit** throughout.
`ent:def:order-unit` is the same notion. The theorem the manuscript called
the "cofinality dichotomy" is now the **order-unit dichotomy**, and the
subtitle changed the same way. Where *cofinality* still occurs in the
report, it means `cf(Γ)`, apart from quotations of the manuscript.
`RESEARCH_STATUS.md` is kept as delivered and still uses the manuscript's
words.

## What the report claims

Let `K = k((t^Γ))` with `k = R` or `C` and `Γ ≠ 0` any set-sized ordered
abelian group. Divisibility is not assumed, and neither is algebraic
closedness. Let `F = q⁻¹P` with `κ = v(q) > 0`, where `P` is integral,
`deg P = deg P₀ = d ≥ 2`, and its reduction `P₀` has `d` distinct roots
`c_i ∈ k`. The degree condition matters: with `q = t` and
`P = (X²−1)(1+tX)`, the reduction still has two simple roots, but
`−t⁻¹ ↦ 0 ↦ −t⁻¹` is a cycle containing a nonintegral point.
Set `I_κ = {h : v(h) > nκ for every n ∈ N}` and
`B_int(F) = {x : Fⁿ(x) ∈ O for all n}`.

- **Universal centers (Theorem 4.1).** Every word `s ∈ {1,…,d}^N` has a
  canonical center `x_s` with `F(x_s) = x_{σs}` and itinerary `s`. It is
  built by finite-parameter formal algebra and strong Hahn evaluation, and
  all centers share one support certificate.
- **Exact fibers (Theorem 5.1, Corollaries 5.2–5.3).**
  `B_int(F) = ⊔_s (x_s + I_κ)`. Inside a fiber,
  `v(Fⁿ(x_s+h) − x_{σⁿs}) = v(h) − nκ`. Itineraries that first differ at
  index `m` give points at valuation distance exactly `mκ`. A word
  determines a unique point **if and only if `κ` is an order unit**
  (Lemma 2.3: `I_κ = 0` exactly then).
- **Preperiodic rigidity (Theorem 6.1, Proposition 6.2, Corollary 6.3).**
  The preperiodic points are exactly the centers of eventually periodic
  words. Every `F^{m+p} − F^m` splits in `K` with `d^{m+p}` simple roots, and
  `#Fix(F^p) = d^p`. The multipliers have valuation `−nκ`. The Möbius
  counts and the zeta series are the classical full-shift formulas.
- **Order-unit dichotomy (Theorem 7.1).**
  - If `κ` is an order unit, `s ↦ x_s` is a homeomorphism from the full
    shift onto a compact perfect set, and no point has equicontinuous
    iterates.
  - Otherwise the fibers are open, every subset of the center set is closed
    and discrete, and the itinerary map is continuous but not a quotient
    map. The iterates are uniformly equicontinuous on `B_int`.
  - Proposition 7.4: the Hausdorff quotient of the `κ`-scale uniformity is
    the full shift, with entropy `log d`.
- **Compact-subsystem rigidity (Theorem 7.5).** If `κ` is not an order unit,
  every compact forward-invariant subset of `B_int` is finite and consists of
  preperiodic centers.
- **Scalar extension (Theorem 8.1, Example 8.2).**
  - The centers do not change under `Γ ↪ Δ`, and new fibers appear.
  - Preperiodic points over any field extension already lie in `K`.
  - If `κ` stops being an order unit, the new nonescaping points are
    transcendental over `K`, and the two topologies differ.
- **Deformations (Theorem 9.1, Corollary 9.3).** A perturbation `D` with
  `θ = min v(d_j)` moves every center by valuation at least `θ`, and the
  leading response is given exactly. Perturbations in `I_κ` leave every
  labelled fiber unchanged but move the fixed points.
- **Bounded orbits (Theorem 10.1, Corollary 10.2).** The theorem gives an
  exact formula for the valuation-bounded locus: it is `B_int` together with
  the points for which `κ + α(x)` is not an order unit. When `Γ` has an order
  unit but `κ` is not one, the corollary identifies it with a coarsened
  valuation ring.
- **No order unit (Proposition 11.1, Theorem 11.2, Corollary 11.4).** The
  following are equivalent:
  1. `Γ` has no order unit;
  2. every orbit of every polynomial is valuation-bounded;
  3. the iterates of every polynomial are locally equicontinuous everywhere.

  Corollary 11.4 then gives `J_aff,v(f) = ∅`. This concerns only the affine
  set of Definition 11.3.
- **Surreal specialization (Theorem 12.1, Corollary 12.4).** For
  `F(x) = ω(x² − 1)`, the locus whose every iterate is finite in `No[i]`
  is `⊔_s (x_s + I)`,
  where the `x_s = Σ a_n(s) ω^(−n)` are real and `ω^(−ω) ∈ I`. Every
  surcomplex preperiodic point is a real center. Every polynomial orbit over
  `No` or `No[i]` is bounded, and the iterates are locally equicontinuous in
  the fine uniformity.

The manuscript proposes as new the arbitrary-rank combination of these
statements: exact fibers, the order-unit/topology dichotomy, compact
rigidity, and the extension and deformation consequences.

## What the report does not claim

Appendix C lists **28 source non-claims (S1–S28)** and **3 placement
non-claims (P1–P3)**. In brief:

- The report is an unrefereed, AI-assisted draft. Priority is **not
  certified**: the search was targeted, incomplete and sometimes noisy. No
  named published conjecture is claimed solved. The three questions of
  Section 14 are proposed continuations, not established open problems.
- Lean coverage is partial: [the ledger](../../FORMALIZATION.md) maps
  Definition 2.1 and Lemma 2.3 to
  [ScaleIdeal.lean](../../../Surreal/HahnSeries/ScaleIdeal.lean), including
  the convex subgroup, error ideal, order-unit criterion and coarsened
  valuation ring. Clopenness is encoded by valuation-ball conditions.
  The positive-support lemma is also proved. The centers, fiber theorem
  and later dynamics remain pending. The source's original repository
  audit was a targeted survey, not a build or formalization.
- Classical inputs are credited, not claimed. These are Neumann's
  positive-support lemma, formal implicit functions, valuation coarsening,
  the full shift and its periodic counts, the rank-one Cantor repeller
  (Benedetto, Example 4.39), and Conway normal form.
- The hypotheses are degree-preserving, simple split reduction (repeated roots are not
  covered), finitely many coefficients and branches, and polynomials only
  (rational maps are not covered).
- **Valuation-expanding is not repelling**, and the expanding points are not
  identified with classical Julia points. `J_aff,v = ∅` says nothing about
  Berkovich or spherical Julia sets. Strong summation is not a topological
  limit. The full shift is a quotient of a coarsened uniformity, not the
  native quotient. The centers have no intrinsic uniqueness among
  set-theoretic sections. No equality is asserted when the deformation
  numerator vanishes.
- No set of all surreals is formed, and compactness in `No` refers to
  set-sized subsets.
- The 38,139 finite checks prove no infinite statement. The two center
  algorithms share their defining equation.
- **Placement:**
  - Nothing is transferred to or from the neighbouring reports below.
  - For the whole class `No[i]`, the set-level discreteness and compactness
    clauses are special cases of `a:thm:discrete`, and the novelty proposal
    concerns set-sized workspaces.
  - The order-unit dichotomy is not `ent:cor:cofinality`.

## Relation to the neighbouring reports

**[dynamics-and-normal-forms](../dynamics-and-normal-forms/)** is a
different subject. It does germ linearization at a unit multiplier, with
small divisors and coefficient categories. Its non-claims exclude global
Julia/Fatou theory on `No[i]` (N51) and attracting or repelling multipliers
(N18). **This report answers neither.** It builds no Julia/Fatou theory,
and its periodic points are valuation-expanding, not repelling. Section 1.4
records that `σ`, `κ`, `q`, "multiplier" and "Julia" mean different things
in the two reports.

**[analysis](../analysis/)** proves `a:thm:discrete`: every *set* in `No[i]`
is closed and discrete in the fine topology `a:def:fine`, with one
separating radius. The surreal-level discreteness and compactness clauses
of Theorem 12.1 are therefore special cases (Remark 12.3). Remark 12.2 is an
instance of `a:rem:notvaluation`. The substance of Theorems 7.1(b) and 7.5
lies in set-sized workspaces with their intrinsic topologies. The
equicontinuity statements over proper-class fine balls, including
Corollary 12.4, are not consequences of `a:thm:discrete`.

**[entire-functions-at-arbitrary-rank](../entire-functions-at-arbitrary-rank/)**
defines the same order unit, `ent:def:order-unit`, and reserves "cofinality"
for `cf(Γ)`. The maximal proper convex subgroup `H` of Section 10.1 is the
kernel of `ent:lem:coarsening`. That lemma is stated under the other report's
standing divisibility hypothesis, and the facts used here are proved
directly without it. The group of Example 11.5 is that report's `Γ_∞`.

**[hahn-tate-uniformization](../hahn-tate-uniformization/)**: `H_κ` is its
`H_α` (`tate:eq:H`). The two reports share a subgroup, not a theorem.

**[rank-one-berkovich](../rank-one-berkovich/)**: the order-unit case has
the same symbolic Cantor model as the classical rank-one construction.
It does not require the ambient group to have rank one: `(1,0)` is an
order unit in `Q ⊕lex Q`. In the other report's field `C((t^R))` every
positive scale is an order unit. That report has no polynomial dynamics,
and no transfer is claimed.

**[omnific-continued-fractions](../../surreal/omnific-continued-fractions/)**
(batch 33) proves a fiber theorem of the same shape for continued-fraction
digits given by the omnific floor (`ocf:thm:fiber`): each digit sequence has
fiber one point plus a convex precision ideal, and an eventually periodic
sequence is unique exactly when its period degree is an order unit
(`ocf:thm:orderunit`); under a bound on the preperiodic degrees that ideal is
`I_κ` at `κ = E`. The proofs are independent. An unnumbered note after
Theorem 5.1 records this; it changed no number and no page count.

## Build and reproduce

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The reviewed source builds to 32 pages with zero errors, zero warnings,
zero undefined references and no overfull or underfull boxes. The earlier
placement build had 31 pages. BibTeX is not needed.

**`code/verify.py` overwrites the shipped record by default.** Its only
option is `--output`, which defaults to `data/verification.json` beside
`code/`, whatever the current directory. It writes there without checking
whether the file exists, so a bare `python code/verify.py` replaces the
delivered evidence. Run it on a copy of this directory, or give an output
path outside it:

```sh
python code/verify.py --output /tmp/epd-verification.json   # run without -O
```

The delivered Makefile writes a *new* file, `data/verification-rerun.json`,
and leaves the record alone. It must be invoked from this directory:
`make -f code/Makefile verify`. Its default interpreter is `python3`; pass
`PYTHON=python` where needed.

The recorded run (Python 3.13.5) passed 38,139 exact checks. At placement the
program was rerun on Python 3.14.4 to a scratch path, and the Makefile target
was run on a copy. Both reported `PASS` with 38,139 checks. The output
matched the record in every field except the Python version and the
elapsed time.
