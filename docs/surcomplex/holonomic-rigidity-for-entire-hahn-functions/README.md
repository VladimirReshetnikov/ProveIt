# Holonomic Rigidity for Entire Hahn Functions

**A sharp order-unit criterion for dilations, with uniform exclusion bounds,
and first-order nonlinear rigidity**
Merged research report, 22 September 2026, from three manuscripts: 08 and 09,
written independently on the same day, and 10, which adds the nonlinear part.

```
article.tex   the report, standalone LaTeX with an internal bibliography
article.pdf   the compiled report, 61 pages
README.md     this guide
08-finite-recurrences-PROOF_AUDIT.md          source 08: assumptions and critical proof steps
08-finite-recurrences-SOURCES_AND_SCOPE.md    source 08: sources, repository pin, priority limits
09-entire-hahn-holonomic-literature_audit.md  source 09: literature audit
10-nonlinear-rigidity-PROOF_AUDIT.md          source 10: dependency chain, sign checks, boundary
10-nonlinear-rigidity-SOURCES_AND_SCOPE.md    source 10: repository pin, literature, novelty limits
code/
  08-finite-recurrences-verify.py             source 08 checks (3,705)
  09-entire-hahn-holonomic-verification.py    source 09 checks (2,043)
  10-nonlinear-rigidity-verify.py             source 10 checks (2,113)
  10-nonlinear-rigidity-build.py              source 10's build script (see "Build and reproduce")
data/
  08-finite-recurrences-verification.txt, 08-finite-recurrences-build_report.txt
  09-entire-hahn-holonomic-verification_results.txt, 09-entire-hahn-holonomic-build_report.txt
  10-nonlinear-rigidity-verification.json     recorded run of the source 10 checks
  10-nonlinear-rigidity-build_report.json     build log audit of the 23-page source 10 manuscript
  10-nonlinear-rigidity-layout_audit.json     page-layout audit of that manuscript
```

Every label in `article.tex` carries the prefix `hol:`; the nonlinear part
uses the sub-prefix `hol:nl:`. The audit files and programs keep the source
numbers `08`, `09` and `10` of the batches they arrived in. The source 10
audit files use that manuscript's own notation and theorem letters (see
"Source 10" below). No source manuscript is shipped.

## Why one report

Manuscripts 08 and 09 are one report written twice. Both prove the same
holonomic rigidity theorem, the same order-unit dilation criterion, the same
finite-step escape lemma, the same partial-theta sharpness witness, and the
same explicit counterexample series. **08 is the base** because it assumes only
`Γ ≠ 0`, while 09 assumes divisibility. Every proof taken from 09 was re-read
for a hidden division before it was attached to an 08 statement. Divisibility
now enters in three threshold constructions, and each prints the hypothesis itself
(Section 1.4):

1. the refined recurrence threshold of Corollary 3.5 (`hol:cor:periodic`),
   whose divisibility-free predecessor is Corollary 3.4 (`hol:cor:boundedcost`);
2. the refined coarsened threshold in Theorem 7.4 (`hol:thm:coarse`), which
   also states the divisibility-free form;
3. the worked sparse threshold of Example 13.1 (`hol:ex:sparse`), an
   instance of (1).

The torsion eigenspace equivalence, Proposition 9.1(c), now needs no
divisibility. The review below replaces root extraction by inward stability
of strong evaluation.

The divisibility-free predecessors are weaker in the constant only, not in the
conclusion.

## Source 10: the nonlinear part

Source 10 (pinned at `048b72c`, where this report was exactly the 08+09
merge) answers the first-order case of the report's open nonlinear question,
then Question 15.1 and now Question 19.1 (`hol:q:nonlinear`). It forms
Sections 14–17, placed after the linear theory, with Theorem D in the
introduction. Its method is not the escape chain: at one large scale the
whole series leaves a finite initial polynomial, and a corner polynomial
controls its top coefficient.

- **Coefficient field.** Source 10 works over `k((t^Γ))` for any field `k`
  of characteristic zero; Sections 1–13 are stated over `C`. This generality
  is recorded for the nonlinear part only (Convention 14.1) and is **not**
  transferred to Theorems A–C, whose extension to other fields is the
  separate remark of Section 12.
- **Renamed symbols** (Section 14.1), to avoid collisions: `D, W → d_P, w_P`
  (`D_z` is the derivative), `H_P → χ_P` (`H ∈ Γ` in the linear part),
  `B_P → κ_P` (a rational cutoff, not an element of `Γ`), `r, r_0 → δ, δ_0`,
  `h_r, p_r → γ_δ, φ_δ`, `M → n_*`, `E_q → ϑ_q` (`E_η` is the formal
  exponential). Source 10's Theorems A, B, C are Theorem D,
  Theorem 16.5 and Theorem 16.1 here.
- **Printed once:** the support calculus (Lemma 2.1, Proposition 2.7), the
  cofinal-valuation criterion (Lemma 2.3(a)), the positive-support lemma
  (Lemma 2.1(2), which source 10 imports without proof), the surreal embedding
  (Section 2.4), strong entireness of `Σ ω^(−ω^n) z^n` (Theorem 11.2), its
  failure after enlarging the group (Section 11.2) and the `Γ = 0` remark
  (Section 12).

## What the report claims

Let `K = C((t^Γ))` for a nonzero set-sized ordered abelian group `Γ`, **not
assumed divisible**. *Entire* means that the evaluation family is strongly Hahn
summable at every point of this one field, not at every point of the full
surcomplex class.

- **Theorem A, differential rigidity.** Every strongly entire D-finite power
  series is a polynomial. More strongly, a fixed nonzero operator `L` has an
  exterior valuation region, computed from finitely many coefficients, on
  which strong evaluation of any formal solution already forces a polynomial
  of degree below a common bound.
- **Theorem B, the sharp dilation criterion.** For `q` of infinite
  multiplicative order, a nonpolynomial strongly entire solution of a nonzero
  linear `q`-difference equation with polynomial coefficients exists **if and
  only if** `v(q) ≠ 0` and `|v(q)|` is an order unit of `Γ`. A nonzero
  valuation is not enough in higher rank. The proof covers units whose
  residues are roots of unity. When the criterion holds, a partial theta
  series is a witness.
- **Theorem C, several variables.** A function strongly summable at every
  point of `K^d` whose mixed partial derivatives span a finite-dimensional
  space over `K(z_1, …, z_d)` is a polynomial.
- Further: mixed differential–dilation rigidity at every nonzero noncofinal
  scale (Theorem 10.2); a recurrence exclusion bound that is **attained**,
  boundary included, by a formal exponential (Proposition 5.3); a coarsened
  exclusion bound valid at every nonzero noncofinal dilation valuation (Theorem 7.4); and the exact strong evaluation domain of
  the partial theta series for an arbitrary Hahn parameter (Theorem 8.1).
- In an explicit surreal workspace with countable cofinality and no order
  unit, `Σ ω^(−ω^n) z^n` is strongly entire (Theorem 11.2) yet satisfies no
  nonzero linear differential equation and no nonzero linear dilation equation for any
  nontorsion parameter of that workspace.

The nonlinear part (source 10, Sections 14–17) works over `k((t^Γ))` for
**any** field `k` of characteristic zero:

- **Theorem D, first-order nonlinear rigidity.** For every nonzero
  `P ∈ k((t^Γ))[z, Y_0, Y_1]`, every strongly entire solution of
  `P(z, f, f') = 0` is a polynomial; for a nonpolynomial formal solution there
  is `δ_0 > 0`, depending on `P` and finitely many coefficients of `f`, with
  `t^(−δ)` outside the strong domain for all `δ ≥ δ_0`. So a nonpolynomial
  strongly entire `f` and `f'` are algebraically independent over `K(z)`.
  No separant, irreducibility or solved-form hypothesis is needed.
- The finite exclusion certificate behind it (Theorem 15.1) applies in any
  order when the residue corner polynomial `χ_P` is nonzero (Theorem 16.1,
  with degree candidates in Proposition 16.2); in order one `χ_P ≠ 0` always.
- Finite candidate degrees for polynomial solutions (Theorem 15.3) and an
  affine algebraic set parametrizing all entire solutions, stable under
  Hahn-field extensions (Corollary 15.6).
- Worked equations: two exact Riccati classifications (Proposition 15.7),
  the attained degree cutoff (Example 15.8), resonant degrees (Example 15.9),
  and the first two Painlevé polynomial equations (Proposition 16.3).
- **The exclusion bound cannot be uniform** (Theorem 15.10): the solutions
  `t^λ/(1 − t^λ z)` of `f' = f²` have exact domain `v(x) > −λ`, unlike the
  operator-only bound of Theorem A.
- **Positive-weight Euler rigidity** (Theorem 16.5): a strongly entire
  `f(x_1, …, x_m)` satisfying `P(x, f, ϑ_q f) = 0`, with
  `ϑ_q = Σ q_ν x_ν ∂_ν` and all `q_ν` positive integers, is a polynomial; zero
  and mixed weights fail (Section 16.3).
- Two-jet independence of `Σ t^(n²) z^n` over `C((t^Q))` (Corollary 17.1)
  and of `Σ ω^(−ω^n) z^n` (Corollary 17.2); characteristic zero is necessary
  even for `f' = 0` (Example 17.3).

## What the report does not claim

- The arbitrary-rank classification is offered as a **proposed original
  contribution**. Priority is not certified, no named published conjecture is
  claimed solved, and the proofs have not been independently refereed.
  The [Lean ledger](../../FORMALIZATION.md) maps the positive-support word
  lemma to [NeumannWords.lean](../../../Surreal/HahnSeries/NeumannWords.lean)
  and the escape mechanism, bounded-cost exclusion and formal exponential
  domain to [EscapeChain.lean](../../../Surreal/HahnSeries/EscapeChain.lean).
  The main classifications, the new inward-stability and torsion results and
  the whole nonlinear part remain unformalized.
- Classical material is credited, not claimed: Stanley's D-finite/P-recursive
  correspondence, Hahn–Neumann support lemmas and Higman's lemma, partial
  theta series and their functional identity, and the Conway normal-form
  identification. Ramis, Garoufalidis and Di Vizio are named antecedents;
  their conclusions are neither inferred nor strengthened here.
- `D_z` differentiates only the formal variable and kills every scalar. It is
  **not** the Berarducci–Mantova derivation, and no theorem about that
  derivation is restated as D-finite rigidity.
- Finite-order dilations are excluded from the main dilation theorem
  (Section 9). **No nonlinear differential transcendence in all orders is
  claimed.** Source 10 answers only the first-order case of the nonlinear
  question, plus the higher-order equations with `χ_P ≠ 0` and positive-weight
  Euler relations. Order two or more with a vanishing residue corner stays open
  (Question 19.1, re-scoped from what was Question 15.1); the equation
  `z²ff'' + zff' − z²f'² = 0` has polynomial solutions of every degree but is not
  a nonpolynomial counterexample (Proposition 16.4). The escape proof does not
  extend to nonlinear equations in any order. Mixed equations at unit
  valuation are also open (Question 19.4, formerly 15.2).
- The linear exclusion thresholds are explicit and uniform but need not be
  optimal; the nonlinear exclusion bound is explicit, solution-dependent, not
  optimal, and has no converse.
- The coefficient-field generality of the nonlinear part is not transferred to
  Theorems A–C.
- The nonlinear part keeps every limitation of source 10, listed as N1–N17 in
  Section 19.3: among them, the corner is not a differential Newton polygon;
  candidate degrees are necessary, not realized, and not a uniform algorithm
  for arbitrary coefficient names; the solution locus does not say the number
  of solutions is finite; `Σ t^(n²) z^n` and `Σ ω^(−ω^n) z^n` are prior
  material, only their two-jet consequences are new; independence concerns
  formal functions, not values; nothing is entire on all of `No[i]`; priority
  is provisional (targeted literature search of 22 September 2026, Hayman and
  Hu–Yang through metadata only, targeted repository comparison at `048b72c`).
- The finite checks validate coefficient conversions, identities, cancellation
  examples and finite ordered-group examples. They do not establish the
  infinite support arguments, the cofinality claims, the generic-line theorem,
  the nonexistence of annihilating operators, or any two-jet independence.

## Relation to the neighbouring reports

**[entire-functions-at-arbitrary-rank](../entire-functions-at-arbitrary-rank/)**
studies the same class of entire functions over the same kind of workspace.
None of its ring-theoretic conclusions is used here. This report cites its
order-unit coarsening lemma `ent:lem:coarsening` rather than repeating it, and
takes from it the background facts about countable cofinality and the group
`⊕_{j≥0} Q ω^j`. **The two order-unit dichotomies are not the same theorem.**
There, the order unit decides Hermite interpolation and the Bézout property of
the ring. Here, it decides which annihilating operators a nonpolynomial member
can satisfy. Neither implies the other.

**[differential-equations](../differential-equations/)** uses a derivation on
surreal *scalars*; this report does not. Its `diff:cor:riccati` solves
`∂u = 1 + u²` in `No[i]` with the same answer `±i` as Proposition 15.7 here,
but for a different derivation acting on different objects; neither implies
the other. **[rank-one-berkovich](../rank-one-berkovich/)**
already contains the quadratic-exponent example `Σ t^(n²) z^n`, so the partial
theta witness is not counted as a new function; the same series is
`found:ex:internal` in [foundations](../../foundations-and-computation/foundations/),
and only its two-jet independence (Corollary 17.1) is new here.

**[tail-spans-and-differential-transcendence](../../surreal/tail-spans-and-differential-transcendence/)**
proves all-order differential independence for particular Galois-supported
constructions, with scalar or fixed-disk analytic derivations over smaller
base fields. The nonlinear part here proves only two-jet independence, but
for every nonpolynomial strongly entire function over its full Hahn field.
Neither result weakens or rediscovers the other.

## Build and reproduce

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
python code/08-finite-recurrences-verify.py --output rerun-08.txt
python code/09-entire-hahn-holonomic-verification.py --output rerun-09.txt
python code/10-nonlinear-rigidity-verify.py --output rerun-10.json
```

The build gives 61 pages with zero errors, zero warnings, zero overfull or
underfull boxes, zero undefined references and zero duplicate PDF
destinations. All three check programs use only the Python standard library
with exact integer and rational arithmetic. Run them on a copy of this
directory. `08-finite-recurrences-verify.py` and `10-nonlinear-rigidity-verify.py`
require an explicit `--output` path, and the latter refuses an existing one,
so that a rerun cannot overwrite the delivered record. The recorded runs
passed 3,705 checks (08), 2,043 checks (09) and 2,113 checks (10, seed
20260922, six groups: 450 + 240 + 480 + 500 + 360 + 83), with no failures; a
rerun of the source 10 suite for this merge reproduced its record exactly.

`code/10-nonlinear-rigidity-build.py` was written for source 10's own
23-page manuscript. Run here, it would typeset this report instead, leave
auxiliary files in the directory and write `data/build_report.json`; the two
shipped `data/10-nonlinear-rigidity-*` build and layout audits describe that
manuscript, not this report. Use `latexmk` on a copy instead.


## Subsequent proof review

This review predates the merge of source 10; its page counts and file counts
refer to the 08+09 report.

The main support, recurrence, orbit, differential, generic-line, dilation,
theta-domain, torsion and mixed-operator proofs were read with the examples
and their downstream uses.

A new support lemma proves inward stability: if a nonzero `x` admits strong
evaluation, so does every `y` with `v(y) ≥ v(x)`. Membership of a fixed series'
domain therefore depends only on the argument valuation, and entireness can
be tested on monomials. This retains the full Hahn coefficient supports;
leading coefficient valuations alone need not determine a boundary domain.

The torsion equivalence now holds without divisible exponents. For an argument
of valuation `δ`, evaluate the outer series at `t^γ` with `γ = min(δ,0)`.
The inner series is then evaluable at `t^(mγ)` and inward stability reaches
the desired argument. No `m`th root in the Hahn field is needed.

The refined recurrence statements now handle absent forward slots explicitly
and place the starting index after the periodic pattern begins. The unit-orbit
application chooses period one for a nontorsion residue. The explicit
infinite-rank witness's cofinal-valuation proof works for arbitrary Hahn tails.

The optional coarsening remark now retains the original field and changes
only its valuation. It is not a coefficientwise map into a smaller Hahn field:
projecting `Σ t^(nε)` along a quotient killing `ε` would collapse infinitely
many coefficients to one exponent. The normal-form, generic-line and
cofinality proofs remain distinct from finite numerical verification.

Historical code, data and source audit files are preserved. Literature priority,
original-source reconciliation and the unformalized main theorem package remain
separate review obligations.

The classical recurrence correspondence was checked against
[Stanley's author-hosted paper](https://math.mit.edu/~rstan/pubs/pubfiles/45.pdf),
Theorem 1.5 (printed page 176). The report supplies its own coefficient
conversion over the stated Hahn field. The optional coarsening was checked
against the local `ent:lem:coarsening`; the broader literature comparisons
were not independently re-audited.

During review, `origin/main` added the checked escape-chain and formal
exponential-domain results. The coverage descriptions above include that
merge; the new inward-stability proof has not been formalized.

The reviewed article and catalogue rebuilt in three passes at 39 and 21 pages.
The status note now fits on the title page; the baseline placed it on a
separate page. Both unchanged finite suites reproduce the historical outputs
exactly, with all six copied code/data files byte-identical to their sources.
The three delivered source audits are also preserved.

## Merge of source 10

Source 10's code, data and two audit files are byte-identical to the
delivered manuscript package; its own README, checksum list, article source
and PDF are not shipped. Every source 10 result is printed in Sections 14–17,
with its proof, except the facts listed above as printed once. Its three
further questions became Question 19.1 (the re-scoped nonlinear question),
Question 19.2 (vector fields beyond positive Euler operators) and
Question 19.3 (effective representations and minimal certificates). Source
10's references to "Question 15.1" and "Theorems A–C" of this report were
accurate at its pin `048b72c`, where the report was identical to the text it
was merged into. The nonlinear part has not been independently refereed or
formalized; a merge-added remark (Section 15.1) combines Theorem 15.1 with
inward stability for `k = C`, and a merge-added comparison (Section 15.5)
notes that each `t^λ/(1 − t^λ z)` also satisfies a λ-dependent linear
equation.
