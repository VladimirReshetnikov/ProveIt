# Surreal Probability and Log-Odds

**A multiscale theory of belief, information, and infinite sampling**
Single-source research report, 22 September 2026, built from one manuscript
(batch 20, number 05, archive `surreal_probability`). Prepared for Vladimir
Reshetnikov. An AI-assisted research draft, not refereed. No `fsp:` label has a
Lean formalization, and the [formalization ledger](../../FORMALIZATION.md)
maps none.

This directory holds one manuscript. It is not a merge. There was no second
source, and nothing here was selected out of a larger body of work.

```
article.tex        the report, standalone LaTeX with an internal bibliography
                   (delivered as surreal_probability.tex, renamed on placement)
article.pdf        the compiled report, 41 pages
README.md          this guide
RESEARCH_AUDIT.md  the manuscript's own repository, literature and evidence audit, as delivered
code/verify.py     exact finite checks in Q(t) (Python 3.10+, standard library only)
code/build.sh      the manuscript's build script, as delivered; does not work as placed
data/verification.json       recorded output of code/verify.py (2,145 assertions)
data/BUILD_VALIDATION.json   the manuscript's own build record (35-page delivered PDF)
```

`RESEARCH_AUDIT.md`, everything in `code/` and everything in `data/` are
byte-identical to the delivered files. The delivered archive was flat; on
placement the program and build script moved to `code/` and the two JSON
records to `data/`. The delivered PDF and README are not shipped.

Every label in `article.tex` carries the prefix `fsp:`. There are 114 labels:
the manuscript's 100, which were unprefixed and received the prefix on
placement, and 14 added on placement (the four new subsections of Section 1 and
eight subsections, one definition and one appendix that the new text cites). None
was dropped. No label of any other report was touched. The added material
contains no numbered statement or equation, so every theorem, equation and
section number of the manuscript is unchanged. The numbers below are checked
against the build of `article.tex` in this directory.

## What the report claims

**Setting.** `K` is a set-sized ordered subfield of `No` containing `R`; `E`
is such a field closed under the canonical surreal `exp` and positive `log`
(every set lies in one, Lemma 2.1). Hahn fields `R((t^Γ))` enter through
`t^γ ↦ ω^(−γ)`, with `v` the least exponent and `lc` the leading coefficient.
A `K`-probability (Definition 3.1) is **finitely** additive; *regular* means
every nonempty event has positive mass. Sample spaces and all supports are
sets; no law on the class `No` is constructed.

**Finite theory (Sections 2–9).**

1. Residue algebra of standard part (Proposition 2.2); finite variance,
   Cauchy–Schwarz, Markov and Chebyshev bounds with surreal thresholds
   (Theorem 3.2); conditioning on infinitesimal events, tower property, total
   variance, and finite coherence against sure loss (Section 3).
2. **Conditional shadows.** Identical real shadows can give different
   rare-event conditionals (Example 4.1). For a finite regular Hahn probability,
   every conditional standard part is determined by the ordered groups of
   equal leading exponent and their leading coefficients (Theorem 4.2).
   **Signed-row compression** (Theorem 4.3): at most `n` real coefficient rows
   decide every comparison of real-valued acts, including infinitesimal tie
   breaking.
3. **Bayes at every scale.** Minimum-plus valuation rule with coefficient tie
   breaking (Theorem 5.1; Example 5.2, rare evidence reversing the dominant
   hypothesis); absolute and valuation-sensitive conditioning stability, a
   precision contract `v(p_i − q_i) > β + λ` (Theorem 5.3); infinite prior
   logits survive finitely many bounded-real increments (Section 5.3).
4. **Logits and softmax.** `σ` and `logit` are inverse increasing bijections
   and Bayes adds log-likelihood ratios (Proposition 6.2); the tail and
   `logit(t) = −log ω + t + t²/2 + …` expansions; logits of independent events
   (6.6); softmax normalization and multiplicative perturbation bounds
   `e^(−2δ) p_i ≤ q_i ≤ e^(2δ) p_i` (Proposition 6.3); the lexicographic
   multiscale softmax limit (Theorem 6.4).
5. **Information and scoring.** Finite Gibbs inequality, `0 ≤ H(p) ≤ log n`
   and `st H(p) = H(st p)` (Theorem 7.1); chain rule and data processing with
   its equality case (Theorem 7.2); equal shadows with positive infinite
   relative entropy, so standard part does not commute with `D` (Example 7.3);
   strict propriety of logarithmic and Brier scores.
6. **Gibbs and decisions.** An exact finite Gibbs variational identity valid
   for infinite energies or infinitesimal temperature, with no compactness
   (Theorem 8.1); rare events with large payoffs; infinitesimal smoothing;
   no attained logistic optimum under strict separation, even with infinite
   parameters (Proposition 8.2).
7. **Finite processes.** Finite-horizon path laws and their shadows; bounded
   optional stopping (Proposition 9.1); rare transitions and the meaning of
   "sample size `1/t`" (Section 9.3).

**Infinite constructions, kept distinct (Sections 10–15).**

8. Set-indexed fine convergence is eventually constant (Proposition 10.1); a
   regular strong Hahn probability on `N` (Example 10.2); the coefficientwise
   definition (Definition 10.3), the same as the measures report's.
9. **Normalized hierarchies** of arbitrarily many (set-sized, well-ordered)
   ordinary probability laws are positive coefficientwise probabilities, with
   explicit conditional shadows (Theorem 11.1); Lebesgue with exceptional point
   masses (Example 11.2); a bounded-observable expectation with coefficientwise
   dominated convergence and a support-controlled Fubini identity (Section
   11.2).
10. **Integration failure** (Theorem 11.3): on `ω₁` with the
    countable–cocountable measure, a coefficientwise measurable function with
    `0 < X < 1` and common well-ordered support integrates coefficientwise to
    `−t^(ω₁)`. With a countable common support, positivity holds (Section 11.3).
    Posterior kernels for continuous observations in a finite hierarchy, with an
    exact reconstruction identity (Section 11.4).
11. **Coin obstructions.** Independent Bernoulli(`t`) coordinates (Theorem 12.1)
    and Bernoulli(`1/2 + t`) coordinates (Theorem 12.2) have no coefficientwise
    extension, not even a signed one; logit parametrizations do not help.
12. **Regular all-subsets extensions.** A relative ordered-field embedding into
    `No` (Lemma 13.1); a fine-ultrafilter construction with equal positive
    singleton masses (Section 13.2) and its nonuniqueness and symmetry limits
    (Section 13.3); every regular finitely additive probability on an algebra
    extends to all subsets after a set-sized field enlargement inside `No`
    (Theorem 13.2), so both coin models have regular finitely additive
    all-subsets laws (Corollary 13.3).
13. **A rare latent regime** (Section 14): a positive coefficientwise path law
    whose finite posteriors all have standard part zero, while the tail event
    gives the rare regime conditional probability one; the posterior
    martingale is not order-Cauchy on any path (Proposition 14.1).
14. **Bridges.** The real shadow is countably additive iff a stated continuity
    test holds (Theorem 15.1); what Loeb's construction needs beyond a field
    embedding (Section 15.2); a Poisson shadow at sample size comparable to
    `1/p` in a chosen nonstandard experiment (Section 15.3).

Section 16 is an implementation and formalization architecture, Section 17
the scope and research agenda, Appendix A a notation and dependency ledger.

## What the report does not claim

Section 1.4 collects every limitation of the manuscript, its delivered README,
research audit and verification record as (N1)–(N16); each is also stated where
it applies. In brief:

- **Status and priority (N1).** Not refereed, no Lean formalization, no Lean
  code. Non-Archimedean probability (Benci–Horsten–Wenmackers), lexicographic
  and conditional probability (Halpern, Brickhill–Horsten), extended
  log-likelihood ratios (Hammond), ranking theories (Spohn) and Loeb measure
  are precedents. No first-in-literature result, no named conjecture solved,
  no absence claim about the literature. Loeb's paper was cited from indexed
  metadata; real disintegration, product laws and strong laws of large numbers
  are imported (Kallenberg), not re-proved.
- **Repository comparison (N2).** At the pin, targeted: the measures report's
  guide and the opening of its source. Strong-class conclusions are not
  generalized; the coin obstructions are special cases of the measures report,
  not new classification theorems.
- **Scalars (N3).** No law on the class `No`; the workspace lemma is closure
  only; the canonical `log` is not the omega-map; exponential-field transfer
  only for fixed-arity inequalities, never for statements about sample spaces,
  sequences, measurable functions or integration.
- **Finite theory (N4–N8).** No hidden countable additivity; shadows and the
  compression concern stated domains only; no infinite likelihood products or
  data streams; logit endpoints are formal `±∞`; entropy leaves Laurent fields;
  standard part does not commute with relative entropy; no thermodynamic limit
  or infinite-volume Gibbs measure; standard part of expected utility needs
  limited payoffs; bounded stopping only; no law of large numbers in the fine
  topology.
- **Infinite theory (N9–N13).** Failures of the strong rule are not
  contradictions; dominated convergence is coefficientwise, not fine; no Fubini
  or Radon–Nikodym for all surreal-valued functions; version choices remain
  real; the coin obstructions exclude neither finite experiments nor regular
  finitely additive laws; embeddings need not preserve exponentials, internal
  structure or Hahn sums; the extension theorem gives no countable additivity,
  symmetry, canonical embedding or tail probabilities; ultrafilters are
  nonconstructive and the laws non-unique; Loeb needs internal sets and
  saturation.
- **Nowhere asserted (N14).** No countably additive probability on all events in
  the fine topology; no universal Carathéodory, Radon–Nikodym, Fubini,
  martingale convergence, strong law of large numbers, central limit or
  stochastic calculus theorem over `No`; no unique exact-zero conditioning, no
  canonical ultrafilter, no effective computability of arbitrary surreal
  expressions.
- **Evidence (N15).** The checks are finite and exact in `Q(t)`; they implement
  no surreal exponential, infinite summation, extension, saturation or
  compactness, and prove no general theorem.
- **Open (N16).** The four directions of Section 17.3: positive integration
  domains beyond bounded real observables and countable supports; convergence
  of conditional beliefs keeping chosen infinitesimal regimes; extension with
  extra structure; a verified computational library.

## Words used differently elsewhere

Section 1.6 of the article fixes these once.

- **Additivity.** *Finite* (Definition 3.1), *strong* (Section 10, the
  measures report's `meas:def:strong`) and *coefficientwise* (Definition 10.3 =
  `meas:def:coefficientwise`) are three different rules; ultrapower snapshot
  addition and Loeb's real countable additivity are two more. On a finite event
  algebra the first three coincide, which is why Sections 4–5 say *finite Hahn
  probability*. *Strong* always means strong Hahn summability; on placement the
  classical strong law was written out as *strong law of large numbers* in four
  places, and Example 10.2 (formerly "A regular strong law") was retitled.
- **Regular** is Brickhill–Horsten regularity (every nonempty event has positive
  mass): not Radon regularity; the measures report gives the word no meaning.
- **Limited** is what `docs/NOTATION.md` calls *finite*; here *finite* counts
  things.
- **Shadow** is standard part (`P_0 = st P`, conditional and path shadows); the
  Markov report's shadow is the same operation on a resolvent matrix.
- **Fine ultrafilter** (Sections 13.2–13.3) contains every cone
  `{s : F ⊆ s}`; unrelated to the fine topology.
- **Hierarchy** is a normalized hierarchy of laws (Theorem 11.1), not the
  Markov report's hierarchy of projections. **Moment** in Theorem 12.2 is a
  fourth-power expectation.
- Local letters: `H` (entropy; hypothesis; hyperinteger; latent label), `E`
  (workspace; energies; blackboard `𝔼` is expectation), `λ` (`λ_γ = −log t^γ`;
  precision; Lebesgue; Poisson), `D`, `T`, `K`, `C`: each meaning is listed in
  Section 1.6.

## Relation to the neighbouring reports

Compared at commit `50cb709`, with those reports' theorem numbers from builds
of their sources at that commit (Section 1.5 of the article).

**[hahn-valued-measures-and-probability](../hahn-valued-measures-and-probability/).**
The collection's Hahn-valued measure theory; this report continues it on the
finite side and at its interfaces, and answers none of its Questions (Section
26 there). Definition 10.3 is its Definition 2.7 (`meas:def:coefficientwise`);
the strong rule is its Definition 2.8 (`meas:def:strong`). Example 10.2 is an
instance of its Theorem 4.2 (`meas:thm:atomic`); the finite-shadow and
atomicity facts quoted in Section 10.2 are its Corollaries 4.5 and 4.6
(`meas:cor:two-axioms`, `meas:cor:shadow`). **Theorems 12.1 and 12.2 are the
cases `p = t` and `p = 1/2 + t` of its Corollary 23.1 (`meas:cor:iid`)**:
an i.i.d. Bernoulli law has a coefficientwise signed extension iff its bias
is real. Its proof uses the same mechanisms (first-coefficient variation `2n`;
a `√n` lower bound from Hölder and fourth-power expectations, its Lemma 20.3,
`meas:lem:L1lower`). Neither coin law is strong either (its Corollary 10.3 and
Example 10.4). Its non-claims 10.1 and 15.1 say that its negative results do not exclude
finitely additive or ultrafilter probability; Corollary 13.3 here constructs
regular finitely additive all-subsets laws for those same coin data.
Its Proposition 24.2 and Example 24.3 condition coefficientwise probabilities;
Theorem 11.1 and Section 11.4 here compute conditional shadows of hierarchies
and posterior kernels. The expectation (11.4) here is the hierarchy case of
its bounded-observable integral (24.2) (`meas:eq:coef-integral`); where it
declines to integrate Hahn-valued functions, Theorem 11.3 here gives the
counterexample at uncountable support rank and the positive countable case.
That mechanism resembles its null-ideal criterion, Theorem 19.2
(`meas:thm:nullideal`), but concerns a different object, and neither result
implies the other. Its Question 33.9 (`meas:q:markov`) stays open. Commit
`5fe7f8d` also placed in that directory the files of a further manuscript on
coefficientwise measure theory (prefix `16-coefficientwise-measure-theory-`);
this report makes no statement about it.

**[foundations](../../foundations-and-computation/foundations/).** Strong
summability is its (10.1) (`found:eq:summability`) and the Neumann lemma its
Section 10.2. Proposition 10.1 here is clause (2) of its Theorem 12.1
(`found:thm:discrete`), with the same proof; the fine / intrinsic /
coefficientwise distinctions of Section 10 are its Section 12.

**[markov-generators-at-every-scale](../markov-generators-at-every-scale/).**
It studies resolvents `R_L(s) = s(sI + L)^(−1)` and excludes path measures (its
non-claim N1). *Observation of the placement:* by its Proposition 3.1
(`markov:prop:forest`) `R_L(s)` is a positive row-stochastic matrix with limited
entries, so Section 9.1 here applies with `T = R_L(c t^α)`, and the path shadow
is the ordinary finite-horizon chain with that report's shadow `K_α(c)` as
transition matrix. Finite paths only; neither report builds a law on infinite
paths. Its Theorem 8.1 (`markov:thm:stability`) and Theorem 5.3 here are
stability results for different maps.

**[physics](../../physics/surreal-scalars-and-spacetime/).** Its
`phys:sub:probability` (Section 15.4) says that equal infinitesimal weights are
not strongly summable, that a fixed ordinary number of trials leaves an
infinitesimal event infinitesimally likely, and that non-Archimedean and Loeb
constructions need extra structure and an interpretation of records. Section 10
repeats the first, (9.3) is the second, Section 13.2 gives a snapshot-additive
law with equal positive singleton masses, and Section 15.2 states Loeb's
requirements. No physical interpretation is offered here either.

## Stale statements corrected

The manuscript's comparison is pinned to
`d22a5b35d5b3040e870c3cfd6d1c8f7259e094b0` (22 September 2026, 17:19 PDT),
seventeen commits before its placement at `5fe7f8d`. The article keeps the pin as
provenance and adds a "Since the pin" paragraph to Section 1.2.
`RESEARCH_AUDIT.md` is kept as delivered and still describes the repository at
the pin and the delivered 35-page PDF.

- Every description of another report in the manuscript was checked against that
  report's full source at `50cb709` and is accurate: the measures report's two
  classes, strong atomicity and extension criteria, product theorems and hidden
  negative mass, and the restriction of the finite shadow and the `ω+1`
  threshold to the strong class; the foundations report's separation of strong
  sums from fine and valuation convergence; the Markov report's exclusion of
  path measures. The measures report's source did not change between the pin and
  `50cb709`.
- The title page said the article was "a new standalone file, not a
  modification of that repository". It is now a report of the collection; the
  status paragraph says so.
- Section 16.3 and Appendix B named `verify.py`, `verification.json`, a build of
  `surreal_probability.tex` and "a build script is included". They now give the
  placed paths, the build command for `article.tex`, a rerun record, and state
  that `code/build.sh` does not work as placed.
- The three repository bibliography entries point to the pin; a placement note
  says where the current comparison is, and an entry for the physics report was
  added.

## Build and reproduce

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

This build gives 41 pages (a title page, two contents pages and 38 numbered
pages), with no errors, no undefined or multiply-defined references or
citations, no duplicate PDF destinations, and no LaTeX, package or box warnings.
No bibliography database or external figure is needed.

`code/build.sh` is kept as delivered and **does not work as placed**: it changes
into its own directory `code/` and builds `surreal_probability.tex`, which is not
there. `data/BUILD_VALIDATION.json` records the manuscript's own build of the
35-page delivered PDF.

`code/verify.py` prints its JSON result and writes a file only with `--output`.
To keep the delivered record, never point `--output` at `data/verification.json`:

```sh
python code/verify.py --output /tmp/fsp-verification.json
```

It uses exact fractions and rational functions in `Q(t)`, with `t` a positive
infinitesimal (signs from leading coefficients), a fixed seed (1729), and no
floating point. The recorded run (Python 3.13.5) passed 2,145 assertions in 19
families: finite Bayes normalization, update order and odds updates;
leading-scale posteriors; conditional skeletons and precision; signed
compression; finite inequalities; smoothing; the logit identity and logistic
tail coefficients; the latent-model covariance and posteriors; the strong
geometric example; Rademacher moments; and the rare-coin and fair-coin cylinder
coefficients. A rerun at placement on a copy (Python 3.14.4) passed the same
2,145 assertions and matched `data/verification.json` in every field except the
Python version. These are finite checks; they prove none of the infinite
theorems.

## Provenance

The source is one manuscript, *Surreal Probability and Log-Odds: A multiscale
theory of belief, information, and infinite sampling*, dated 22 September 2026.
It arrived as `surreal_probability.zip`, number 05 of the nine archives
committed as `2765c8f`, and was placed at `5fe7f8d`. With one source there were
no merge decisions; every theorem, proof, example and disclaimer is kept. It
continues the measures report but answers no question it names, so it is a
report of its own.

Placement (Section 1.7 of the article) renamed the source, prefixed its labels,
added Sections 1.4–1.7, the "Since the pin" paragraph and pointer sentences in
Sections 10 and 12, updated the title-page status, Section 16.3, Appendix B and
the bibliography notes, and made the *strong* renames listed above. It left the
mathematics unchanged. `RESEARCH_AUDIT.md` is the manuscript's own audit, not an
independent review; no subsequent proof review has been recorded for this
report.
