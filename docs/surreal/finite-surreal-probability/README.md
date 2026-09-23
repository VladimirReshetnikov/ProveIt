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
article.pdf        the compiled report, 53 pages
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

The main-text proof review covers Sections 2–17: scalar workspaces, standard
part, finite probability, conditional shadows, Bayesian updates, logits,
softmax, finite information theory, Gibbs laws, smoothing, logistic separation,
finite stochastic processes, infinite-addition conventions, normalized
hierarchies, integration, posterior kernels, coin obstructions and regular
all-subsets extensions, the rare latent learning model, standard-part bridges,
Loeb measure and the Poisson construction. It corrects the point-weight
event-algebra hypothesis,
the joint-normalizer condition for successive updates, neutral evidence and
the distinction between sufficient and necessary conditioning precision.
It also separates the attained interior logarithmic-score minimum from the
unattained boundary infimum over strictly positive predictions.
Smoothing now distinguishes positive prior weights from posterior support,
and optional stopping states adaptation and stopping-time measurability.
The hierarchy review makes common supports, uniform bounds and coefficientwise
convergence explicit and gives a posterior with nonintegrable coefficients
before density cancellation. The extension review expands coefficient variation,
relative embeddings, ultrafilters and finite compactness models. The latent
model now derives its martingale updates, proves the needed Bernoulli strong
laws and separates coefficientwise, order and standard-part limits. The bridge
review supplies an explicit Poisson ultraproduct with a diagonal saturation
proof, a quantitative logarithm bound and a measurable ordinary count. The
implementation and scope pass preserves zero weights, specifies the exponential
interface and aligns the dependency notes with the proofs. Remaining imported
results and source/provenance reconciliation still require review; see the
collection's [review record](../../REVIEW.md).

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
   hypothesis); absolute and valuation-sensitive conditioning stability, a sufficient
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
   strict propriety of logarithmic loss for interior true laws and Brier loss
   on the full simplex; boundary logarithmic loss has an unattained infimum
   when predictions must remain strictly positive.
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
    `1/p` in an explicit ultraproduct experiment (Section 15.3), including
    diagonal saturation, the fixed-count limits and a measurable ordinary
    Poisson count defined outside a Loeb-null set.

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
  metadata; ordinary real disintegration and product-law existence are
  imported (Kallenberg). Section 14 now proves the two needed Bernoulli strong
  laws by a fourth-moment argument.
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
- **Nowhere asserted (N14).** No general infinite probability theory based on
  countable additivity in the full fine topology; finite-support laws do
  satisfy that condition. No universal Carathéodory, Radon–Nikodym, Fubini,
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

This build gives 50 pages (a title page, two contents pages and 47 numbered
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
no merge decisions; placement retained every theorem, proof, example and
disclaimer. It
continues the measures report but answers no question it names, so it is a
report of its own.

Placement (Section 1.7 of the article) renamed the source, prefixed its labels,
added Sections 1.4–1.7, the "Since the pin" paragraph and pointer sentences in
Sections 10 and 12, updated the title-page status, Section 16.3, Appendix B and
the bibliography notes, and made the *strong* renames listed above. It left the
mathematics unchanged. `RESEARCH_AUDIT.md` is the manuscript's own audit, not an
independent review. The subsequent review below concerns Sections 2–3 and
records the correction to the finite point-weight representation. The later
Sections 4–5 pass records the update and precision corrections.

## Subsequent proof review

The finite-probability review begins with Sections 2–3. The full event
algebra is now an explicit hypothesis for point-weight models; the trivial
two-point algebra demonstrates why point weights are otherwise not unique.
The expanded scalar and finite proofs cover standard-part uniqueness and
units, positive leading coefficients, common-partition expectation,
Cauchy–Schwarz at zero second moment, tail bounds and Jensen, positive
conditioning denominators, nested conditional expectations, total variance,
and the ticket identities characterizing coherence. Regularity remains a
separate condition, and null-atom versions do not affect scalar identities.
The canonical Hahn embedding was checked against van den Dries–Ehrlich
Section 2, p. 176, and the scalar exponential transfer against Corollary 2.2,
p. 177; the erratum changes ordinal support estimates, not that result.

Validation: three-pass baseline and revised PDFs are clean, with 41 and 43
pages respectively; the changed scalar, probability, inequality and
conditioning pages were visually inspected. All 114 source labels and their
numbers are preserved. The copied delivered verifier passes 2,145 assertions
and matches its recorded JSON apart from the Python version. A separate
953-check exact `Q(t)` run covers all 15 partitions of four points and
nested refinements, including zero masses, infinite payoffs, infinitesimal
thresholds, limited-unit residues and the additivity sure-loss witness.
These are finite examples, not proofs of the general or infinite statements.
All five historical audit/code/data artifacts are unchanged. The independent
index audit checks 2,114 entries in 44 reports; 890 local Markdown destinations
in 93 files resolve. The full Lean build passes 3,906 jobs and its axiom audit
checks 6,127 declarations using only `propext`, `Classical.choice` and
`Quot.sound`. This source review adds no Lean coverage. Sections 4 onward,
remaining imports and broader source reconciliation still require review.

The final probability-core integration merged `e79b92a` through `2cda5fe`,
including the finite-angle quotient and canonical polar-group splitting.
Its source mapping retains the finite-angle domain and ordinary `2πℤ`
periods while allowing a nonzero surcomplex modulus of arbitrary size.
The combined build passes 3,912 jobs, and 6,214 declarations pass the axiom
audit with only `propext`, `Classical.choice` and `Quot.sound`.
The merge also brought in two packages placed in `d4e71b7`; their 67 base-source
statements are indexed provisionally, with assembly and review explicitly
pending. The independent index now checks 2,181 entries across 46 current
main sources (44 assembled reports plus two base manuscripts). All 903 local
Markdown destinations in 97 files resolve. The probability source and its
43-page PDF are unchanged by the merge, and the 30 newly delivered files
remain unchanged. This is integration validation, not a proof review of
the new foundations packages or additional probability Lean coverage.

The second finite-probability pass reviews Sections 4–5. It expands the
conditional-shadow product law and leading-scale formula, including empty
numerators, and shows how pairwise conditional shadows recover the ordered
leading groups and their coefficient ratios. The signed-row proof now makes
the well-ordered selection, dimension bound and coefficient argument explicit;
a two-state example shows why surreal payoffs outside ordinary `ℝ` are not
covered. The comparison with conditional probability spaces and real-payoff
equivalence was checked against Halpern Definition 2.1 and Section 4.

Three scope corrections matter for use: successive updates with zero
likelihoods require a positive joint normalizer; a neutral likelihood ratio
leaves the exact prior unchanged; and the strict valuation-error contract is
sufficient, not necessary for an individual pair of laws. The precision
clause now has its own positive-event hypothesis, and the exact difference
numerator has the correct sign. A rescaling example gives identical
conditionals despite larger input errors; a boundary example proves that
replacing the strict valuation bound by a non-strict one loses the stated
output precision. Infinite-logit persistence now includes the finite-sum
bound and the exponential argument for its unchanged real shadow.

Validation: clean three-pass PDFs at 43 pages in the baseline and 44 after
revision; the changed proof pages were visually inspected. All 114 label
numbers and all five historical audit/code/data artifacts are preserved.
The copied source verifier reproduces its 2,145 assertions, with the JSON
matching apart from the Python version. An additional 1,361 exact `Q(t)`
checks cover conditional products, scale recovery, compatible and impossible
joint updates, strict precision, cancellation, the payoff counterexample and
neutral odds. These are finite examples, not a general proof or an
implementation of surreal logarithms. The independent index audit checks
2,181 entries across 46 main sources (including two provisional bases), and
all 903 local Markdown destinations in 97 files resolve. The full build
passes 3,912 jobs and its axiom audit checks 6,214 declarations using only
`propext`, `Classical.choice` and `Quot.sound`. Sections 6 onward and the
remaining imports still require review; probability Lean coverage is unchanged.

The final Sections 4–5 integration merged `ab36649` through `6f55757`,
including unique interval representatives, natural roots and the complete
polar root formulas. The source mapping was checked against the actual
interval endpoints, positive-degree hypothesis, nonzero input and positive
radius restrictions; the polygon result here is its side-length clause.
The combined build passes 3,916 jobs and 6,277 declarations pass the axiom
audit using only `propext`, `Classical.choice` and `Quot.sound`.
All 2,181 indexed statements across 46 main sources remain correctly
catalogued, and all 907 local Markdown destinations in 97 files resolve.
The merge leaves the reviewed probability source and 44-page PDF unchanged.
This integration adds no probability formalization or review of later sections.

The third finite-probability pass reviews Sections 6–7. Logit Bayes now
states the interior-prior hypothesis and both positive likelihoods explicitly.
The finite state and scale lists are nonempty. The proofs expand logistic
inverses and the infinitesimal Taylor coefficient, softmax's exact common-shift
ambiguity, multiplicative perturbation bounds and the normalizer's logarithmic
bound, and the dominance argument for separated scales. The softmax “limit”
is explicitly a standard-part formula at fixed surreal inputs.

The information proofs now expose the nonnegative Gibbs slack terms, handle
positive-residue and zero-residue entropy coordinates separately, and justify
support inheritance in the chain rule and data processing. The data-processing
gap is an exact sum of conditional divergences, including infinitesimal
positive weights. The rare-entropy series and infinite-divergence example are
expanded. For logarithmic loss over strictly positive predictions, an interior
true law has its unique minimizer, while a boundary law has no minimizer.
Explicit redistribution strictly improves any interior prediction for a
boundary truth, and exponential smoothing attains arbitrarily small excess
above entropy, proving the infimum inside the workspace. Brier's full-simplex
identity and the logistic-loss identity are also expanded.

Validation: baseline and revised PDFs rebuilt in three passes without warnings
at 44 and 46 pages; changed proof pages were visually inspected. All 114 label
numbers and five historical audit/code/data files are preserved. The copied
source verifier reproduces 2,145 assertions with JSON unchanged apart from the
Python version. Separate checks pass 813 exact `Q(t)` cases for softmax ratios,
gauge invariance, infinitesimal errors, boundary redistribution, smoothing and
Brier excess, plus 112 symbolic identities for logistic expansions, Gibbs slack,
entropy chain rules and data-processing gaps with zero coordinates/columns.
These finite checks do not implement arbitrary surreal exp/log or prove the
multiscale theorem. The independent index audit checks 2,181 entries in 46
current sources and all 907 local Markdown destinations in 97 files resolve.
The full Lean build passes 3,916 jobs; its axiom audit checks 6,277 declarations
using only `propext`, `Classical.choice` and `Quot.sound`. No new probability
Lean coverage is claimed. Sections 8 onward and remaining imports are pending.

The fourth finite-probability pass reviews Sections 8–9. Gibbs minimization
now includes its full-simplex domain, uniqueness at infinitesimal temperature,
and the ground-state shadow with a contrasting temperature-scale energy gap.
The finite decision argument includes the nonempty-act hypothesis and the
limited-payoff condition for standard part. Smoothing now distinguishes prior
regularity from posterior support and requires a positive joint normalizer
for successive updates. Its Hahn leading coefficient includes `lc(t)` for a
general infinitesimal scale, and the no-observation case is explicit.

The logistic-separation proof improves every candidate by a finite parameter
shift; an opposite-label example shows that a minimizer can exist without
separation. Finite path consistency is proved by terminal-coordinate sums,
including horizon zero. Optional stopping states adaptation, null-atom
versions and stopping-time measurability, expands the tower/pull-out proof,
and includes an anticipative-time counterexample. Rare hitting includes the
zero horizon, and Bernoulli variance and the failure of infinitesimal accuracy
at any ordinary sample size have explicit calculations.

Validation: baseline and revised PDFs rebuilt in three passes without warnings
at 46 and 47 pages; changed proof pages were visually inspected. All 114 label
numbers and five historical audit/code/data files are preserved. The copied
verifier reproduces 2,145 assertions with JSON unchanged apart from the Python
version. Separate checks pass 275 exact `Q(t)` cases for path marginals,
finite stopping rules (including null atoms and infinite payoffs), hitting,
Bernoulli moments and smoothing, plus 19 symbolic identities for Gibbs laws
and the opposite-label minimum. These finite checks do not construct an
infinite path law or compute canonical surreal exp/log. The independent index
audit checks 2,181 entries in 46 current sources, and all 907 local Markdown
destinations in 97 files resolve. No new probability Lean coverage is claimed.
Sections 10 onward and remaining imports are pending.

The following integration merges the actual surreal projective half-angle
formalization from `7ce5edd`/`f38a1ef` through `2a2d1c9`. The affine and
projective Cayley charts, direction multiplication, finite half-angle formula
and infinite-parameter proximity to the half-turn now have actual-surreal
Lean mappings. The full merged build passes 3,918 jobs and audits 6,313
declarations using only `propext`, `Classical.choice` and `Quot.sound`.
The independent index still checks 2,181 entries in 46 current sources;
all 910 local Markdown destinations in 97 files resolve. The probability
source and 47-page PDF are unchanged by the merge, which adds no probability
formalization or review of its later sections.

A second synchronization through `9189e9d` incorporates `061d8f2` and
batch 21's assembly/catalogue/index commits. The actual inverse sine and
cosine cover their closed surreal input intervals, inverse tangent covers
all surreal slopes, and tangent's fine derivative is proved; inverse-function
fine derivatives remain pending. The merged build passes 3,919 jobs and
its axiom audit checks 6,371 declarations with only the three allowed axioms.

The two new foundations reports are now assembled and catalogued, with
61-page and 50-page PDFs and 136 indexed standard results. Their 26 delivered
audit/code/data files remain byte-identical to placement. The independent
index checks 2,250 entries across all 46 assembled reports, and all 930 local
Markdown destinations in 97 files resolve. These integration checks do not
constitute proof review of the new reports. The finite-probability source and
47-page PDF remain unchanged; review of Sections 10 onward is still pending.

The fifth finite-probability pass reviews Sections 10–11. Fine convergence
retains its relative-smallness hypothesis and is distinguished from a discrete
full carrier. The strong geometric law now has explicit event coefficients,
local finiteness under disjoint regrouping and exact tail masses. The
coefficientwise definition states finite total variation and one support for
all events, matching the measure report. The normalized hierarchy proof
expands the reciprocal, the common product support, the finite coefficient
measure formula and its total-variation bound, including the single-component
case. Conditional shadows explicitly handle a zero numerator residue.

Real-observable expectation uses a uniform real bound; the leading component's
essential bound alone fails on exceptional events, as an endpoint indicator
shows. Dominated convergence permits component-dependent null sets and is
coefficientwise only. The Fubini construction now covers any two set-sized
hierarchies in one value group, since their supports automatically satisfy
the Hahn product lemma. The uncountable-support positivity counterexample
has its scalar group and measure construction explicit; the countable-support
boundary has a transfinite first-nonzero-coefficient proof and the correct
finite-measure upper bound.

For finite-hierarchy posterior kernels, the density versions and their common
full-measure set are explicit. A finite union of positive-gap monoids supplies
a common support for all observations, and the coefficient formulas prove
measurability. The example with densities `2y`, `2(1−y)` on `(0,1)` gives
posterior `t(1−y)/(y+t(1−y))`: its first coefficient `(1−y)/y` is nonintegrable,
whereas multiplying by the observation density reconstructs `t/(1+t)`.
The ordinary disintegration input was checked against Kallenberg, third
edition, Theorem 8.5 in [Conditioning and Disintegration](https://doi.org/10.1007/978-3-030-61871-1_9),
with the observation as conditioning variable and the state as Borel-valued
variable. This verifies the imported scope, not a new surreal disintegration
theorem or a priority claim.

Validation: three-pass baseline and revised builds have no warnings, at 47 and
49 pages; changed proof pages were visually inspected. All 114 label numbers
and the five historical audit/code/data files are preserved. The copied
verifier reproduces 2,145 assertions with JSON unchanged apart from Python
version. Separate checks pass 29,716 exact `Q(t)` examples for geometric
coefficients/regrouping, hierarchy shadows, product exponent collisions and
posterior cancellation, plus 12 symbolic coefficient and integral identities.
These finite checks do not establish transfinite support lemmas, countable
measure extension or the uncountable integration theorem. The independent
index checks all 2,250 entries across 46 reports, and all 930 local Markdown
destinations in 97 files resolve. The Lean build passes 3,919 jobs and audits
6,371 declarations using only `propext`, `Classical.choice` and `Quot.sound`.
No new probability Lean coverage is claimed. Sections 12 onward and remaining
imports are pending.

The following synchronization merges `872f921`/`1c4f513` through `bd4cf96`.
It completes the three actual inverse-trigonometric fine derivatives using
native interval continuity and a topological-field local inverse rule.
The ledger keeps subsequent series, infinite-slope asymptotic and endpoint
assertions separate. The merged Lean build passes 3,920 jobs, with 6,397
declarations audited using only `propext`, `Classical.choice` and `Quot.sound`.
All 2,250 source-index entries remain correct and all 932 local Markdown
destinations in 97 files resolve. The probability source and 49-page PDF
are unchanged by the merge; it adds no probability formalization or review
of Sections 12 onward.

The sixth finite-probability pass reviews Sections 12–13. The two coin
obstructions now expose the common mechanism: real coefficient measures
would need unbounded total variation. The rare-coin first-success partition,
including its complementary all-zero event, gives `2N`; the fair-coin proof
expands pattern multiplicities, second/fourth moments, Hölder exponents and
an explicit finite contradiction threshold. Both exclude signed extensions.
The infinite negative-logit argument now uses the leading coefficient and
exponent of `exp(−L)` in the original Hahn coordinates; it does not assume
that this infinitesimal is a monomial or that changing coordinates preserves
coefficientwise measure structure.

The relative ordered-field embedding proof now constructs both real closures,
checks their size, uses the simplest element of each cut, proves polynomial
and rational-function sign preservation, and treats limit stages and the final
restriction to the original extension. The ultrafilter argument spells out
properness, fineness, nonprincipality, ultrapower order, positive singleton
masses and the infinite snapshot size. The even/odd example and the limits of
permutation invariance are expanded; the shift on the positive integers is
explicitly an injection, and a separate permutation witnesses failure of
unrestricted invariance under regularity. The shared notation guide separates
fine ultrafilters from the fine topology and scalar snapshot sizes from ordinary
cardinalities.

The extension theorem explicitly assumes an ordered subfield and a set-sized
language with a diagram that preserves the original constants. Its finite
models split each positive parent mass equally among nonempty refined children,
preserving all named old events and disjoint-additivity constraints. Different
finite models need not be compatible. Finite sample spaces admit the splitting
inside the original field; the coin corollary applies compactness over `R(t)`
and fixes the original `t`. Checked the construction comparison against
[Benci–Horsten–Wenmackers, arXiv Section 4.2](https://arxiv.org/pdf/1106.1524)
and [Brickhill–Horsten, Definition 4 and Propositions 5–6](https://arxiv.org/pdf/1608.02850).
These references support the sampling construction and its regularity/uniformity
scope, without identifying their infinite-sum convention with Hahn summation.

Validation: baseline and revised PDFs build in three warning-free passes at
49 and 50 pages; changed proof pages were visually inspected. All 114 label
numbers and five historical audit/code/data files are preserved. The copied
verifier reproduces 2,145 assertions, with JSON unchanged except Python version.
Another 5,650 exact finite checks cover coefficient variation and moments,
nonmonomial leading terms, finite atom-splitting models and parity snapshots.
They do not compute infinite ultrafilters, logical compactness, ordered-field
embeddings or countable measure extensions. The independent index checks
2,250 entries in 46 reports, and all 932 local Markdown destinations in 97
files resolve. The Lean build passes 3,920 jobs and audits 6,397 declarations
using only `propext`, `Classical.choice` and `Quot.sound`. No new probability
Lean coverage is claimed. Sections 14 onward and remaining imports are pending.

The following synchronization through `03b474b` merges ten Lean modules
from `debd084` and the placement `7b5f934`. The new modules cover Wick and
theta domains, Tate cubic lemmas, point-spectrum rigidity, polynomial-iterate
equicontinuity, invariant strong measures, finite visibility of negative atoms,
polynomial branch values and Prony cofactor bounds. Their source mappings retain
exact hypotheses and remaining clauses. All ten are imported by the default
root. The merged build passes 3,968 jobs and audits 7,045 declarations using
only `propext`, `Classical.choice` and `Quot.sound`.

Following the new source-reference check in `AGENTS.md`, all 2,542 distinct
referenced labels in the ledger and Lean docstrings resolve in current LaTeX
sources, including optional-argument labels. The placement adds two current
manuscripts with 48 standard results and source material for five existing
reports. All 49 newly placed files are preserved byte-for-byte. The two new
sources are provisionally indexed, giving 2,298 entries in 48 current sources;
the catalogue still covers 46 assembled reports. Their write phase and review
remain pending. All 964 local Markdown destinations in 108 files resolve.
The reviewed finite-probability source and 50-page PDF are unchanged by the
merge. No new Lean mapping is added for that report, whose Sections 14 onward
and remaining imports still await review.

The next synchronization, `6149ce2`, incorporates the inverse-tangent Taylor
formalization from `5e2b6e3`/`2638239`. The geometric inverse agrees with its
analytic lift at finite inputs, its odd-power strong series has the explicit
coefficients, and positive infinite slopes have an exact finite remainder
with the stated standard part. Inverse-sine coefficients and endpoint
ramification remain pending. No manuscript source changed in this merge.
The combined build passes 3,971 jobs and audits 7,074 declarations using only
`propext`, `Classical.choice` and `Quot.sound`. All 2,542 referenced source
labels resolve; the independent index checks 2,298 entries in 48 sources,
and all 967 local Markdown destinations in 108 files resolve. The probability
review remains through Section 13, with its 50-page PDF unchanged.

The seventh finite-probability pass reviews Section 14. Positive integer
coordinate indices and the zero-observation case are explicit. Word
likelihoods derive the posterior, and the predictive success probability
`(1+M_n)/3` verifies its martingale identity directly. Component moments
give the exact nonzero covariance. A fourth-moment bound, Markov's inequality
and the summable real tail estimate prove both Bernoulli strong laws here.
The tail event's measurability, invariance under removal of an initial segment
and pullback to the joint space are explicit. The full-observation conditional
expectation is verified on every observation event using finite-range integrals.

The two exact consecutive-posterior differences have valuation one, so the
single order tolerance `t²` disproves the Cauchy condition on every path.
This includes paths where the real likelihood ratios tend to zero: on the
common-regime typical event, each Hahn coefficient tends to zero, whereas
on the rare tail event even the first coefficient tends to positive infinity.
The text distinguishes these real coefficient limits, standard-part limits,
order convergence and strong Hahn summation, without introducing surreal times.

Validation: the baseline and revised PDFs build in three warning-free passes
at 50 and 51 pages; the changed pages were visually inspected. All 114 label
numbers and five historical audit/code/data files are preserved. The copied
verifier reproduces 2,145 assertions with JSON unchanged except Python version.
Another 3,232 exact or symbolic checks cover word likelihoods, posterior
normalization and expectation, predictive updates, covariance, consecutive
differences, leading coefficients, geometric coefficients and centered fourth
moments. These checks do not compute infinite path events or prove convergence
theorems. The independent index checks 2,298 entries in 48 sources; all 967
local Markdown destinations in 108 files resolve. No Lean module changed in
this pass and no new probability formalization is claimed. Sections 15 onward
and remaining imports are pending.

A downstream consistency check also corrects two sentences in Section 16.
The conditioning precision contract is sufficient, not necessary for each
query with possible cancellation. An ordered field embedding fixing the
reals does preserve standard parts, directly from the inequalities defining
them; preserving exponentials, strong sums or internal structure requires
more. These targeted corrections do not constitute review of the rest of
Section 16. The PDF remains 51 pages after three warning-free passes, with
the affected page inspected and all 114 label numbers preserved.

Synchronization through `64e8a0e` incorporates `f8840cc`/`2cb9c02`.
The actual inverse-sine strong series now has explicit central-binomial
coefficients and a finite ninth-order remainder; inverse sine and inverse
tangent preserve exact valuation at infinitesimal inputs. The endpoint
ramification and derivative obstruction remain separate pending claims.
No manuscript source changed in this merge, and both added Lean modules
are included by the root import. The combined build passes 3,973 jobs and
audits 7,098 declarations with only `propext`, `Classical.choice` and
`Quot.sound`. All 2,543 referenced source labels resolve. The independent
index still checks 2,298 entries in 48 sources, and all 969 local Markdown
destinations in 108 files resolve. These integration checks add no Lean
coverage for finite probability.

A further synchronization through `d93d5fd` incorporates `3e30b1f`, completing
the actual inverse-cosine endpoint half-angle identity, strong series, finite
remainder and half-valuation formula. The endpoint derivative obstruction
remains pending. No manuscript source changed. All three added modules are
root imports, and the merged default build passes 3,976 jobs with 7,116
declarations audited using only `propext`, `Classical.choice` and `Quot.sound`.
All 2,545 cited source labels, 2,298 indexed entries in 48 sources and 972
local Markdown destinations in 108 files pass their checks. The reviewed
probability source and 51-page PDF are unchanged by this integration.

The eighth finite-probability pass reviews Sections 15–17 and aligns the
introductory and appendix dependency notes. The shadow-continuity theorem
now proves real finite additivity first, expands both directions of continuity
from above, and distinguishes real tolerances from arbitrary surreal ones.
The Loeb construction specifies its internal event algebra and probability,
uses saturation on internal remainders to prove the premeasure property,
and distinguishes the unique real measure extension from its completion.
An ordered embedding fixing the reals preserves that real measure but does
not provide its internal events or preserve internal exponentiation.

The Poisson model is now a defined ultraproduct of finite product experiments.
Its internal probability is well-defined, and a diagonal selection proves the
countable saturation needed for Loeb extension. A quantitative real logarithm
bound gives the fixed-count limit, including the empty-product case. The
ordinary finite-count event is Loeb measurable and has measure one; the
resulting ordinary nonnegative integer-valued variable has the exact Poisson
law. A separate Markov estimate shows that no mass escapes to infinite counts.
The written infinite arguments are distinct from computations at finite sample
sizes. Loeb's publisher text remains unavailable in this pass; the historical
metadata-only citation boundary is retained, while the finite-probability
construction is spelled out from saturation and ordinary measure extension.

The implementation interface now permits nonnegative weights with positive
total, retaining exact zeros; strictly positive weights describe regular laws.
It places Brier scoring in the ordered-field layer and names the exponential
isomorphism and scalar inequalities needed for the logarithmic results.
Dependency notes now record the Bernoulli strong laws as proved here, while
product-law existence and real disintegration remain imported. The scope
section corrects an overstatement about full fine countable additivity:
finite-support laws do satisfy it by eventual stabilization. What is absent
is a general infinite sampling theory under that rule. The notation guide
separates the internal and Loeb probabilities and the internal and ordinary
counts, and distinguishes the two local meanings of `H`.

Validation: baseline and revised PDFs build in three warning-free passes at
51 and 53 pages, with changed pages visually inspected. All 114 label numbers
and the five historical audit/code/data files are preserved. The copied
verifier reproduces 2,145 assertions with JSON unchanged except Python version.
Another 7,269 exact rational checks cover binomial normalization, means,
factorization, Markov tails and independent enumeration of word probabilities.
They do not implement an infinite ultrafilter, saturation or Loeb extension.
The independent index checks 2,298 entries in 48 sources, all 2,545 cited
source labels resolve, and all 972 local Markdown destinations in 108 files
resolve. This completes the Sections 2–17 main-text review; remaining imports
and source/provenance reconciliation still require work. No new probability
Lean formalization is claimed.
