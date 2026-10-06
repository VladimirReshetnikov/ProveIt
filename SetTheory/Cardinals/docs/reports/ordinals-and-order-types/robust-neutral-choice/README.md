# Robust Choices That Never Settle

**An exact finite–infinite puzzle about resilience, choice, and randomness:
the exact Hamming-robustness optimum of neutral two-way rules (a corollary of
Kleitman's diameter theorem), a sharp prefix inequality, unavoidable
oscillation, an open near-Bernoulli recoding, probability against category,
and a biased-product threshold**

A research article dated 5 October 2026, built from one manuscript. It is an
**unrefereed external manuscript**. Its author line and its PDF author field
read "Research article prepared for Vladimir Reshetnikov"; the package says
nothing about how the text was produced, carries no "unrefereed" or
"prepared for private review" line, no e-mail address and no personal data.
This README adds no authorship statement.

| Source | Batch | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 114 (non-bundle arrival) | `robust_choices.zip` (617,494 bytes, SHA-256 `99cae286…0fff7`; wrapper directory `robust_choices/`, 12 files, 710,666 bytes unpacked), arrival commit `2399df2bd` ("New research reports", 5 October 2026); main file `robust_choices.tex` (1,539 lines, 22-page PDF) | `3b9458b31` (`3b9458b31f459b480ab43a068d7cc56f4cfdbb28`, Section 10 and bibliography entry [3] of the article and the delivery README; it is the batch-98D placement commit of this repository) | `99053b5d1` (batch 114) | the whole report |

**Status:** unrefereed, not formalized: no Lean or Rocq declaration exists
for any statement of this report, and its place in the collection confers no
formal status (Remark 10.1 says which proved Lean declarations bear on one
half of Theorem 8.1). The finite statements were checked exhaustively in
dimensions 1–5 by the delivered program; the infinite theorems rest on the
written proofs only.

## Trust boundaries

- **Quoted, not proved.** Kleitman's diameter theorem (Theorem 2.3),
  credited as the source credits it, to Kleitman (J. Combin. Theory 1(2)
  (1966) 209–214) and to Huang, Klurman and Pohoata (arXiv:1812.05989),
  whose Theorem 1.1 the write read: it is Theorem 2.3 exactly, both parities.
  Kakutani's product-measure dichotomy (1948), the explicit input of
  Theorem 9.1 (not read by the write).
- **Classical, credited.** The finite optimum (Theorem 2.1) is a corollary
  of Kleitman's theorem and is not new; the source proves the reduction to it
  and the matching construction. The non-convergence mechanism is Rényi's
  theory of mixing sequences (1958); sparse extraction belongs to the
  subsequence-principle literature (Aldous 1977, Aldous–Eagleson 1978). The
  source gives direct proofs specialized to the puzzle.
- **Proved in the text.** Everything else: the antipodal-core reduction,
  the sharp prefix inequality and its matching constructions, the mixing and
  oscillation results, the Hamming-code separation, the open bounded-density
  recoding theorem, the probability/category contrasts, the choice theorem
  and the biased-product extension (given Kakutani). The intake found no
  error.
- **The computation proves nothing in higher dimension.** `code/verify.py`
  enumerates every neutral rule in dimensions 1–5 (65,814 rules) and checks
  the optimum and the prefix inequalities with integers; its tables for
  larger `n` evaluate the formula and enumerate nothing.
- **No priority** is claimed by the source, and none is established here.

## What it proves

A rule `f : {−1,1}ⁿ → {−1,1}` is *neutral* if `f(−x) = −f(x)`; `R_f(x)` is the
Hamming distance from `x` to the nearest input with the other output;
`ρ_f(r) = P(R_f > r)` and `ε_f(r) = 1 − ρ_f(r)` under the uniform measure.
Statement numbers are the delivered ones (section counter).

- **Theorem 2.1** (`rch:thm:finite`): `max ρ_f(r) = 2^{1−d} Σ_{j ≤ (d−1)/2 − r} C(d, j)`,
  `d` the largest odd integer `≤ n`; majority on `d` coordinates attains every
  `r` at once, and an even committee has the optimum of one fewer member.
  Lemma 2.2: a robust core has diameter `≤ n − 2r − 1` (the reduction).
- **Proposition 3.1**: the critical budget is of order `√n`, with limit
  `2Φ(−2c)` at `r ~ c√n`, and `1 − ρ*_n(r) = 2r√(2/(πn))(1 + O((r²+1)/n))`.
- **Theorem 4.1** (`rch:thm:prefix`): `α_f(m) = ‖E[f | F_m]‖_∞ ≤ (2^m/V(m,r)) ε_f(r)`,
  `V(m,r)` the Hamming-ball volume, with the best constant independent of the
  dimension; Lemma 4.2: a nonconstant rule on `Q_m` has at least `V(m,r)`
  inputs vulnerable to `r` changes.
- **Theorem 5.1**: if `ε_n(1) → 0`, the decisions are mixing with density
  1/2, agree with any fixed measurable candidate limit asymptotically half the
  time, and take both signs infinitely often on a conull comeager set;
  Proposition 5.2: vanishing influence of each fixed voter suffices;
  **Proposition 5.3**: a Hamming-code construction with `ε(1) → 0` and
  `ε(2) = 1` (one-edit resilience does not give two-edit resilience).
- **Theorem 6.1**: for every `η > 0` a deterministic subsequence whose
  decision map is a continuous open surjection with
  `e^{−η} ≤ dν/dβ ≤ e^{η}` against fair Bernoulli measure (under one-vote
  resilience only); under resilience at every budget, also `R → ∞` almost
  surely. An explicit schedule for majorities.
- **Theorem 7.1**: along those horizons, normal output streams almost surely,
  but frequencies with liminf 0 and limsup 1 and `R = 1` infinitely often on a
  comeager set; Proposition 7.2: no rate for the number of mind changes.
- **Theorem 8.1**: in ZFC a neutral rule invariant under finite changes
  exists on all infinite streams; none is measurable, and neither fibre has
  the Baire property (inner measure 0, outer measure 1).
- **Theorem 9.1**: for the product of Bernoulli(`p_i`) laws such a rule
  measurable for the completed measure exists iff `Σ (p_i − 1/2)² = ∞`
  (a deduction from Kakutani), with an explicit Chebyshev/Borel–Cantelli
  measurable part; no such rule is Borel or has the Baire property.
- Section 10: the computation, the pinned repository files and a proposed
  formalization order; Section 11: research questions Q1–Q10; Appendix A: a
  short problem statement; Appendix B: assumptions at a glance.

Added by the write (5 October 2026), with proofs, marked `[write]`:

- **Remark 10.1 (`rch:rem:lean`)**: the category half of Theorem 8.1 from the
  proved Lean declarations `Cantor.transitive`, `generic_const` and
  `fixed_label`, with complementation as the homeomorphism; complementation
  as a Lean homeomorphism and the assembled statement are not in the
  repository.
- **Proposition 11.1 (`rch:prop:alphabet`)**: for a finite alphabet and a
  group with no global fixed label, an equivariant rule invariant under finite
  changes has fibres that are not all measurable and do not all have the
  Baire property (none, for a transitive group). This proves the regularity
  half of the "natural generalization" that Q6 asserts; existence is not
  addressed.
- In Section 11.1: `K(n,m,r)` is nondecreasing in `n`,
  `K(n,m,r) ≤ 1/(1 − ρ*_n(r))` with equality at `m = n`, and
  `K(n,2,1) = 4/3` for `n ≥ 3` (Question 1); the selection principle of Q8 is
  equivalent over ZF to the existence of the rule (Question 8); the explicit
  schedule forces `n_j > n_{j−1}²` (Question 4).
- A note after the proof of Theorem 7.1 making explicit that `α_f(k)` is
  nondecreasing in `k`, which the recurring-fragility step uses.
- Section 1.4 (provenance, the sources as the write read them, the intake
  checks, relation to the repository, collected non-claims, reading
  conventions), a note on the Kleitman citations after Theorem 2.3, and a
  repository note in Section 10.

## What is not claimed

From the source, kept in the article (collected in Section 1.4):

- The problem is designed; no claim to have settled "a previously advertised
  major conjecture"; the proofs "do not certify historical priority"; the
  delivery README: the article "makes no unverified claim of worldwide
  novelty or a breakthrough on a published open problem".
- The finite optimum is Kleitman's corollary; the bias theorem is "a
  deduction from a classical product-measure theorem, not a new version of
  Kakutani's theorem", concerns one completed biased law, and gives no
  universally measurable neutral selector.
- No new Lean or Rocq verification; the finite program is "a useful
  independent check, not a formal proof".
- The even/odd plateau is not a claim about every fairness criterion or
  voting model; the attaining rules are not classified; the prefix constant
  is sharp only uniformly over dimensions.
- The candidate limit `G` is fixed before the limit; vanishing influences say
  nothing about coalitions; the selected outputs need not be independent;
  the coupling uses an enlarged space; `x E₀ y ⇒ H(x) E₀ H(y)` is a
  homomorphism, not a reduction; `H|_E` is not claimed open or onto.
- The choice construction is not identified with full choice; its exact
  weak-choice strength is open.
- The Lean declarations are not "an already named, directly matching
  repository theorem"; the repository searches are no certificate of
  novelty.
- The explicit majority schedule is not optimal; the questions are proposals,
  a "target" is not asserted to be a published open problem; randomized rules
  must be neutral per seed; the problem was not reviewed or endorsed by
  Elliot Glazer.

## Further questions

Section 11.1 of the article ("Further questions and research",
`rch:sec:further`) states every unproved claim as an open question with its
source, sketch and what is missing (Vladimir's standing rule of 4 October
2026). **Nothing in the source was found to be wrong.** The ten questions
are the source's Q1–Q10, all open; four body sentences that point beyond
what is proved are attached to them.

1. **Fixed-dimension prefix constants** `K(n,m,r)` (`rch:q:constants`).
   *Observation of the write* (exhaustive, exact, `n ≤ 5`):
   `K(n,m,r) = min{2^m/V(m,r), 1/(1 − ρ*_n(r))}` in every case, so the
   prefix inequality is strict in those dimensions except for `r = m` and
   for `(m,r) = (2,1)`, `n ≥ 3`; e.g. `K(5,3,1) = 8/5 < 2`,
   `K(5,5,1) = 8/5 < 16/3`. Whether the minimum formula persists is open.
2. **Classification and stability of optimal rules** (`rch:q:classify`):
   the cores of maximizers are extremal Kleitman families (characterized by
   Frankl, per the abstract of Wu–Li–Feng–Liu–Yu, arXiv:2411.08325v2); the
   rule off the cores is the open part.
3. **Two budgets** (`rch:q:tradeoff`). *Observation:* for `n ≤ 5`, `ε(2) < 1`
   only at the smallest `ε(1)`, `(5/8, 15/16)` for majority of five.
4. **Dense extraction from majority** (`rch:q:dense`): the sufficient
   schedule grows at least doubly exponentially (`7n_j ≥ (7n_{j−1})²`).
5. **A cost of changing one's mind** (`rch:q:mind`).
6. **Several alternatives and other groups** (`rch:q:groups`): regularity
   half proved (Proposition 11.1); existence, packing and a prefix
   inequality open.
7. **Other adversarial metrics** (`rch:q:metrics`).
8. **The exact weak-choice principle** (`rch:q:weakchoice`): the existence
   of the rule is equivalent over ZF to selecting one class from each pair
   of complementary `E₀`-classes; where that principle lies is open.
9. **Dependent laws** (`rch:q:dependent`).
10. **Effective and formal quantitative ergodicity** (`rch:q:formal`).

**Independent check of the write (5 October 2026).** An adversarial check
made by the intake after the write (`9ccf04eae`) found no item needing a
correction. It reread the proof of Proposition 11.1 line by line (both
zero–one laws are proved inside it, with no external ergodicity theorem; `G`
may be infinite), confirmed Remark 10.1 against `GenericErgodicity.lean` at
`74a988c32` (the three declarations exist as quoted and nothing else uses
them), re-derived facts (a)–(c) of Question 1, and with its own exact
enumeration of all 65,814 neutral rules in dimensions 1–5 (not shipped)
reproduced the `K(n,m,r)` formula in all 35 cases, the printed values, the
equality cases and the attainable `(ε(1), ε(2))` lists. It also confirmed
the growth bound of Question 4 (its sharper form `7n_j ≥ (7n_{j−1})²` is now
recorded there), the ZF equivalence of Question 8, and the
Huang–Klurman–Pohoata note against arXiv:1812.05989v1. Its suggestion that
`|Σ| ≥ 2` in Proposition 11.1 follows from the hypothesis on `G` holds only
for nonempty `Σ`, so the statement is unchanged. The record is a dated note
at the end of Section 11.1.

## Checks made at intake

On copies (5 October 2026; Windows, Python 3.14.4, standard library only):

- At placement (batch-114 dossier): `code/verify.py` "OVERALL STATUS: PASS"
  in 3.7 s — 65,814 neutral maps (2, 4, 16, 256, 65,536 in dimensions 1–5),
  394,576 checks of `α_f(m) ≤ ε_f(m)` and 985,710 of the general prefix
  inequality, and a direct-distance audit of the 278 maps of dimensions 1–4;
  the four outputs equal the delivered data files up to newline style (the
  CSV byte for byte). `generate_figures.py` (needs matplotlib and numpy) was
  not run.
- At the write: the same verifier on a fresh copy, PASS in about 2 s, with
  the same comparison result. All 9 shipped delivered files (code, data,
  figures) are byte-identical to the archive.
- The dossier read the manuscript in full and checked by hand the core
  diameter and both parities of the Kleitman reduction, the nine-voter row,
  the induction of Lemma 4.2, the fibre cancellation, the sharpness
  sandwich, the code construction, the likelihood bounds, openness by nested
  compactness, the singular case of Theorem 9.1 and the example `γ ≤ 1/2`.
  Independent programs: the nine-voter row exactly; Proposition 5.3's
  construction brute-forced for `d = 2`, `N = 3` with `L = 1` and `L = 3`
  (neutral, `R_f ≤ 2`, `ε(1) = u_N + t_L − u_N t_L` exactly). The write
  reread every proof; no error.
- The write's own enumeration (exact, all 65,814 neutral rules of
  dimensions 1–5; not shipped) gave the Question 1 and Question 3
  observations above.
- Sources read by the write: Huang–Klurman–Pohoata, arXiv:1812.05989v1,
  Theorem 1.1 (its own bibliography gives Kleitman's paper as J. Combin.
  Theory Ser. A 43 (1986) 85–90, not checked); the Crossref record of
  Kleitman's 1966 paper; the abstract of arXiv:2411.08325v2. Not read:
  Kleitman's paper, Kakutani, Rényi, Aldous, Aldous–Eagleson, Glazer's
  dissertation, the Epoch AI page.

## Relation to the repository

**Formal status.** No statement of this report is formalized. The source
cites `SetTheory/Cardinals/Cardinals/Countable/GenericErgodicity.lean`
(byte-identical at the pin and at the write's base commit; "Everything is
proved; nothing is admitted"), whose declarations
`Cardinals.Countable.zero_one`, `generic_const`, `fixed_label`,
`Cantor.transitive` and `Cantor.global_fixed_point` formalize Proposition
15.3 of the large-cardinal synthesis (`SetTheory/Cardinals/Cardinals/README.md`).
They are ingredients only: Remark 10.1 shows how three of them give the
category half of Theorem 8.1 once complementation is supplied as a
homeomorphism, which the repository does not do. `FiniteCycles.lean` is
cited as motivation only.

**Neighbouring reports** (paths under `SetTheory/Cardinals/docs/reports/`):

- `ordinals-and-order-types/noisy-parity-cubes` (same batch; **see also**):
  total parity labels, which change sign under every single flip, against
  rules here, which are invariant under finite changes and change sign under
  global complementation; its biased threshold `Σ min(q_i, 1 − q_i) < ∞`
  (`np:found:biased`) against `Σ (p_i − 1/2)² = ∞` here (Theorem 9.1). No
  shared theorem; neither cites the other.
- `SetTheory/Cardinals/docs/cardinals/research-synthesis/` (outside the
  collection), Proposition 15.3 (`prop:baire`): the same generic-ergodicity
  mechanism for coordinate permutations.
- Same batch and category, no shared theorem:
  `freiling-symmetry-blacklists`, `bounded-width-power-set-compression`
  (which cites Greene–Kleitman, a different theorem),
  `random-bits-arithmetic-cuts`; `measurable-box-games` shares the
  motivation from Glazer's work.

**Stale claims.** The source's three repository statements (the content of
`GenericErgodicity.lean`, the role of `FiniteCycles.lean`, and that no
quantitative robustness development exists) are correct at the write's base
commit. Nothing to correct.

## Notation

A table at the end of Section 1.4 fixes the letters the source reuses, with
the tempting false readings: `ε_f(r)` (vulnerability) against the tolerance
`ϵ` of Section 9; `η`, `a`, `δ_j` against `η` of `noisy-parity-cubes`, the
growth function `a(n)` and `d = 2a + 1`; `d(n)`, `d`, `d_i` against Hamming
distance `d_H`; `m`; `C_r(f)`/code `C`/cylinder `C`; `D`; `N`; `A`, `A_n`
(two meanings), `A_+`; `b`, `b_i`; `F`, `F_ℓ` and the Lean label type `F`;
`H` and the Lean family `H`; `E`, `E₀`; `K`; `τ_i`, `κ`; the measures. The
cube is `{−1,1}ⁿ` in the text, `F₂` coordinates in Proposition 5.3 and
`{0,1}ⁿ` (first `m` coordinates = low bits) in the program. No symbol was
renamed.

## Labels

Every label carries the prefix `rch:` (none existed in the repository). The
manuscript's 79 labels (`eq:` 51, `sec:` 12, `thm:` 8, `prop:` 4, `lem:` 2,
`prob:` 1, `fig:` 1) were prefixed before anything cited them, and every
`\ref`/`\eqref` was updated. The write added 14: `rch:sec:provenance`,
`rch:rem:lean`, `rch:sec:further`, `rch:prop:alphabet`, and the questions
`rch:q:constants`, `rch:q:classify`, `rch:q:tradeoff`, `rch:q:dense`,
`rch:q:mind`, `rch:q:groups`, `rch:q:metrics`, `rch:q:weakchoice`,
`rch:q:dependent`, `rch:q:formal`. The report has 93 labels; builds of the
delivered text and of this one give all 79 delivered labels the same numbers
(aux files compared). The added remark and proposition are the only numbered
statements of Sections 10 and 11, so no theorem or equation number moved.

## Files

```text
README.md                         this guide (replaces the delivery README.txt)
article.tex                       the report (delivered robust_choices.tex; labels prefixed, [write] additions)
article.pdf                       compiled report, 30 pages
code/README.md                    the delivered verifier guide
code/verify.py                    exhaustive exact verifier, dimensions 1-5 (standard library)
code/generate_figures.py          redraws the figure from exact binomial fractions (matplotlib, numpy)
data/exact_verification.json      the verifier's machine-readable report
data/majority_table.csv           exact and decimal optimal fractions, n = 3, 5, 9, 25, 101 (CRLF line endings)
data/majority_table.tex           the same table through n = 25 as a LaTeX tabular
data/verification_run.txt         the verifier's printed report
figures/robustness_profile.pdf    Figure 1, included by article.tex
figures/robustness_profile.png    the same figure as PNG (not used by article.tex)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery (checked again at the write). The delivery
layout is kept (`code/`, `data/`, `figures/`). `data/majority_table.csv` is
delivered with CRLF line endings and kept byte for byte by a `-text` line in
`SetTheory/Cardinals/.gitattributes`. `data/majority_table.tex` is not input
by the article, whose nine-voter table is typed in.

**Not shipped**, recoverable from the arrival commit (next section):
`robust_choices.pdf` (the delivered 22-page PDF, 437,971 bytes) and the
delivery `README.txt` (2,271 bytes), staged at placement and replaced by this
guide (summarized under "From the delivery README"). The package has no
checksum manifest.

**Delivered text that names the delivery layout.** The article's own
sentences about "the package" and "the accompanying `code/verify.py`" are
accurate here. `code/README.md` says "Run from the package directory" and
that the outputs go to `data/`: in this directory that would overwrite the
shipped data (see below).

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 2399df2bd:docs/incoming/robust_choices.zip > "$T/rc.zip"
sha256sum "$T/rc.zip"   # 99cae2868e1c04b374a298cc96b1b192523bd649b79c4721daf0f3c93a30fff7, 617,494 bytes
cd "$T" && unzip -q rc.zip     # creates robust_choices/
```

## Rerun the checks (on a scratch copy)

Python 3.10 or later, standard library only. **Do not run `code/verify.py`
in this directory**: its default output directory is `../data` relative to
the script, so it rewrites the four shipped data files, and on Windows it
writes the JSON, TeX and text files with CRLF line endings, which changes
their bytes (the CSV is CRLF on every platform). Run it on a copy:

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/ordinals-and-order-types/robust-neutral-choice
T=$(mktemp -d); mkdir "$T/code"; cp "$R/code/verify.py" "$T/code/"; cd "$T"
python3 -I -B code/verify.py            # writes $T/data/; about 2-4 s; ends "OVERALL STATUS: PASS"
cmp data/majority_table.csv "$R/data/majority_table.csv"
for f in exact_verification.json majority_table.tex verification_run.txt; do
  diff <(tr -d '\r' < "data/$f") <(tr -d '\r' < "$R/data/$f") && echo "$f same"
done
```

Tested at the write (Windows, `py` for `python3`): PASS, the CSV
byte-identical, the other three identical up to carriage returns.
`--max-n 4` gives a shorter run; `--output-dir PATH` writes elsewhere. To
redraw the figure, copy `code/generate_figures.py` likewise (it writes
`../figures` relative to itself, here `$T/figures`); it needs matplotlib and
numpy and was not run by the intake.

## Build the PDF

pdfLaTeX (fontenc, inputenc, lmodern, microtype, geometry, amsmath, amssymb,
amsthm, mathtools, graphicx, booktabs, tabularx, array, xcolor, enumitem,
fancyhdr, hyperref); the bibliography is embedded and the figure is
`figures/robustness_profile.pdf`.

```sh
B=$(mktemp -d); mkdir "$B/figures"; cp article.tex "$B/"; cp figures/robustness_profile.pdf "$B/figures/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 5 October 2026, and
rebuilt after the independent check: 30 pages (unchanged); no errors or warnings, no undefined references or citations, no
multiply defined labels, no duplicate PDF destinations, no overfull boxes,
and one underfull line (badness 1675) in the delivered paragraph on
`FiniteCycles.lean` in Section 10, which the delivered text shows identically
(22 pages built the same way).

## From the delivery README

The delivery `README.txt` (replaced by this guide) listed the article, its
PDF, the figure, the verifier, the figure script and the four data files,
gave the commands `python3 code/verify.py`, `python3 code/generate_figures.py`
and two `pdflatex` passes, and stated the mathematical status: "The finite
optimum is a consequence of Kleitman's diameter theorem. The article proves
the antipodal reduction, sharp prefix inequality and its matching
constructions, mixing/oscillation results, the open bounded-density recoding
theorem, probability/category contrasts, a Hamming-code separation of
one-edit and two-edit resilience, and the biased-product extension.
Kakutani's theorem is an explicit input for the bias classification. General
mixing and subsequence phenomena are classical; the article makes no
unverified claim of worldwide novelty or a breakthrough on a published open
problem. Further research questions are labeled proposals." It added that
the exact finite program "is a useful independent check, not a formal proof
of the infinite-dimensional theorems. No new Lean or Rocq verification is
claimed", and named the ProveIt snapshot `3b9458b31f459b480ab43a068d7cc56f4cfdbb28`
and `GenericErgodicity.lean`.

## Rights

Repository contents are MIT-0. The package contains no OEIS or other
third-party data; the figure and tables are computed from the formula.
Nothing was submitted anywhere.

## Provenance

- Sources cited by the manuscript: Kleitman, J. Combin. Theory 1(2) (1966);
  Huang–Klurman–Pohoata, arXiv:1812.05989; Wu–Li–Feng–Liu–Yu,
  arXiv:2411.08325v2; Rényi, Acta Math. Acad. Sci. Hungar. 9 (1958); Aldous,
  Z. Wahrsch. 40 (1977); Aldous–Eagleson, Ann. Probab. 6 (1978); Kakutani,
  Ann. of Math. 49 (1948); Glazer's Harvard dissertation (2023); an Epoch AI
  page (motivation); ProveIt at `3b9458b31`.
- Repository input: `GenericErgodicity.lean` and `FiniteCycles.lean` at the
  pin, both unchanged at the write's base commit.
- Batch 114 of `docs/incoming` (non-bundle arrivals); arrival `2399df2bd`,
  placement `99053b5d1`, written 5 October 2026. Single source, so no merge
  choices. The delivered `robust_choices.tex` is shipped as `article.tex`;
  the delivered code, data and figures as listed above.
