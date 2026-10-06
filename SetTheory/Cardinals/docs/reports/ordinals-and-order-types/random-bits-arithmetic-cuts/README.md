# Random Bits, Finite Catalogs, and Arbitrary Cuts of Arithmetic

**Exact noise thresholds, Boolean universality, and the strength of
induction: which initial segments of a countable model of PA a random
predicate is internally coded on, for every independent bias law; every cut
and every monotone system of conjunction cuts realized; a three-regime
induction theorem; and the finite candidate-catalog problem behind it**

A research article dated 5 October 2026, built from one manuscript. Its
title page reads "Research report prepared for Vladimir Reshetnikov" and
"Developed and written with ChatGPT"; its PDF author field reads "Research
report prepared with ChatGPT for Vladimir Reshetnikov". That is the
authorship statement of the package; this README adds none. The package
carries no "prepared for private review" line, no e-mail address and no
personal data.

| Source | Batch | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 114 (non-bundle arrival) | `Random_Bits_Arithmetic_Cuts.zip` (817,508 bytes, SHA-256 `babff555…80e97`; wrapper directory `random_bits_arithmetic_cuts/`, 17 files, 1,045,556 bytes unpacked), arrival commit `2399df2bd` ("New research reports", 5 October 2026); main file `random_bits_arithmetic_cuts.tex` (2,647 lines, 37-page PDF) | `3b9458b31` (`3b9458b31f459b480ab43a068d7cc56f4cfdbb28`, Section 12.3 of the article, `SOURCE_AUDIT.txt` section 5 and bibliography entries [7]–[10]; it is the batch-98D placement commit of this repository) | `99053b5d1` (batch 114) | the whole report |

**Status:** AI-assisted, unrefereed, **not formalized**: no Lean or Rocq
declaration exists for any theorem, lemma, proposition or corollary of this
report, and its place in the collection confers no formal status. The one
sentence with a formal counterpart is a passing remark (PA has no finite
models; see "Formal status" below). The infinite-model theorems rest on the
written proofs only; the delivered program checks small finite cases and
regenerates the plotted data. Section 11 of the article, "A proposed
formalization route in ProveIt", is the source's **proposal**, not a
description of the repository.

## Trust boundaries

- **Credited, not new.** The fair-coin standard cut (Corollary 3.2) was
  announced by Elliot Glazer (MOPA seminar, 17 October 2023, for countable
  models of PA "or even Q"); the source reconstructs the PA case with its own
  binary-coding formula (Glazer's formula is not public) and claims neither
  his Q case nor anything about uncountable models. Optimal finite ranking
  and the normal source-coding transition (Theorem 9.5) are credited to
  Kontoyiannis–Verdú and Chen–Effros–Kostina; the pairwise atom bound
  (Theorem 8.2) to Benjamini–Gurel-Gurevich–Peled, Proposition 25, who adapt
  Boros–Prékopa. The source proves all of these itself.
- **Proposed as new, priority not established.** The arbitrary-bias
  formula, the realization theorems, the Boolean spectra, the finite-marginal
  and weak-limit separations and the induction classification. The source
  calls its search "a bounded literature assessment, not a priority
  certificate"; the write searched no further (Section 13.1, last item).
- **Computation.** `code/verify_finite_budgets.py` checks the Hamming-layer
  formula, the projection/extension bounds and the pairwise extremizers in
  exact rational arithmetic for N ≤ 10 and draws the two figures. It neither
  simulates a nonstandard model nor verifies an infinite theorem.

## What it proves

`M` is a countable model of PA (nonstandard where needed), `P ⊆ M` an
external random predicate, and `Cut(P)` the set of `a` such that
`P ∩ [0, a)` has an internal binary code `c < 2^a` (a successor-closed
initial segment, its *coding cut*). `S(w)` is the set of `a` with
`Σ_{t<a} w_t < ∞`, an external real sum. Statement numbers are the
delivered ones.

- **Theorem 3.1 (`rbc:thm:product`)**: for independent bits with arbitrary
  biases `p_t`, mode `b`, minority mass `ε_t = min(p_t, 1 − p_t)`, almost
  surely `Cut(P) = Cut(b) ∩ S(ε)`; for `p_t ≤ 1/2`, `Cut(P) = S(p)`.
  Corollary 3.2: fair bits give the standard cut (Glazer's announcement).
  Section 2 proves the deterministic structure (finite-change invariance,
  complements, symmetric differences).
- **Section 4**: every cut is `Cut(P)` almost surely for a full-support,
  nonatomic product law, keeping any finitely many prescribed marginals in
  `(0, 1)` (Theorem 4.2); weak limits do not preserve the coding cut
  (Corollary 4.3).
- **Section 5 (labels `rbc:bs:…`)**: for an independent array of predicates
  with biases bounded away from one, a family of conjunction cuts `C_S` is
  realizable iff it is inclusion monotone (Theorem 5.2, with all biases below
  any `δ < 1/2`); every finitary Boolean observable has cut
  `⋂_{S ∈ D(f)} C_S` over its minimal sensitive supports (Theorem 5.5);
  union, XOR, AND, threshold and nonmonotone examples; a power-law threshold
  (Proposition 5.7); vanishing biases (Proposition 5.8).
- **Section 6**: the bounded `Δ₀(P, E)` coding formula and a bare-language
  `Σ₁(P)` formula `χ` define the same set (Lemma 6.1), so a proper cut
  refutes `IΣ₁(P)` (Corollary 6.2); `Cut(P) = M` iff `(M, P)` satisfies
  `IΔ₀(P, E)` (Theorem 6.3); an infinite externally locally finite
  predicate satisfies `IΔ₀(P, E)` but not `IΣ₁(P)` (Lemma 6.5); three
  regimes for zero-modal independent noise by `W = Σ p_a` and `W_x`
  (Theorem 6.6), each with full support (Corollary 6.7).
- **Section 7**: the event `a ∈ Cut(P)` is dense, meager and `F_σ` for
  nonstandard `a`; the standard-cut fiber is comeager; every fiber is
  `Π⁰₃` (not claimed optimal; `Δ⁰₃` for cuts `{x < a + n}`); finite tests
  have non-commuting double limits (Theorem 7.3); the coding-cut map is
  exactly Baire class two (Proposition 7.4); locally summable perturbations
  preserve the cut (Proposition 7.5).
- **Section 8**: pairwise independence suffices for Theorem 3.1 (Theorem
  8.1); the sharp pairwise atom bound `1/(N+1)` (odd `N`), `1/(N+2)` (even)
  with explicit extremizers (Theorem 8.2); fair marginals alone allow every
  cut (Theorem 8.3); local atoms are the exact obstruction for dependent
  laws (Proposition 8.4).
- **Section 9**: the optimal catalog takes the `K` largest atoms
  (Proposition 9.1); bounded budgets suffice iff `Σ ε_i < ∞` (Theorem 9.2);
  the exact Hamming-layer formula (Theorem 9.4); the normal transition with
  the `−½ log N` term (Theorem 9.5); the sparse Poisson staircase for
  `p_N = λ/N` (Theorem 9.6). Section 10 links the two sides (Corollary 10.1:
  nonconstant Boolean outputs of the universal construction fail `IΣ₁`).

Added by the write (6 October 2026), with a proof, marked `[write]`:

- **Remark 13.1 (`rbc:rem:cp-class`)**: if `M` is nonstandard and
  `Cut(P) = M`, then `P` is a class (every bounded restriction is definable
  from a code), hence not strongly CP-generic by Theorem 19 of
  Abdul-Quader–Schmerl (arXiv:2107.11867v3, read by the write); so every
  product law whose almost-sure coding cut is `M` gives an almost surely
  non-strongly-CP-generic predicate. This makes explicit one sentence of the
  source's Question 5; it says nothing about laws with a proper cut.
- Section 1.3 (provenance, the sources as the write read them, relation to
  the repository with the formal status of each statement, reading
  conventions, collected non-claims), the status note after the abstract,
  dated notes in Sections 1, 11 and 12, and Section 13.1.

## Formal status

Checked by `git grep` in `Logic/PeanoArithmetic` at `3988bf5c4`.

- **Formalized: only the remark of Section 1 that PA has no finite
  models.** `no_finite_PA_model` and `model_carrier_not_finite` (with
  `finite_carrier_cannot_have_injective_successor_missing_zero`) in
  `Logic/PeanoArithmetic/NoFiniteModel/Lean/NoFiniteModel/Theorem.lean`;
  Coq counterparts such as `peano_arithmetic_has_no_finite_model` in
  `Logic/PeanoArithmetic/NoFiniteModel/Coq/NoFiniteModel.v`. The Lean
  statements are for the shallow interface `SetTheory.PA.Model`
  (`Logic/Interpretability/PAHF/Lean/PAHF/PASyntax.lean`), whose induction
  field ranges over every Lean predicate; the proof uses only that successor
  is injective and omits zero, as the remark does.
- **Ingredients only.** `finite_list_beta_code` and
  `finite_vector_beta_code`
  (`Logic/PeanoArithmetic/NotFinitelyAxiomatizable/Lean/PAFiniteBasisReduction/FiniteBetaCoding.lean`):
  in every raw PA structure (`RawPASatisfies`), an *externally finite* list
  of arbitrary, possibly nonstandard, elements has a beta code, with the
  modulus `1 + (i+1)·step` of the article's (6.4). That covers the coding
  step of Lemma 6.5 (standard length `n`), not Lemma 6.1 (internal sequences
  of nonstandard length) and not the binary `Bit` relation, which is not
  formalized. `not_sat_inductionForm` (`EvaluatorCutContract.lean`, with
  `sat_cutAt_iff_isStandard` and `not_sat_sealed_induction`): under that
  module's evaluator `Contract`, the induction instance of the formula
  `cutAt evalFormula` fails because it defines exactly the standard
  elements. Same pattern as Corollary 6.2 and Lemma 6.5, **different
  formula**, no predicate `P`. `raw_above_of_nonstandard` (nonstandard
  elements lie above every numeral) is used implicitly in Lemma 6.5.
- **Outside `Logic/PeanoArithmetic`** (added after the independent check of
  6 October 2026): same-named copies of the three no-finite-model Lean
  declarations, for a `ShallowPAModel` with only zero, successor and the two
  successor axioms (namespace `ProveIt.Optimizations.NoFiniteModel`), are in
  `Optimizations/Logic_Foundations_Optimizations.lean` (`88e56dc38`), which
  the root library (`lakefile.toml`, `ProveIt.lean`) does not import. The
  article's sentence "and nothing else that bears on this report" is
  corrected accordingly, with a dated note keeping the first wording.
- **Not formalized:** every numbered statement of the report; nothing
  probabilistic, no coding cut, no summability cut, no `Bit`, no induction
  statement about `(M, P)`.
- **The "ProveIt formalization plan"** (Section 11, delivered title "A
  concrete formalization route in ProveIt", retitled by the write with a
  dated note) is a proposal. None of its eight modules exists. It is carried
  as Question 13 (`rbc:q:verified`).

## What is not claimed

From the source, kept in the article (collected at the end of Section 1.3):
the Q case and the uncountable and measurability problems of Glazer's talk;
priority, or the solution of a named open problem; that the finite checks
simulate a nonstandard model, verify an infinite theorem or establish
priority; external peer review (the reviews were an internal audit); any
Lean or Rocq formalization; optimality of the `Π⁰₃` bound; sharpness of the
catalog bound `K q_N` for `K > 1`; that Theorem 4.2 matches arbitrary
correlated data; that Theorem 9.2 covers the triangular array
`p_N = λ/N`; induction results in the standard model; failure of bare
`Δ₀(P)` induction by deleting `E`; laws for countably infinite conjunctions
(Remark 5.4); vanishing in the internal order (Proposition 5.8); anything
about uncountable or countably saturated models; any endorsement by Glazer.
The write adds that none of its additions is formalized.

## Further questions

Section 13 of the article holds the source's fourteen questions, now
labelled `rbc:q:base`, `borel`, `invariant`, `effective`, `cpgeneric`,
`modal`, `withinsite`, `approx`, `multiword`, `sparse`, `unequal`,
`alphabets`, `verified`, `uncountable` (cited as Q1–Q14). Section 13.1
(`rbc:sec:further`, Vladimir's standing rule of 4 October 2026) gives the
status of each and adds the source's priority statement as a further open
item. **Nothing in the source was found to be wrong; nothing is refuted.**
All fourteen stay open; Q5 (strongly CP-generic predicates under biased
laws) is settled by Remark 13.1 for laws whose coding cut is `M`; Q13 (a
verified end-to-end theorem) is where the Section 11 plan belongs.

1. Q1, the weakest arithmetic base (Glazer's announced Q case is not
   reproduced).
2. Q2, exact Borel or Wadge complexity of the fibers (`Π⁰₃` upper bound,
   `Δ⁰₃` for one family; no lower bounds).
3. Q3, automorphism-invariant laws.
4. Q4, effective realization relative to a presentation.
5. Q5, arithmetic genericity under biased laws (partly: Remark 13.1).
6. Q6, induction over an arbitrary modal predicate (Theorem 6.6 is
   zero-modal only).
7. Q7, Boolean spectra with correlations inside each site.
8. Q8, quantitative approximate independence.
9. Q9, multiword catalogs under pairwise independence.
10. Q10, all-order sparse expansions and inversion.
11. Q11, algorithms for unequal biases.
12. Q12, growing or internally nonstandard alphabets.
13. Q13, a verified end-to-end theorem (the Section 11 proposal).
14. Q14, beyond countable models.
15. Priority of the proposed contributions (Sections 1.2, 12.3).

## Checks made at intake

On copies (5–6 October 2026; Windows):

- At placement (batch-114 dossier): all 16 entries of the delivered
  `SHA256SUMS.txt` verify; `verify_finite_budgets.py` reran in about 35 s
  (uv; Python 3.13.5, NumPy 2.5.3, SciPy 1.18.1, Matplotlib 3.11.2) and
  reproduced every count (6,138 / 494 / 114 with maximal error 3.33e-16 /
  10, 55, 660, 65, 10). The dossier read Sections 1–11 in full and checked
  by hand the Borel–Cantelli tail, pattern nullity with countably many
  codes, the diagonal marker recursion, the product-weight error, the
  second-moment bound, the two moment polynomials, the induction
  equivalence and the list formula; no error. Its own program confirmed the
  Hamming-layer formula against sorted atoms (N ≤ 8, p = 1/10, 1/3), the
  three values of the table in Section 10 (0.45979872, 0.73572209,
  0.91968940 at N = 10,000, p = 1/N) and the pairwise extremizers (N ≤ 10).
- At the write: the archive re-extracted from `2399df2bd`; all 15 staged
  delivery files byte-identical to it. The script reran on a copy in about
  25 s with the same versions: the JSON equals the shipped one except for
  its `versions` block; the four CSVs have the same rows and differ in 19,
  3, 7 and 3 rows by at most 1.02e-14 (floating-point noise). The write
  reread the whole article, Sections 12–13 and the bibliography included,
  and found no error.
- Sources read by the write: Glazer's seminar abstract; Abdul-Quader and
  Schmerl, arXiv:2107.11867v3 (conventions and Theorem 19); Benjamini,
  Gurel-Gurevich and Peled, arXiv:1201.3261v1, Proposition 25, formula (12),
  which at `p = 1/2` gives `1/(n+1)` (odd) and `1/(n+2)` (even). Located,
  theorems not read: Kontoyiannis–Verdú (arXiv:1212.2668), Chen–Effros–
  Kostina (arXiv:1902.03366, DOI confirmed). Not read: Boros–Prékopa (nor by
  the source).

**Independent check of the write (6 October 2026).** An adversarial check
made by the intake after the write (`90198e982`), with its own code, found
the write's additions correct. Remark 13.1 matches arXiv:2107.11867v3
(conventions of Section 1.1, the definition of a class in Section 4,
Theorem 19 and its proof), and its probabilistic part follows from
Theorems 3.1, 6.6 and 4.2 as stated. Every declaration, file and line of
the formal-status paragraph was confirmed by `git grep`; the check found the
standalone copies in `Optimizations/Logic_Foundations_Optimizations.lean`
that the paragraph's "nothing else" omitted, now added there with a dated
note. Benjamini–Gurel-Gurevich–Peled's formula (12) agrees with an exact
linear program in 112 cases (n = 2..15, eight biases); the Hamming-layer
formula and the exact finite optimization agree with brute force over all
words, N ≤ 10 (6,138 cases); the Poisson limits are approached at N = 10^4
and 10^5 as claimed. No other item needed a correction. The record is a
dated note at the end of Section 13.1.

## Relation to the repository

**Stale claims.** The four repository files the source read
(`Logic/PeanoArithmetic/ListCoding/README.md`,
`Logic/PeanoArithmetic/NotFinitelyAxiomatizable/README.md`, and
`FiniteBetaCoding.lean` and `EvaluatorCutContract.lean` under
`Logic/PeanoArithmetic/NotFinitelyAxiomatizable/Lean/PAFiniteBasisReduction/`)
are byte-identical at the pin and at `3988bf5c4`, and the source describes
them correctly. It did not cite `Logic/PeanoArithmetic/NoFiniteModel`
(present at the pin), which formalizes its remark on finite models. Its
statement that repository searches found no treatment of random predicates
or coin flipping is still true: Glazer's other work is cited in surreal
reports and in `measurable-box-games` and `naming-elementary-embeddings`,
but no other file cites the coin-flipping talk. Nothing needed correcting.
Pointers from the `Logic/PeanoArithmetic` project READMEs are added at
catalogue time, not here.

**Neighbouring reports** (paths under
`SetTheory/Cardinals/docs/reports/ordinals-and-order-types/`):

- `noisy-parity-cubes` (same batch; **see also**): its Proposition
  `np:found:biased` (a total parity label is measurable for the completed
  biased product measure iff `Σ min(q_i, 1 − q_i) < ∞`) has the
  minority-mass condition of Theorems 3.1 and 9.2 and the same first
  Borel–Cantelli step. Different theorems; neither cites the other.
- `robust-neutral-choice` (same batch): a different biased threshold,
  `Σ (p_i − 1/2)² = ∞`. No shared theorem.
- `measurable-box-games`: Glazer's choiceless box-game paradox
  (arXiv:2211.10474), a different problem that also uses product measures
  on random bits. No shared theorem.
- `freiling-symmetry-blacklists`, `bounded-width-power-set-compression`
  (same batch and category): shared delivery template only.

**Category.** `ordinals-and-order-types/` is the collection's set-theory and
logic category (cuts of a model are order-theoretic initial segments); the
report opened no new category.

## Notation

A table in Section 1.3 lists the letters the source reuses, with tempting
false readings: `E` (exponentiation `2^t`) against expectation `𝔼` and the
error term `E_S`; `S(w)` (an external sum, not one computed in `M`) against
index sets `S` and the successor symbol; `D_a` (coded traces) against
`D(f)` (minimal sensitive supports), `A_x`, `D_f`; `A_a` against marker sets
`A_S`; `θ_P`/`ϑ` against the layer fraction `θ`; `χ`, `ℓ`, `Λ`; `δ`, `ε`,
`c`, `W`, `q`, `Q`, `K`, `b`, `a`, `I`; and the words "cut" (no closure
under `+`, `·`), "finite" (external against internal) and `Cut(P) = M`
(`P` is a class, not coded as a whole). No symbol was renamed.

## Labels

Every label carries the prefix `rbc:` (unused before in the collection). The
manuscript's 87 labels (`eq:` 23, `bs:` 22, `sec:` 12, `thm:` 12, `prop:` 6,
`cor:` 5, `lem:` 4, `fig:` 2, `prob:` 1) were prefixed before anything cited
them (`bs:x` became `rbc:bs:x`), and every `\ref`/`\eqref` was updated. The
write added 17: `rbc:sec:provenance`, `rbc:sec:further`,
`rbc:rem:cp-class` and the fourteen question labels `rbc:q:…` (with
`ref=Q\arabic*` on the delivered list). The report has 104 labels. Builds of
the delivered text and of this one give all 87 delivered labels the same
numbers (aux files compared): the additions are a last subsection of
Section 1, a last subsection and remark of Section 13, and unnumbered notes.

## Files

```text
README.md                                  this guide (replaces the delivery README.txt)
article.tex                                the report (delivered random_bits_arithmetic_cuts.tex; labels prefixed, [write] additions)
article.pdf                                compiled report, 44 pages
SOURCE_AUDIT.txt                           delivered source and repository audit (cites the pin)
PROOF_MAP.txt                              delivered map of the main results and their hypotheses
FINITE_VERIFICATION_README.txt             delivered description of the finite checks
code/verify_finite_budgets.py              exact finite checks, CSV tables and figures (delivered at the package root)
data/finite_budget_verification.json       counts, scope and versions of the delivered run (delivered at the package root)
data/fixed_bias_normal_transition.csv      plotted data, Figure 2 (1,053 rows)
data/sparse_critical_window.csv            plotted data, Figure 1 right (1,188 rows)
data/sparse_exponent.csv                   plotted data, Figure 1 left (1,203 rows)
data/sparse_convergence_table.csv          compact convergence table (20 rows)
figures/sparse_budget_staircase.pdf        Figure 1 (included by article.tex)
figures/sparse_budget_staircase.png        PNG copy
figures/fixed_bias_normal_transition.pdf   Figure 2 (included by article.tex)
figures/fixed_bias_normal_transition.png   PNG copy
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery (checked again at the write). The four CSVs
have **CRLF line endings as delivered** and are kept byte-for-byte by `-text`
lines in `SetTheory/Cardinals/.gitattributes` (the rest of the repository
normalizes text to LF).

**Not shipped**, recoverable from the arrival commit:
`random_bits_arithmetic_cuts.pdf` (the delivered 37-page PDF, 515,511
bytes); `SHA256SUMS.txt` (1,533 bytes, 16 entries; repository policy ships
no checksum manifests; verified at placement and at the write); and the
delivery `README.txt` (3,794 bytes), staged as `README.md` at placement and
replaced by this guide (summarized under "From the delivery README").

**Delivered text that names the delivery layout.** `README.txt` (not
shipped) and `FINITE_VERIFICATION_README.txt` run
`python verify_finite_budgets.py` at the package root, where it writes
`finite_budget_verification.json`, `data/*.csv` and `figures/*` **beside
itself** (`ROOT = Path(__file__).resolve().parent`), overwriting them. Here
the script is in `code/` and the JSON in `data/`: running it in place would
create `code/data/`, `code/figures/` and `code/finite_budget_verification.json`.
`SOURCE_AUDIT.txt` and `PROOF_MAP.txt` refer to "this archive", "the
article" and theorem numbers, which are unchanged.

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 2399df2bd:docs/incoming/Random_Bits_Arithmetic_Cuts.zip > "$T/a.zip"
sha256sum "$T/a.zip"   # babff555d621512e25006607cdaa0dfe4c67ecc22577fbb5eec3fd3aa0780e97, 817,508 bytes
cd "$T" && unzip -q a.zip && cd random_bits_arithmetic_cuts && sha256sum -c SHA256SUMS.txt
```

## Rerun the checks (on a scratch copy)

Python 3 with NumPy, SciPy and Matplotlib; no network. Never run the script
in the repository.

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/ordinals-and-order-types/random-bits-arithmetic-cuts
T=$(mktemp -d); cp "$R/code/verify_finite_budgets.py" "$T/"; cd "$T"
uv run --no-project --with numpy --with scipy --with matplotlib python verify_finite_budgets.py
```

It prints the JSON and writes `finite_budget_verification.json`, `data/` and
`figures/` in `$T` (about 25–35 s at intake). Compare
`finite_budget_verification.json` with `$R/data/finite_budget_verification.json`
(equal except `versions`) and the CSVs with `$R/data/` row by row: expect
float noise near 1e-14 in a few rows, not byte equality. The regenerated
figures need not be byte-identical to the shipped ones. The same works in a
fresh extraction (previous section) by running the script in its own
directory.

## Build the PDF

pdfLaTeX (lmodern, geometry, amsmath, amssymb, amsthm, mathtools, microtype,
booktabs, longtable, array, enumitem, graphicx, xcolor, fancyhdr, hyperref,
bookmark, xurl); the bibliography is embedded; the figures must be beside
the source.

```sh
B=$(mktemp -d); cp -r article.tex figures "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 6 October 2026, and rebuilt
after the independent check the same day: 44 pages (unchanged); no errors or warnings, no undefined references or citations, no
multiply defined labels, no duplicate PDF destinations, no overfull boxes;
two underfull boxes (in the formalization table and in a bibliography
entry), both present in a build of the delivered text (37 pages).

## From the delivery README

The delivery `README.txt` (replaced by this guide) listed the package
contents, the build (`latexmk` or three `pdflatex` runs; "The delivered
build used pdfTeX 1.40.25 (TeX Live 2023/Debian)"), the rerun command
(`python verify_finite_budgets.py`, which "overwrites those reproducible
outputs"; delivered run with Python 3.12.14, NumPy 2.3.5, SciPy 1.17.0,
Matplotlib 3.10.8) and the counts above. Its "Mathematical and historical
status" repeats the non-claims: the infinite results rest on the proofs;
"No Lean or Rocq formalization is included"; the reviews are "an internal
research audit, not external peer review"; the fair-coin result is credited
to Glazer and the finite tools are classical; the other results are
"proposed contributions" with no priority asserted.

## Rights

Repository contents are MIT-0. The package uses no OEIS data. The figures
and tables are regenerated from the delivered program.

## Provenance

- Sources cited by the manuscript: Glazer's MOPA abstract (2023);
  Abdul-Quader and Schmerl, MLQ 68 (2022); Kontoyiannis and Verdú, IEEE
  Trans. Inf. Theory 60 (2014); Chen, Effros and Kostina, IEEE Trans. Inf.
  Theory 66 (2020); Benjamini, Gurel-Gurevich and Peled, arXiv:1201.3261;
  Boros and Prékopa, Math. Oper. Res. 14 (1989); four ProveIt files at the
  pin `3b9458b31`.
- Batch 114 of `docs/incoming` (non-bundle arrival `2399df2bd`), placement
  `99053b5d1`, written 5–6 October 2026. Single source, so no merge
  choices. The delivered `random_bits_arithmetic_cuts.tex` is shipped as
  `article.tex`; the delivered program, data, figures and audit texts as
  listed above.
