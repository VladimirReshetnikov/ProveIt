# Aligned Fragments and Constrained Crossover

**Undecidability, exact generation depth, and rational growth of context-free recombination closures; with Part II, PSPACE-complete finite stabilization of regular seeds, Part III, decidable regularity and exact stabilization of crossover closures, Part IV, quadratic finite rank, Part V, rational rank slopes, Part VI, finite crossover stabilization for deterministic automata, and Part VII, the sharp leading constant**

This is a research report in seven Parts, built from seven manuscripts.
Part I (29 September 2026) answers a question that Charles E. Hughes left
open in arXiv:2608.27755v1: the complexity of deciding `L ⊗_c L = L` for a
context-free language `L`, where `⊗_c` is constrained crossover (see "Which
question of Hughes" below). Parts II and III (both 30 September 2026, batch
66) continue it: Part II locates finite stabilization of regular seeds
exactly (PSPACE-complete for NFA input), and Part III decides regularity of
the full closure of context-free seeds and classifies sparse one-marker
seeds. Part IV (1 October 2026, batch 71) answers Part II's Question 24.2:
the largest finite aligned-fragment rank `F(s)` of a binary language
recognized by an `s`-state NFA is quadratic, `(s−3)² ≤ F(s) ≤ (2s+5)²` for
`s ≥ 4`; only the lower bound is new (the upper bound is Part II's). Part
V (1 October 2026, batch 73) answers Part II's Question 24.3: on every live
residue the largest rank of a length-`n` hull word is `σ_r n + O(1)` with a
rational, effectively computable slope `σ_r`; it also lowers the finite-rank
bound to `2(s−1)² + 3`, so `(s−3)² ≤ F(s) ≤ 2(s−1)² + 3`. Part VI (1
October 2026, batch 73) answers Part II's Question 24.1 and Part IV's
Question 53.2: finite stabilization of an explicit complete binary DFA is
coNP-complete, and the largest finite rank `F_DFA(s)` of an `s`-state
complete binary DFA satisfies `(s−7)² + 2 ≤ F_DFA(s) ≤ s² + 3` for `s ≥ 8`,
so `F_DFA(s)/s² → 1`. Part VII (1 October 2026, batch 73) answers Part
IV's Question 53.1 as to the leading constant: for binary NFAs
`(s−3)² ≤ F(s) ≤ s² + 8s`, so `F(s)/s² → 1` (over `q` letters the upper
bound is `s² + max(8, 2q−4)s`), and `F(1), …, F(4) = 1, 2, 5, 7`, the last
three computer-assisted. All seven are AI-assisted research drafts. The title pages and PDF metadata of
Parts I-III name ChatGPT as the drafting assistant and Vladimir Reshetnikov
as the person they were prepared for (Part I: "Research draft prepared with
ChatGPT for Vladimir Reshetnikov"; Part II the same; Part III "Research
manuscript prepared with ChatGPT for Vladimir Reshetnikov"); the title
pages and metadata of Parts IV-VII read "Research note prepared with
OpenAI for Vladimir Reshetnikov". That wording
stays on Part I's title page and in the provenance records (here and the
opening sections of Parts II-VII) only.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 44, manuscript 02 | `ProveIt_Constrained_Crossover` (arrived in `ae28ea2db`; 23-page US-letter PDF) | `9b24a3a8d` | `203016015` | Part I: Sections 1-12 and Appendices A-D, apart from text marked `[write]` |
| 02 | batch 66, manuscript 01 | `ProveIt_Crossover_Stabilization` (*Finite Crossover Stabilization Is PSPACE-Complete: periodic interior universality, quadratic rank bounds, and linear-growth obstructions*; arrived in `9ad899cbe`; 23-page US-letter PDF) | `b8b0fa218` | `4fee1cd07` | Part II: Sections 13-28 |
| 03 | batch 66, manuscript 03 | `ProveIt_Crossover_Classification` (*Decidable Regularity and Exact Stabilization of Crossover Closures: arithmetic invariants, sparse-marker trichotomies, and immediate loss of context-freeness*; arrived in `9ad899cbe`; 23-page US-letter PDF) | `b8b0fa218` | `4fee1cd07` | Part III: Sections 29-45 |
| 04 | batch 71, manuscript 01 | `quadratic-finite-rank-package` (inner directory `quadratic-finite-rank`; *Quadratic Finite Rank for Constrained Crossover*; arrived in `aee32ad45`; 8-page US-letter PDF) | `1bd730779` | `427bca743` | Part IV: Sections 46-54 |
| 05 | batch 73, manuscript 33 | `rational-rank-slopes-package` (inner directory `rational-rank-slopes`; *Rational Rank Slopes for Constrained Crossover*; arrived in `f8c3a392a`; 11-page US-letter PDF) | `1bd730779` | `5e4f1263c` | Part V: Sections 55-65 |
| 06 | batch 73, manuscript 29 | `dfa-crossover-package` (inner directory `dfa-crossover`; *Finite Crossover Stabilization for Deterministic Automata*, revised edition; arrived in `f8c3a392a`; 12-page US-letter PDF) | `1bd730779` | `26abf259b` | Part VI: Sections 66-74 |
| 07 | batch 73, manuscript 21 | `common-path-rank-package` (no inner directory; *Sharp Leading Constant for Constrained Crossover Rank*, source files `hamiltonian-rank.*`; arrived in `f8c3a392a`; 31-page US-letter PDF) | `1bd730779` (and `aee32ad45` for Part IV's manuscript) | `5e4f1263c` | Part VII: Sections 75-88 |

The pins are ProveIt commits `9b24a3a8d545af9624f6ac455f5b548be62818b6`
(source 01, recorded in its Section 1.1 and in `provenance.md`),
`b8b0fa2184a044d46ce9ed0f25f88d7bb60fa042` (sources 02 and 03, recorded in
Sections 14.1 and 30.1 and in their audit notes) and
`1bd730779e8bc44c8976dcd9f38cad86a0d21c26` (sources 04-07, recorded in
their bibliographies and delivery READMEs, and in Sections 46.1, 55.1, 66.1
and 75.1). At `b8b0fa218` Part
I's `article.tex` had the blob `eb4f427f`, which is also the blob at the
placement commit `4fee1cd07`, so everything the two batch-66 manuscripts
say about "the inspected report" refers to Part I as printed. They were
written in parallel and do not cite each other. Source 04's pin postdates
the write of Parts II-III (`202aafd08`); at the pin `article.tex` had the
blob `ff492c83`, unchanged at its placement commit `427bca743`, so its "pinned
report" and "Part II" are Parts I-III and Part II as printed here. Source 05
has the same pin and therefore reads Parts I-III the same way; it links lines
3109-3120 of that blob, which are exactly Question 24.3 and its comment, and
it knew Part IV only as the separate manuscript it calls "the companion
note". Source 06 has the same pin and links lines 3079-3090 of the same
blob: Question 24.1 (lines 3080-3083) and the comment after it; it knew
Parts IV and V only as separate manuscripts. **Superseded and not shipped:**
batch-73 manuscript 32, `dfa-crossover-package (1).zip`, the earlier
10-page edition of source 06 (same pin, also arrived in `f8c3a392a`). It
lacks source 06's Section 7 (the bound `s² + 3`, with Lemmas 73.2-73.3),
takes the upper bound `2(s−1)² + 3` from source 05 and so concludes only
`F_DFA(s) = Θ(s²)`; its nine support files are byte-identical to source
06's. Nothing of it is printed or shipped; it survives in the arrival
commit, and Section 66.1 describes it. Source 07 pins `1bd730779` for this
report and `aee32ad456135cff5db062c5b13eb27fd10ef4c0` for Part IV's
manuscript (then `docs/incoming/quadratic-finite-rank-package.zip`), and
identifies Part V's manuscript by the SHA-256 of its source file
(`data/07-sharp-constant-source-pins.json`); it did not know Part VI.
**Superseded and not shipped:** batch-73 manuscript 24,
`common-path-rank-package (1).zip`, the first (19-page) version of source 07,
same pins, also arrived in `f8c3a392a`; source 07's review receipt names it
as the previous version, and every result and proof of it is in source 07
(which adds Sections 81-84: the finite-alphabet bound, the linear family,
the exact algorithm and the censuses). Section 75.1 describes it.

**Status.** AI-assisted and unrefereed. **Not formalized**: no statement of
any Part has a Lean or Rocq proof, and none of the manuscripts claims one.
The finite computations are exact audits of finite specializations, not
proofs of the universal statements. The report sits in a repository with
Lean and Rocq developments; that placement gives it no formal status (see
"Formal status" below).

```
article.tex        the report, standalone LaTeX with an internal bibliography (pdfLaTeX)
article.pdf        the compiled report, 156 US-letter pages (unnumbered title page, contents pp. 1-4,
                   Part I Sections 1-12 pp. 5-28, Part II Sections 13-28 pp. 29-53,
                   Part III Sections 29-45 pp. 54-77, Part IV Sections 46-54 pp. 78-88,
                   Part V Sections 55-65 pp. 89-101, Part VI Sections 66-74 pp. 102-116,
                   Part VII Sections 75-88 pp. 117-149,
                   Part I's Appendices A-D pp. 150-154, references pp. 154-155)
README.md          this guide
provenance.md      Part I: the manuscript's source record and bounded novelty audit, as delivered
proof-audit.md     Part I: the manuscript's author-side proof and edge-case audit, as delivered
02-pspace-stabilization-proof-audit.md      Part II: claim-dependency and edge-case audit, as delivered
02-pspace-stabilization-source-ledger.md    Part II: pinned-repository and primary-source record, as delivered
03-closure-classification-proof-audit.md    Part III: dependency structure and boundary cases, as delivered
03-closure-classification-provenance.md     Part III: repository pin, literature and novelty audit, as delivered
code/verify.py     Part I: exact finite reference verifier (Python >= 3.10, standard library only)
code/Makefile      Part I: the delivered Makefile (pdf, check, clean; see below)
code/02-pspace-stabilization-verify.py      Part II: exact finite reference solver and audits (486 lines, standard library)
code/02-pspace-stabilization-example.py     Part II: small use of that solver (imports it as `verify`)
code/02-pspace-stabilization-build.sh       Part II: the delivered LaTeX build script
code/03-closure-classification-crossover_masks.py  Part III: exact ray analyzer (206 lines, standard library)
code/03-closure-classification-verify.py    Part III: exact finite audit (158 lines; imports the analyzer as `crossover_masks`)
code/03-closure-classification-Makefile     Part III: the delivered Makefile (pdf, check, examples, clean)
code/04-quadratic-finite-rank-check.py      Part IV: finite construction and rank checker (standard library; prints JSON)
code/04-quadratic-finite-rank-build.sh      Part IV: the delivered two-pass pdfLaTeX build script
code/05-rational-slopes-verify_greedy.py    Part V: literal seed-partition oracle against the subset-reset parser (standard library; prints JSON)
code/05-rational-slopes-check_boundaries.py Part V: checker of the two boundary examples of Section 64.1 (standard library; prints JSON)
code/05-rational-slopes-build.sh            Part V: the delivered two-pass pdfLaTeX build script
code/06-dfa-crossover-check_stripes_exhaustive.py  Part VI: safe core against stripe criterion, all complete binary DFAs on 1-3 states
code/06-dfa-crossover-check_stripes_random.py      Part VI: the same on 1,519 seeded random complete binary DFAs on 1-8 states
code/06-dfa-crossover-check_rank_family.py         Part VI: rank witnesses of the deterministic gate family, literal seed checks
code/06-dfa-crossover-check_gate_completion.py     Part VI: independent gate-completion and witness checks
code/06-dfa-crossover-build.sh                     Part VI: the delivered two-pass pdfLaTeX build script
code/07-sharp-constant-<name>                      Part VII: 22 files (delivered layout flattened into the name):
                                                   check.py, check_general.py, check_templates.py (consistency checks),
                                                   alphabet-check_fixed_alphabet_lemmas.py, alphabet-check_ternary_bookkeeping.py,
                                                   exact-audit_census.cpp, exact-compare_pointwise.cpp, exact-audit_literal.py,
                                                   exact-validate_receipts.py, exact-reproduce.sh,
                                                   exact-producer-{census.cpp,census_graph.cpp,exact_rank.py},
                                                   exact-four_state-{audit_four.cpp,census_four_pruned.cpp,
                                                   four_state_prune_budget.cpp,audit_families.py,check_literal_four.py,
                                                   validate_receipts.py,reproduce.sh}, verify.sh, build.sh
data/verification.json   Part I: the delivered receipt, PASS, 1,766,639 checks
data/verification.txt    Part I: console output of the delivered run
data/02-pspace-stabilization-verification.json  Part II: the delivered receipt, PASS (Python 3.13.5)
data/02-pspace-stabilization-verification.txt   Part II: console transcript of that run
data/02-pspace-stabilization-build-receipt.json Part II: the delivered PDF build record (23 pages, no formal verification)
data/03-closure-classification-verification.json    Part III: the delivered receipt, PASS, 12,867 checks (Python 3.13.5)
data/03-closure-classification-verification.txt     Part III: the same bytes as the JSON receipt (the delivered stdout copy)
data/03-closure-classification-artifact-validation.json  Part III: the delivered PDF/source validation record
data/03-closure-classification-<name>.json         Part III: five ray inputs (endpoint_cycle5,
data/03-closure-classification-<name>.result.json   finite_point_exception, five_markers,
                                                    incompatible_velocities, two_markers) and their analyses
data/04-quadratic-finite-rank-verification.json     Part IV: the delivered record, PASS (147,677 gate-length,
                                                    8,184 literal-rank and 8,222 path-rank checks;
                                                    extremal ranks for m = 2..20)
data/05-rational-slopes-verification.json           Part V: the delivered parser record, PASS (2,604 automata,
                                                    14,407 nonempty slices, 309,574 rank comparisons; seed 20261001)
data/05-rational-slopes-boundary-verification.json  Part V: the delivered record of the two boundary examples
data/06-dfa-crossover-stripes-exhaustive.json      Part VI: PASS, 2 + 64 + 5,832 = 5,898 DFAs, 26,881 live residues
data/06-dfa-crossover-stripes-random.txt           Part VI: one line, 1,519 random DFAs passed
data/06-dfa-crossover-rank-family.json             Part VI: PASS, 24 path witnesses (m = 2..25, top rank 578), 14,308 seed checks
data/06-dfa-crossover-gate-completion.json         Part VI: PASS, 1,829 gate-state completions, 19 witnesses (m = 2..20)
data/07-sharp-constant-<name>                      Part VII: 23 files: general-verification.json, verification.json
                                                   (receipts of check_general.py and check.py), source-pins.json,
                                                   review-receipt.json, finite_alphabet_integration_audit.json,
                                                   linear-exact-census-integration-review.json,
                                                   alphabet-{fixed_alphabet_lemmas,ternary_bookkeeping,
                                                   fixed_alphabet_independent_audit}_receipt.json,
                                                   exact-{audit_receipt,literal_receipt,independent_one_state,
                                                   independent_two_state,independent_three_state,pointwise_two_state,
                                                   pointwise_three_state,original_cutoff_rerun,original_graph_rerun}.json,
                                                   exact-four_state-{audit_receipt,family_verification,
                                                   literal_rank_seven}.json and two census logs
                                                   (exact-four_state-four-state-pruned-census.log,
                                                   exact-four_state-independent-pruned-census.log)
```

Part VII's two remaining delivered files, `check_lower.py` and
`lower-verification.json`, are byte-identical to Part IV's
`code/04-quadratic-finite-rank-check.py` and
`data/04-quadratic-finite-rank-verification.json` and were not shipped
again.

All shipped code, data and notes files are byte-identical to the
deliveries. Delivery names and shipped paths:

- **Part I:** `notes/provenance.md` -> `provenance.md`,
  `notes/proof-audit.md` -> `proof-audit.md`, `Makefile` -> `code/Makefile`;
  `code/verify.py` and `data/verification.{json,txt}` keep their delivered
  paths. The package had no checksum ledger.
- **Part II:** `notes/proof-audit.md` -> `02-pspace-stabilization-proof-audit.md`,
  `notes/source-ledger.md` -> `02-pspace-stabilization-source-ledger.md`,
  `build.sh` -> `code/02-pspace-stabilization-build.sh`, `code/verify.py` and
  `code/example.py` -> `code/02-pspace-stabilization-{verify,example}.py`,
  `data/verification.{json,txt}` and `data/build-receipt.json` ->
  `data/02-pspace-stabilization-*`. The package had no checksum ledger.
- **Part III:** `notes/proof-audit.md`, `notes/provenance.md` ->
  `03-closure-classification-{proof-audit,provenance}.md`, `Makefile` ->
  `code/03-closure-classification-Makefile`, `code/crossover_masks.py` and
  `code/verify.py` -> `code/03-closure-classification-*`,
  `data/verification.{json,txt}` and `data/artifact-validation.json` ->
  `data/03-closure-classification-*`, `examples/<name>.json` and
  `examples/<name>.result.json` -> `data/03-closure-classification-<name>.json`
  and `...-<name>.result.json`. Its checksum list `SHA256SUMS` (21 entries,
  all verified at placement) was retired by repository policy.
- **Part IV:** `check.py` -> `code/04-quadratic-finite-rank-check.py`,
  `build.sh` -> `code/04-quadratic-finite-rank-build.sh`, `verification.json`
  -> `data/04-quadratic-finite-rank-verification.json`. The package had no
  audit or provenance notes; its checksum list `SHA256SUMS` (6 entries, all
  verified at placement) was retired by repository policy.
- **Part V:** `verify_greedy.py` and `check_boundaries.py` ->
  `code/05-rational-slopes-{verify_greedy,check_boundaries}.py`, `build.sh` ->
  `code/05-rational-slopes-build.sh`, `verification.json` and
  `boundary-verification.json` -> `data/05-rational-slopes-*`. The package had
  no audit or provenance notes; its checksum list `SHA256SUMS` (8 entries, all
  verified at placement) was retired by repository policy.
- **Part VI:** `check_stripes_exhaustive.py`, `check_stripes_random.py`,
  `check_rank_family.py`, `check_gate_completion.py` and `build.sh` ->
  `code/06-dfa-crossover-*`; `stripes-exhaustive.json`, `stripes-random.txt`,
  `rank-family.json`, `gate-completion.json` -> `data/06-dfa-crossover-*`.
  The package had no audit or provenance notes; its revision note
  `REVISION.md` is not shipped (its content is in Section 66.1 and above),
  and its checksum list `SHA256SUMS` (13 entries, all verified at placement)
  was retired by repository policy.
- **Part VII:** every staged file keeps its delivered path with `/` turned
  into `-` after the prefix `07-sharp-constant-`: programs and build or
  reproduction scripts in `code/`, receipts, review and audit JSON and the
  two census logs in `data/` (for example `exact/four_state/audit_four.cpp`
  -> `code/07-sharp-constant-exact-four_state-audit_four.cpp`,
  `alphabet/fixed_alphabet_lemmas_receipt.json` ->
  `data/07-sharp-constant-alphabet-fixed_alphabet_lemmas_receipt.json`;
  Section 88 tabulates all 45). The package had no audit or provenance
  Markdown; its checksum list `SHA256SUMS` (50 entries, all verified at
  placement) was retired by repository policy.
- **Not shipped**, for all seven: the delivered manuscript (`article.tex`, for
  Part IV `quadratic-finite-rank.tex`, for Part V `rational-rank-slopes.tex`,
  for Part VI `dfa-crossover-stabilization.tex`, for Part VII
  `hamiltonian-rank.tex`; printed in the report), its PDF (this directory's
  PDF is a build of the written `article.tex`) and `README.md` (replaced by
  this file). They survive in the arrival commits `ae28ea2db`, `9ad899cbe`,
  `aee32ad45` and `f8c3a392a`.

Delivered files whose text still uses delivery names or describes the
package rather than this report:

- `code/Makefile` runs `python3 code/verify.py` and `latexmk` on
  `article.tex` from the package root; see "Building" and "Rerunning".
- `code/verify.py` writes its receipt to `../data/verification.json`
  relative to its own directory, that is, **over Part I's shipped receipt**
  when run in place.
- **`code/02-pspace-stabilization-verify.py` has the same default output
  path, `../data/verification.json`, so run in place without `--output` it
  also overwrites Part I's receipt.** It uses `assert` for some checks (its
  delivered README says to run ordinary Python, not `python -O`).
- `code/02-pspace-stabilization-example.py` does `from verify import NFA,
  Periodic`, which fails beside the prefixed file; its comment calls the
  parity language "article Example 9.3", which is Example 22.3 here.
- `code/02-pspace-stabilization-build.sh` changes to its own directory
  (`code/`) and runs `latexmk` on an `article.tex` there; there is none.
- **`code/03-closure-classification-verify.py` always writes
  `../data/verification.json` relative to its own directory (over Part I's
  receipt) and imports `crossover_masks`, which fails beside the prefixed
  file.** `code/03-closure-classification-Makefile` runs `code/verify.py`
  (in this report Part I's verifier), `code/crossover_masks.py`,
  `examples/*.json` and `latexmk` on `article.tex`.
- `data/verification.txt` ends with the receipt path of the delivered run
  (`/mnt/data/ProveIt_Constrained_Crossover/data/verification.json`), and
  `data/02-pspace-stabilization-verification.txt` with
  `/mnt/data/ProveIt_Crossover_Stabilization/data/verification.json`.
- `data/02-pspace-stabilization-build-receipt.json` and
  `data/03-closure-classification-artifact-validation.json` describe the
  delivered 23-page PDFs, which are not shipped; the latter's `pdf_sha256`
  and `tex_sha256` identify the delivered PDF and source, not this report's
  files.
- `02-pspace-stabilization-proof-audit.md` cites "Section 2", "Section 3",
  "Sections 4-5" and `../data/verification.{json,txt}` of the delivered
  package. Section and theorem numbers of the manuscripts shift by a
  constant in the report: manuscript 02's Section `n` is Section `n + 13`
  (its Theorem 5.3 is Theorem 18.3), its Appendices A and B are Sections 27
  and 28; manuscript 03's Section `n` is Section `n + 29`, its Appendices A
  and B are Sections 44 and 45.
- `provenance.md`, `02-pspace-stabilization-source-ledger.md` and
  `03-closure-classification-provenance.md` speak of "this package" or "this
  delivery", say no repository file was edited (true of the deliveries, not
  of the write phase), and `03-closure-classification-provenance.md` says
  it was "Prepared ... for the user's request".
- The article's Section 10.2 lists Part I's delivered package layout, and
  Sections 23 and 45 those of Parts II and III; `[write]` notes there give
  the shipped paths. Section 54 describes Part IV's `check.py` and
  `verification.json` by their delivery names and says to run
  `python3 check.py`; a `[write, batch 71]` note there gives the shipped
  paths.
- `code/04-quadratic-finite-rank-build.sh` changes to its own directory
  (`code/`), runs `pdflatex` twice on `quadratic-finite-rank.tex` (the
  delivered standalone manuscript, printed as Part IV and not shipped) with
  output in `build/`, and copies the PDF beside itself; there it would fail.
  `code/04-quadratic-finite-rank-check.py` has a `python3` shebang and uses
  `assert` for its checks.
- Part IV's manuscript (Section 54) speaks of "the source file", and its
  bibliography links the pinned `article.tex` at lines 3092-3110; Question
  24.2 occupies lines 3092-3107 there, and lines 3109-3110 already begin
  Question 24.3 (cosmetic; Section 46.1 says so).
- Part V's Section 65 describes `verify_greedy.py`, `check_boundaries.py`,
  `verification.json` and `boundary-verification.json` by their delivery
  names; a `[write, batch 73]` note there gives the shipped paths.
  `code/05-rational-slopes-build.sh` changes to its own directory, runs
  `pdflatex` twice on `rational-rank-slopes.tex` (the delivered manuscript,
  printed as Part V and not shipped) with output in `build/`, and copies the
  PDF beside itself; there it would fail. Both checkers use `assert` for their
  comparisons.
- Part VI's Section 74 describes its four checkers and their outputs by
  their delivery names and says to run them without `-O`; a
  `[write, batch 73]` note there gives the shipped paths. Its delivered
  README's rerun recipe (`python3 check_... > ...-new.json; diff -u ...`) is
  written for the delivered layout. `code/06-dfa-crossover-build.sh` changes
  to its own directory, runs `pdflatex` twice on
  `dfa-crossover-stabilization.tex` (the delivered manuscript, not shipped)
  with output in `build/`, and copies the PDF beside itself; there it would
  fail. `data/06-dfa-crossover-stripes-random.txt` contains an en dash
  ("1–8 states"), as delivered.
- **Part VII's programs all use their delivered layout.** Each Python
  program reads and writes receipts beside itself under delivered names
  (`Path(__file__).parent`), and the two `alphabet` checkers also hash the
  manuscript at `../hamiltonian-rank.tex`, which is not shipped; run in
  `code/` they fail or write files there. `code/07-sharp-constant-verify.sh`
  copies `check*.py`, `*verification.json`, `hamiltonian-rank.tex`,
  `alphabet/` and `exact/` into a temporary directory, and its `diff` against
  `lower-verification.json` needs the delivered `check_lower.py` (Part IV's
  checker here). `code/07-sharp-constant-exact-reproduce.sh` and
  `...-exact-four_state-reproduce.sh` compile the C++ censuses and **replace
  the result receipts in place**; `code/07-sharp-constant-build.sh` builds
  `hamiltonian-rank.tex`. See "Rerunning".
- Part VII's Section 88 describes the package by its delivery names and
  says "the README distinguishes fast receipt and consistency validation
  from complete exhaustive reruns" (the delivered README, not this one); a
  `[write, batch 73]` note there gives the shipped paths.
- `data/07-sharp-constant-exact-audit_receipt.json` records a SHA-256 for
  `producer/exact-finite-rank-algorithm.md`, a note that was not delivered
  (the package's `source-pins.json` says the separate notes were integrated
  into the article). `data/07-sharp-constant-source-pins.json` and
  `data/07-sharp-constant-review-receipt.json` record SHA-256 values of
  delivered and earlier sources (the earlier version, manuscript 24, among
  them); they are kept as delivered data, and the article quotes none of
  them.
- `code/07-sharp-constant-exact-four_state-census_four_pruned.cpp` and
  `data/07-sharp-constant-exact-literal_receipt.json` have no final newline,
  as delivered; the two `.log` files were added past the repository's
  `*.log` ignore rule.

## Labels

Every label carries the prefix `ccc:`; Part II's carry `ccc:ps:`, Part
III's `ccc:cl:`, Part IV's `ccc:qr:`, Part V's `ccc:rs:` and Part VI's
`ccc:dc:`, Part VII's `ccc:sc:`. **404 labels in total** (pattern
`\label(\[[^]]*\])?\{`, no `\label[...]` form occurs):

- **Part I, 80.** The 76 labels of the batch-44 write, unchanged: none was
  renamed or removed, and a comparison of the `.aux` files of the committed
  and the new build shows every one of them with the same number. Four
  labels were added in batch 66 to existing questions so that the new Parts
  can cite them: `ccc:q:regular` (Question 11.2), `ccc:q:grammar` (11.4),
  `ccc:q:series` (11.6), `ccc:q:restricted` (11.7).
- **Part II, 76** (`ccc:ps:`): all 71 labels of manuscript 02, prefixed,
  every `\ref` and `\eqref` updated; five new (`sec:provenance`,
  `sec:source`, `sec:abstract`, `sec:notation`, `sec:conclusion`).
- **Part III, 80** (`ccc:cl:`): all 66 labels of manuscript 03, prefixed;
  nine new on its nine unlabelled research questions (`q:nonsparse`,
  `q:grammarcomplexity`, `q:explicit`, `q:minimal`, `q:arithmetic`,
  `q:approx`, `q:markers`, `q:obstructions`, `q:certificates`) and five new
  sections as in Part II.
- **Part IV, 26** (`ccc:qr:`): all 17 labels of batch-71 manuscript 01,
  prefixed, every `\ref` and `\eqref` updated; five new sections
  (`sec:provenance`, `sec:source`, `sec:abstract`, `sec:notation`, and
  `sec:intro` on the manuscript's unlabelled Section 1) and four new on its
  four unnumbered research questions, now Questions 53.1-53.4 (`q:constant`,
  `q:dfa`, `q:transfer`, `q:formal`).
- **Part V, 33** (`ccc:rs:`): all 25 labels of batch-73 manuscript 33,
  prefixed, every `\ref` and `\eqref` updated; four new sections
  (`sec:provenance`, `sec:source`, `sec:abstract`, `sec:notation`) and four
  new on the questions of its closing sentence, now Questions 65.1-65.4
  (`q:complexity`, `q:denominator`, `q:period`, `q:error`).
- **Part VI, 37** (`ccc:dc:`): all 29 labels of batch-73 manuscript 29,
  prefixed, every `\ref` and `\eqref` updated; four new sections as in
  Part V and four new on the questions of its sentence of open refinements,
  now Questions 74.1-74.4 (`q:exact`, `q:lower-order`, `q:family`,
  `q:individual`).
- **Part VII, 72** (`ccc:sc:`): all 64 labels of batch-73 manuscript 21,
  prefixed, every `\ref` and `\eqref` updated; four new sections as in
  Parts V and VI, and four new on the manuscript's unlabelled Sections 1, 11,
  12 and 13 (`sec:intro`, `sec:near`, `sec:barrier`, `sec:scope`). The
  manuscript has no numbered questions.

The raw manuscripts collided with each other (`app:audit`, `eq:hull`,
`sec:examples`, `sec:hardness`, `sec:questions`) but not with Part I; the
sub-prefixes remove the collisions. Before batch 66 the count was 76, before
batch 71 it was 236. Batch 71 renamed and removed no label, and a comparison
of the `.aux` files of the committed and the new build shows all 236 earlier
labels with the same numbers (the labels of pages 23 and 46 and all of Part
III's now fall one page later, those of the appendices eleven pages later).
Before batch 73 the count was 262. The batch-73 write of Part V renamed and
removed no label, and a comparison of the `.aux` files of the committed and
the new build shows all 262 earlier labels with the same numbers (those of
Parts I and III fall one page later, because the contents grew by a page,
those of Parts II and IV one or two pages, because of the dated notes, and
the appendices fourteen pages later). The write of Part VI renamed and
removed no label either; all 295 earlier labels keep their numbers (Part I's
stay on their pages or fall one page later, those of Parts II-IV one or two
pages, those of Part V two, because of the dated notes, and the appendices
seventeen pages later). The write of Part VII renamed and removed no label;
all 332 earlier labels keep their numbers (those of Parts I and II stay on
their pages or move one page, those of Parts III-VI one or two pages, and
the appendices thirty-four pages later).

## Which question of Hughes

Charles E. Hughes, *Undecidability of Adjacent Equality for Insertion,
Shuffle, and Crossover Language Operations*, arXiv:2608.27755v1 (27 August
2026; 13 pages, printed page numbers equal to PDF page numbers). Checked
against that PDF when Part I was written:

- Section 2 ("Definitions and Notations", p. 2) defines unconstrained
  crossover `⊗_u` and constrained crossover `A ⊗_c B = {wz, yx : wx ∈ A,
  yz ∈ B, |w| = |y|, |x| = |z|}`, the operation of this report (same
  symbol).
- **Section 4 ("Foundational Results"), under "Single step equality"**:
  Theorem 1 and its Corollary make single-step equality undecidable for
  operators that contain concatenation (simple insertion, shuffle,
  unconstrained crossover). The note after the Corollary (p. 3) says that
  constrained crossover fails this criterion, so the complexity of the
  question "does L ⊗_c L = L?" is open; the list of open questions that
  follows repeats it for a context-free `L` (its second item, top of p. 4).
  This is the question Part I answers (its Theorem 4.2).
- Section 14 (p. 12) lists "Study constrained crossover" among its open
  directions without a specific question; Part I's `[write]` note after
  Question 11.9 says how its results bear on Hughes's other Section 13-14
  questions (for crossover only), and a batch-66 note there adds Parts II
  and III.

The delivered abstract of Part I says "Section 4", and its delivered README
and bibliography say "printed page 3"; both are correct. Parts II and III
cite the same version (v1) for the definition only; neither claims a second
answer to Hughes's question.

## What is claimed

Constrained one-point crossover: equal-length parents exchange suffixes at
the same cut (endpoint cuts allowed); `T(L) = L ⊗_c L`, parallel iterates
`L^[k]`, frozen-source iterates `Y_k` (one parent always from `L`).

**Part I** (source 01):

- **Exact rank calculus** (Section 3): the aligned-fragment rank satisfies
  `rank_{T(L)}(w) = ⌈rank_L(w)/2⌉` (Theorem 3.2); `L^[k] = {w : rank ≤ 2^k}`,
  depth `⌈log₂ rank⌉`, and the union of all generations is the coordinate
  hull (Theorem 3.3); the ranks on a slice have no gaps (Theorem 3.4); sharp
  slice stabilization by `⌈log₂ n⌉` (Corollary 3.5, Example 3.6,
  Corollary 3.7); frozen-source depth `rank − 1` (Theorem 3.8).
- **One-step undecidability** (Theorem 4.2): deciding `L ⊗_c L = L` for a
  context-free grammar is co-r.e.-complete, already over `{0,1,@}`, even on
  a family whose first generation is universal; no computable bound on
  shortest counterexamples (Corollary 4.3). This answers Hughes's question.
- **Finite stabilization** (Section 5): exact rank `r + 1` for `r` repeated
  forbidden blocks (Theorem 5.1); eventual stabilization undecidable over
  `{0,1,@,#}`, each fixed adjacent equality co-r.e.-complete (Theorem 5.2;
  frozen-source version Corollary 5.3); the eventual-stabilization set is in
  `Σ⁰₂` and `Π⁰₁`-hard (Proposition 5.4).
- **Fixed target** (Proposition 6.1): rank and generation of one word are
  computable in `O(g n^5)` time from a CNF grammar.
- **Regular inputs** (Section 7): a polynomial DFA one-step test with
  counterexamples of length at most `2s³ − 1` (Theorem 7.1); PSPACE-complete
  one-step problem for NFAs over a fixed ternary alphabet (Theorem 7.2); a
  distance automaton with at most `s·4^s` states whose value is rank − 1
  (Theorem 7.3); finite stabilization decidable, with an EXPSPACE upper bound
  for DFA input that is not claimed optimal (Corollary 7.4). *Batch 66:*
  Part II improves this bound to PSPACE for NFA and DFA input and proves
  PSPACE-completeness for NFA input (below; unrefereed, not formalized). The
  EXPSPACE bound remains a true, weaker statement; a dated note after
  Corollary 7.4 says so.
- **Counting** (Section 8): the full closure of every context-free seed has
  an effectively rational commutative generating function, commuting letter
  weights retained (Theorem 8.3, Corollary 8.4).
- **Non-context-free closure** (Section 9): the binary linear seed `S_q`
  (`q ≥ 3`) has a non-context-free closure `K_q` (Theorem 9.2) with
  `|(K_q)_n| = 4^⌊n/q⌋` and exact generation counts (Theorem 9.3); the
  minimal recurrence order of generation `k` is `q·2^k + 1`, and `q(k+1) + 1`
  for the frozen source (Theorem 9.4).
- **Audit** (Section 10.1): 1,766,639 exact checks, all passing: all 65,814
  binary seed sets of lengths 0-4 (1,050,698 target-rank queries), all 64
  complete two-state binary DFAs (8,128 queries), 255 guard repairs, block
  amplification for 1-64 blocks, the linear-seed family for `q = 3..7` up to
  length 12, and 25 recurrence pairs.

**Part II** (source 02), for a language given by an `s`-state NFA, with
`m = s+2`, `T_s = 2m² + 2m`, `p_s = lcm(1..m)`, `B_s = (2s+5)²`:

- **Main theorem** (Theorem 14.1): finite stabilization of parallel, and of
  frozen-source, self-crossover is in PSPACE and PSPACE-complete over a fixed
  binary alphabet, even for factorial languages with universal hull; if it
  stabilizes, every hull word has rank at most `B_s`, so the parallel clock
  stabilizes by `⌈log₂ B_s⌉` and the frozen one by `B_s − 1`; if not, the
  maximum rank is between `cn − C` and `n` on all large lengths of some
  residue class mod `p_s`; for DFA input a safe-core criterion decides it,
  with interior obstructions of length at most `p_s s²`.
- The steps: exact-length fragment criterion for NFAs (Lemma 16.1); common
  quadratic transient and period, from To's corrected unary theorem
  (Lemma 17.1); interior-universality criterion with `R(L) ≤ 2t + 1`
  (Theorem 18.3); pumping of one obstruction into linear rank
  (Theorem 18.4); residue-wise bounded/linear dichotomy (Corollary 18.5);
  short obstructions (Lemma 19.1), the PSPACE upper bound via Savitch
  (Theorem 19.2), the uniform cutoff (Corollary 19.3) and witness lengths
  (Corollary 19.4); binary hardness from Kao-Rampersad-Shallit's Lemma 6
  (Lemma 20.1, Theorem 20.2, Corollary 20.3: two letters is the least
  alphabet); a four-letter delimiter variant (Proposition 20.4); the safe
  core (Theorem 21.2, Corollary 21.3) and why it fails for NFAs
  (Example 21.4); the one-`1` family `L_m` showing that the `Θ(log s)` order
  of the parallel bound is sharp (Theorem 22.1); Examples 22.2-22.3.
- **Audit** (Section 23): PASS on all 4,096 two-state binary NFAs (3,720
  stabilizing, 376 not), all 5,832 complete three-state binary DFAs (5,768 /
  64), 258,048 independent rank comparisons and further families listed in
  its table; overlapping categories, not to be summed.

**Part III** (source 03):

- For context-free seeds: inclusion, equality and eventual equality of full
  closures are decidable (Theorem 32.1), as are Boolean-combination length
  sets (Theorem 32.3); the full closure is regular exactly when every
  position support has finite row type, which is decidable, with DFA
  synthesis (Theorem 33.1) or an effective infinite obstruction
  (Theorem 33.2).
- For binary one-marker seeds `L_R = 0* ∪ {0^i 1 0^j : (i,j) ∈ R}`: every
  generation is the set of hull words with at most `2^g` ones (frozen:
  `g + 1`), with exact depths and binomial slice counts (Theorem 34.3,
  Corollary 34.4); for semilinear `R`, finite stabilization holds exactly
  when the periods of each component are collinear, and `R` then normalizes
  to rays and points (Theorem 35.1); in that case the hull and generations
  are regular (endpoint velocities), linear context-free and non-regular (one
  co-occurring interior velocity), or not context-free from generation 1 on
  (two distinct compatible interior velocities) (Theorem 37.1,
  Corollary 37.2).
- For ray input: the maximum marker count is a clique number of a
  congruence graph (Theorem 38.2); every graph is realized by vertical rays
  with regular seed and hull (Lemma 39.1); deciding `K(R) ≥ k` is
  NP-complete and stabilization by an input depth coNP-complete, for
  binary-encoded rays (Theorem 39.2).
- A binary linear seed whose closure is reached in one step, is not
  context-free, and has the generating function `(1+z+4z²)/(1−z³)`
  (Theorem 40.1); a family realizing every finite depth (Theorem 40.2).
- **Audit** (Section 41.2): 12,867 exact checks, all passing, including all
  1,099 labelled graphs on 1-5 vertices.

**Part IV** (source 04), with Part II's `R(L)` (largest finite rank, `1`
adjoined) and `F(s)` (its maximum over binary languages of NFAs with at most
`s` states; NFAs ε-free, several initial states allowed):

- **Quadratic finite rank** (Theorem 47.1): for every `s ≥ 4` an `s`-state
  NFA recognizes a language with universal hull and `R(L) = (s−3)²`; with
  Part II's upper bound, `(s−3)² ≤ F(s) ≤ (2s+5)²` and `F(s) = Θ(s²)`. This
  answers Part II's Question 24.2 as to order, for NFAs; the previous lower
  bound was Part II's `⌊(s−3)/2⌋` (Theorem 22.1, a complete-DFA family).
- The construction: the Wielandt two-cycle length gate on `m = s−2` states
  accepts exactly the lengths `H_m = {0} ∪ (m + ⟨m, m−1⟩)` (Lemma 49.1),
  whose largest gap is `(m−1)²` (Lemma 49.2, Sylvester's two-generator
  Frobenius formula shifted by `m`, proved directly; the write credits it);
  adding two monochromatic loop states gives the gate language
  `L^gate_m = {|w| ∈ H_m} ∪ 0* ∪ 1*`, whose rank is `1` on gate lengths and
  the number of runs elsewhere (Lemma 50.1); a transfer principle for any
  cofinite length set (Remark 50.2); exact depths `⌈log₂(m−1)²⌉` and
  `(m−1)² − 1` and binomial slice counts (Corollary 50.3); the six-state
  example with its length-nine generation counts (Section 51).
- Consequences (Section 52): the largest finite stabilization indices are
  `D_∥(s) = ⌈log₂ F(s)⌉ = 2 log₂ s + O(1)` (sharpening Part II's
  `Θ(log s)`) and `D_frozen(s) = F(s) − 1 = Θ(s²)`; under a
  single-initial-state convention `(s−4)² ≤ F_one(s) ≤ (2s+5)²` for `s ≥ 5`.
- Proposition 48.1 restates Part I's rank calculus (Theorems 3.2, 3.3, 3.8,
  Corollary 3.5; Part II's Proposition 15.2 and Corollary 15.3) with one
  more proof; it is not claimed.
- **Audit** (Section 54): the delivered record, PASS: 147,677 gate-length
  comparisons (`2 ≤ m ≤ 60`, `0 ≤ n ≤ 2m²`), 8,184 literal rank computations
  (all binary words, `2 ≤ m ≤ 9`, `n ≤ 9`), 8,222 path-based rank
  computations with alternating extremal witnesses up to `m = 20` (rank
  361).

**Part V** (source 05), in Part II's notation (`P_i`, `R_j`, a transient and
period `t, p`, stable layers `S_{r,a}` and letters `C_{r,a}`, `M_L(n)`):

- **Greedy optimality** (Lemma 57.1): if the admissible intervals of a word
  contain the singletons and are closed under restriction, taking the longest
  admissible interval at each boundary gives a minimum partition; aligned
  fragments of any seed language qualify. Credited as a positional form of a
  classical greedy-parsing principle (Crochemore-Langiu-Mignosi;
  De Luca-Fici), not claimed as new in itself.
- **Fixed-word rank** (Corollary 58.2): a subset parser computes the rank of a
  word of length `n` under an `s`-state NFA in `O((|Σ|+n)s²)` time and
  `O(ns + s²)` space (`O(ns²)` and `O(ns)` given the union relation), in
  place of Part II's interval dynamic program (the comparison is the
  write's).
- **Reset graph** (Proposition 60.1): on a live residue the minimum number of
  liftable pieces of a phase-admissible word is one plus the weight of its
  path in a deterministic 0/1-weighted subset-reset graph with at most
  `p(2^s − 1)` vertices; **cycle means** (Lemma 61.1): the largest path weight
  of length `m` is `σm + O(1)` for the largest reachable cycle mean `σ`.
- **Rational slopes** (Theorem 62.1): for every `s`-state ε-free NFA, every
  valid `t, p` and every live residue `r`, `M_L(n) = σ_r n + O_L(1)` along
  `n ≡ r (mod p)`, where `σ_r ∈ [0, 1]` is rational, effectively computable,
  has reduced denominator at most `p(2^s − 1)`, and is positive exactly on the
  residues with an interior obstruction; no refinement of `p` is needed. This
  answers Part II's Question 24.3 in all three parts.
- **Examples** (Section 63): avoiding `1^{k+1}` gives `M_L(n) = ⌈n/k⌉`, slope
  `1/k`, so denominators are unbounded; a parity language has slopes 0 and 1
  on the two residues (Part II's Example 22.3 with the parities exchanged).
- **Finite-rank bound** (Corollary 64.2): with Schwarz's relation-power
  theorem (imported, Theorem 64.1), `R(L) < ∞` implies `R(L) ≤ 2(s−1)² + 3`,
  so `(s−3)² ≤ F(s) ≤ 2(s−1)² + 3` for `s ≥ 4` and the leading constant lies
  in `[1, 2]`; two three-state examples show that neither `t + 1` nor `κ + 1`
  can replace `2t + 1` (Section 64.1).
- **Audit** (Section 65): the delivered records, PASS: 2,604 automata (every
  binary two-state NFA with nonempty initial and final sets through target
  length six, and 300 seeded random NFAs on three to five states through
  length eight, seed 20261001), 14,407 nonempty slices, 309,574 rank
  comparisons of the parser with a literal seed-partition oracle; the two
  boundary examples with their seed slices and witnesses.

**Part VI** (source 06), for complete DFAs `(Q, Σ, δ, q_in, F)`, with
`F_DFA(s)` the largest finite `R(L)` over complete binary DFAs with at most
`s` states:

- **Decision complexity** (Theorem 67.1): deciding finite stabilization of an
  explicit complete binary DFA is coNP-complete under polynomial-time
  many-one reductions, for the parallel and the frozen-source clock;
  nonstabilization is NP-complete; the coNP upper bound holds over every
  explicit finite alphabet. This answers Part II's Question 24.1.
- The upper bound: cyclic SCCs `H` with period `d_H` and cyclic classes
  define at most `s` stripes `W(H, h)`; a stripe is wholly viable or not
  (Lemma 69.1); internal edges are permitted (Lemma 69.2); one safe vertex
  forces its stripe (Lemma 69.3); a live residue has a nonempty safe core iff
  some viable stripe has no permitted exit from its SCC (Theorem 69.4);
  hence a polynomial certificate of nonstabilization (Proposition 70.1).
- The lower bound: Stockmeyer-Meyer prime-residue testers on unary cycles
  behind a binary selector, with monochromatic branches `00`, `11`; the DFA
  stabilizes iff the 3CNF formula is unsatisfiable (Lemma 71.1).
- **Rank order for DFAs** (Theorem 67.2): for `m ≥ 2` a complete binary DFA
  with one initial state and `m + 6` states has
  `(m−1)² + 2 ≤ R(L^dfa_m) ≤ (m−1)² + 4` (gate lengths and a common
  completion of length `(m−1)² + 1`, Lemma 72.1; Proposition 72.2), and every
  finite-rank complete `s`-state DFA over any finite alphabet has
  `R(L) ≤ s² + 3` (Theorem 73.1, via Lemma 73.2, actual letters lie in the
  stable alphabets after `s` positions, and Lemma 73.3, the joint entry and
  exit budget `h + β ≤ (s − c)d`); so `(s−7)² + 2 ≤ F_DFA(s) ≤ s² + 3` for
  `s ≥ 8`, `F_DFA(s)/s² → 1`, the largest finite parallel index for complete
  binary DFAs is `2 log₂ s + O(1)` and the frozen one is asymptotic to `s²`.
  This answers Part IV's Question 53.2.
- **Audit** (Section 74): the delivered records, PASS: the stripe criterion
  against repeated-deletion safe cores on all 5,898 labelled complete binary
  DFAs with fixed initial state on one to three states (26,881 live
  residues) and on 1,519 seeded random ones on one to eight states (seed
  153735); 24 path-based witnesses of the family for `2 ≤ m ≤ 25` (largest
  rank 578) with 14,308 literal seed-membership tests; 1,829 gate-completion
  cases for `2 ≤ m ≤ 60` and 19 witnesses for `m ≤ 20`.

**Part VII** (source 07), with `F_2(s)` = Part II's `F(s)` and `F_q(s)` its
`q`-letter analogue (the subscript is the alphabet size):

- **General bound** (Theorem 76.2): every `s`-state ε-free binary NFA (any
  initial and final sets) with finite `R(L)` has `R(L) ≤ s² + 8s`; with Part
  IV's family, `(s−3)² ≤ F(s) ≤ s² + 8s` for `s ≥ 4` and `F(s)/s² → 1`. This
  answers Part IV's Question 53.1 as to the leading constant.
- The route: robust compression in a primitive factor-universal component,
  `n² + 8n` pieces with fixed-endpoint witnesses (Theorem 77.2; Lemmas
  77.3-77.5 on two-cycle-length digraphs, from Kirkland-Olesky-van den
  Driessche); a universal strongly connected component and its full stripe
  (Lemmas 78.2-78.3); transfer to the whole NFA with Part VI's two lemmas in
  NFA form (Lemmas 79.1-79.2), the imprimitive case `s² + 6s − 3` and the
  one-symbol case `3s`.
- **Finite alphabets** (Theorem 81.1): `R(L) ≤ s² + max(8, 2q−4)s` over `q`
  letters, an all-symbol family with `R(L) = (s−3)²`, so `F_q(s)/s² → 1` for
  fixed `q` and for `q = o(s)` (Lemmas 81.2-81.4: cycle counts, a common
  vertex by a Hall/König argument, common anchors).
- **Linear family** (Proposition 82.1): for `s ≥ 3` a primitive
  factor-universal binary NFA with one initial and one final state, exponent
  `e = s − 1`, `R(L) = 2s − 1 = 2e + 1` and slice maxima `min(N, 2s − 1)`;
  with Part IV's family `F(s) ≥ max(2s − 1, (s−3)²)`.
- **Exact algorithm and cutoff** (Theorems 83.2-83.3): `R(L)` is unbounded
  iff a reachable periodic-middle graph has a positive cycle, and otherwise is
  computed exactly; finite maximal rank is attained at a length at most
  `max(1, 2t + p(2^s − 1) − 1)`.
- **Small extrema** (Theorem 84.1): `F(1) = 1`, `F(2) = 2`, `F(3) = 5`,
  `F(4) = 7`; computer-assisted for `s = 2, 3, 4` (complete censuses of 2,304
  and 12,845,056 labelled presentations with three agreeing implementations;
  for four states a proved pruning by the bound `2t + 1` and a complete scan
  of 45,695,722 letter-exchange representatives, maximum 6, reproduced
  independently), with explicit witnesses.
- **Restricted classes** (Sections 85-87): `R(L) ≤ n² + n + 1` for
  Hamiltonian primitive factor-universal graphs (Theorem 85.1),
  `n² + 3n` for circumference at least `n − 1` (Theorem 86.1), and a family
  with exponent `(n−1)(n−2)`, no forward- or backward-total subset and
  `R(L) ≤ 6n + 3` (Proposition 87.1).
- Restated, not claimed: Lemma 78.1 and Corollary 83.4 (Part II's criterion
  and bound `2t + 1`), Proposition 80.1 (Part IV's theorem), Lemma 83.1 and
  its parser (Part V's, second proof kept).
- **Audit** (Section 88): the delivered receipts of the consistency checks
  and censuses; the census logs; three review receipts of the delivery.

## What is not claimed

**Part I**, kept from the manuscript: an unrefereed draft, not a
proof-assistant development; the bounded literature search is not a
priority claim, and equivalents in recombination, splicing or
genetic-algorithm literature have not been excluded; the coordinate-hull
(product) observation is not claimed as a first discovery; CFG universality,
effective Parikh semilinearity, Presburger counting (Woods) and
distance-automaton limitedness (Kirsten) are imported, not reproved; the
guard construction alone cannot prove undecidability of eventual
stabilization; `Σ⁰₂`-completeness is not claimed (Question 11.1); the
EXPSPACE bound is not claimed optimal (Part II now improves it; see above)
and the `O(g n^5)` bound not optimal; rationality of the commutative series
implies neither regularity nor context-freeness of the closure; the finite
audits do not implement a general CFG compiler, Presburger counting engine
or limitedness solver, and the executable verifier specializes to finite
seeds and DFAs; the research questions other than Hughes's are not asserted
to be new or globally open; the Lean section is a plan. Part I does not
solve the both-singleton insertion conjecture and does not reprove the
sibling report's spectrum realizations. Its results for crossover answer
none of Hughes's questions about insertion or shuffle.

**Part II**, kept from manuscript 02: unrefereed, no Lean or Rocq; priority
not asserted (targeted literature audit against a pinned revision); To's
corrected unary progression theorem, Kao-Rampersad-Shallit's Lemma 6 and
Savitch's theorem are imported, not reproved; Part I's rank calculus is
credited and reproved, not claimed; **the exact complexity for DFA input is
not determined** (Question 24.1), nor the optimal rank bound (24.2, known
only between `⌊(s−3)/2⌋` and `(2s+5)²`; *batch 71:* Part IV raises the
lower bound to `(s−3)²` for NFAs, so the order is quadratic, while the
constant and the DFA case stay open) or the residue-wise slopes (*batch
73:* Part V determines them, and bounds the constant by two); the
safe-core algorithm is polynomial only in the expanded period, not in the
DFA (*batch 73:* Part VI settles the DFA complexity, coNP-complete, and the
DFA rank order); the four-letter delimiter reduction is credited to Part I's amplifier;
the reference solver stores explicit graphs and is not an implementation of
the polynomial-space bound; finite audits prove no universal statement and
do not infer PSPACE-hardness.

**Part III**, kept from manuscript 03: unrefereed, no Lean or Rocq; global
priority not established; Parikh semilinearity, Presburger definability,
monadic decomposition and the slender-language (paired-loop) background are
classical, and CLIQUE hardness is imported; the regularity procedure has no
polynomial bound in the grammar; the closure procedures do not compare the
seeds themselves or solve eventual stabilization for arbitrary grammars;
**no general context-freeness decision for nonsparse Presburger hulls**
(Question 42.1); the NP/coNP results are for binary ray input and a variable
threshold, **not for explicit DFAs** or fixed depths; the analyzer implements
no CFG compiler, Presburger solver, semilinear normalization or DFA
synthesis; the global-regularity question is not attributed to a numbered
open question by the manuscript. (The write notes that it partly answers
Part I's Question 11.4; the manuscript itself makes no such claim.)

**Part IV**, kept from batch-71 manuscript 01 and its delivery README:
unrefereed, no Lean or other proof-assistant formalization; no global
priority, no exhaustive priority search, no claim of first discovery in the
worldwide literature; the upper bound `(2s+5)²` (with To's corrected unary
theorem behind it) and the fragment-clock framework are credited inputs,
imported, not reproved; the equal-length fragment framework is the
report's, and related represented-interval crossover machinery is credited
to Manzoni, Vanneschi and Mauri (2012); the two-cycle graph is classical
(Wielandt, Neufeld); **the leading constant, the exact `F(s)` and the order
for DFAs are not determined** (`liminf F(s)/s² ≥ 1`, `limsup ≤ 4`;
Questions 53.1-53.2; *batch 73:* Part V lowers the `limsup` to at most 2,
and Part VI determines the order for complete DFAs);
the construction is genuinely nondeterministic; the finite checks do not
prove the all-`m` theorem, exhaust all `s`-state NFAs, prove the inherited
upper bound, determine `F(s)` or verify novelty.

**Part V**, kept from batch-73 manuscript 33 and its delivery README:
unrefereed, no Lean or other proof-assistant verification; no literature-wide
priority or global first-discovery claim; greedy parsing and cycle-mean
methods are classical (credited to Crochemore-Langiu-Mignosi, De Luca-Fici
and Karp), Schwarz's theorem and Part IV's lower family are imported, the
rank calculus and periodic-interior framework are the report's; **no tight
complexity of computing the slope, no eventual affine periodicity of `M_L`,
no smallest error bound, and no sharp leading constant or limit of
`F(s)/s²`** (the constant lies in `[1, 2]`); the effective procedure is not a
claim of an input-complexity bound (the period and the subset graph can be
large); the two boundary examples rule out two transient-only shortcuts, not
a state-count constant one; the finite checks do not prove the slope theorem,
exhaust all NFAs or verify Schwarz's theorem, and test hull targets only (no
systematic test of infinite-rank inputs or of the empty-word branch).

**Part VI**, kept from batch-73 manuscript 29 and its delivery README:
unrefereed, no Lean or other proof-assistant formalization; no global novelty
or worldwide priority claim, and no comprehensive search for equivalent
earlier crossover results; the rank clocks, periodic interiors,
deterministic safe cores, CRT arithmetic and clause testers (Stockmeyer-Meyer),
selector-to-cycle devices (Gawrychowski et al.) and the relation-power bound
(Schwarz) are credited background; **the bound `s² + 3` is proved for
complete DFAs only, not for NFAs** (its proof uses determinism); the lower
witness is not asserted to attain the maximal rank of its language, whose
exact rank is open (`(m−1)² + 2 ≤ R ≤ (m−1)² + 4`); state counts include the
selector and the rejecting sink; the exact `F_DFA(s)`, the lower-order terms,
and the complexity of the exact rank or least stabilization generation of one
DFA are not determined (Questions 74.1-74.4); the finite tests do not prove
the stripe lemmas, the complexity classification, every CRT reduction
instance or the asymptotic rank bounds, and no finite test exercises
`s² + 3`.

**Part VII**, kept from batch-73 manuscript 21 and its delivery README:
unrefereed, ordinary and computer-assisted proofs, no proof-assistant
certificate; no literature-wide priority claim (the provenance claim is
local to the pinned report); the primitive-exponent and high-exponent
structure results (Kirkland-Olesky-van den Driessche, with Lewin-Vitek) are
imported; the length-gate construction is Part IV's; **no exact `F(s)` for
`s ≥ 5`, no optimal additive term, and no leading constant one uniform in the
alphabet size** when `q` is comparable to `s`; the Hamiltonian and
near-Hamiltonian bounds have no matching lower constructions in their
classes; the lower family is sharp for the unrestricted class, not within
the primitive factor-universal class; the four-state counts are pruned
representative counts, not a distribution over all four-state NFAs; the
censuses record an empty hull as raw value 0 where the article puts
`R(L) = 1` (no extremal value is affected); the finite parameter,
template and family checks corroborate the proofs and are not premises; the
delivered reviews are the delivery's own, not refereeing.

## Questions answered or re-scoped by the batch-66 Parts

Dated notes (`[Added 30 September 2026, batch 66: …]`) record these in the
article; no question is printed as open where a Part answers it.

- Part I's **Question 11.2** ("Sharp regular-input complexity"): answered for
  NFAs (PSPACE-complete over two letters, Corollary 20.3); for DFAs Part II
  gives PSPACE (Theorem 19.2) and a safe-core criterion (Theorem 21.2); the
  exact DFA complexity stays open (Part II's Question 24.1).
- Part I's **Corollary 7.4**: EXPSPACE improved to PSPACE (Theorem 19.2).
- Part I's **Question 11.4** ("Grammar classes preserving context-freeness"):
  partly answered by Part III (regularity decidable for every context-free
  seed; complete classification for finitely stabilizing semilinear
  one-marker seeds); open in general (Part III's Question 42.1).
- Part I's **Question 11.6** ("Which rational counting series occur?"): Part
  III adds examples only.
- Part I's Questions 11.1 and 11.7 stay open; Part II's Questions 24.6 and
  24.7 restate or extend them (24.6 is printed as a pointer to 11.1).
- Part III's **Question 42.3** (explicit automata versus succinct rays):
  answered for NFAs by Part II; its DFA part stays open. Part III's
  conclusion gains the same note.
- Part I's Hughes Sections 13-14 note, its conclusion, its title-page note,
  its Section 10.2 and Appendix D gain one dated note each.

## Questions answered or re-scoped by Part IV (batch 71)

Dated notes (`[Added 1 October 2026, batch 71: …]`, the manuscript's own
date) record these in the article.

- Part II's **Question 24.2** ("The optimal finite rank bound"): answered as
  to order, for NFAs: `F(s) = Θ(s²)` (Theorem 47.1). The leading constant
  and the exact `F(s)` stay open (Question 53.1), and so does the order for
  DFAs (Question 53.2; the bounds for complete DFAs remain `⌊(s−3)/2⌋` and
  `(2s+5)²`). Notes after the question, after Theorem 22.1 and its comment
  ("The presently proved lower and upper orders … are linear and quadratic"),
  in Part II's delivered status and in its conclusion say so.
- Part II's Question 24.8 (formalization): Part IV's Question 53.4 asks the
  same for its construction (note after 24.8). Part II's Question 24.1 (DFA
  decision complexity) is unaffected (Part IV says so; Section 53).
- Part I's conclusion, its Section 10.2, its Appendix A note (the appendices
  now follow Part IV too) and Appendix D gain one dated note each. The title
  page gains none: it is already full, and a note there spills onto a second
  page.

## Questions answered or re-scoped by batch 73

Dated notes (`[Added 1 October 2026, batch 73: …]`) record these in the
article.

- Part II's **Question 24.3** ("Exact residue-wise rank slope"): answered in
  all three parts by Part V (Theorem 62.1): the limit of `M_L(n)/n` exists on
  every live residue without refining the period, is rational, and is
  computable. Notes after the question, after Part II's fixed-word dynamic
  program (Section 16.1, now a linear pass by Corollary 58.2), after
  Corollary 18.5 (now an exact slope) and in Part II's conclusion say so.
- Part II's **Question 24.2** and Part IV's **Question 53.1** (leading
  constant): narrowed, not answered: `(s−3)² ≤ F(s) ≤ 2(s−1)² + 3`, so the
  constant lies in `[1, 2]` (Corollary 64.2). Notes after both questions and
  in Part IV's Section 53 ("the gap between leading constants one and four")
  say so.
- Part II's Questions 24.4 and 24.5 bear on Part V's denominator bound
  `p(2^s − 1)` and its Question 65.3; neither is answered. Part V adds
  Questions 65.1-65.4 (complexity of the slope, denominators, distinguishing
  period, periodicity of the bounded error).
- Part II's **Question 24.1** ("Exact complexity for DFA input"): answered
  by Part VI (Theorem 67.1): coNP-complete, for both clocks; with it the DFA
  parts of Part I's Question 11.2 and Part III's Question 42.3 are settled
  (42.3 keeps the gap between explicit automata and succinct ray inputs).
  Notes after Part I's Corollary 7.4 and Question 11.2 and in its
  conclusion, in Part II's opening, delivered status, comparison table
  (Section 14.3), Section 21 ("no matching DFA lower bound"), after Question
  24.1 and in its conclusion, in Part III after its complexity remark
  (Section 39), after Question 42.3 and in its conclusion, and in Part IV's
  opening, its "Not affected" item and after its remark on the DFA decision
  question (Section 53) say so.
- Part IV's **Question 53.2** ("Order for DFAs"): answered by Part VI
  (Theorems 67.2 and 73.1): quadratic with leading constant one,
  `(s−7)² + 2 ≤ F_DFA(s) ≤ s² + 3` for `s ≥ 8` (before: Part II's linear
  lower bound; Part V had lowered the upper bound to `2(s−1)² + 3`, note after
  the question). Notes after Question 53.2, after Questions 24.2 and 53.1 (the
  NFA constant stays open) and after the comment on Part II's Theorem 22.1
  say so.
- Part II's **Question 24.5** (compressed periods and certificates): bears,
  for DFAs, by the write's observation: stripes are polynomial-size names
  and nonstabilization has a polynomial certificate, while a polynomial
  certificate of stabilization would give NP = coNP. Not answered.
- Part VI adds Questions 74.1-74.4 (exact `F_DFA(s)`, lower-order terms,
  exact rank of its family, complexity for one DFA).
- Part IV's **Question 53.1** ("Leading constant"): answered as to the
  constant by Part VII: it is one, `(s−3)² ≤ F(s) ≤ s² + 8s`
  (Theorem 76.2), over `q` letters `s² + max(8, 2q−4)s` (Theorem 81.1); the
  exact function is known for `s ≤ 4`, `1, 2, 5, 7` (Theorem 84.1). The exact
  `F(s)` for `s ≥ 5` and the additive term stay open. Notes after Questions
  24.2 and 53.1, after the comment on Theorem 22.1, in Part II's delivered
  status and conclusion, in Part IV's opening, its list of answers, its
  one-initial-state paragraph and Section 53, in Part V after Corollary 64.2
  and in its list of what it leaves open, and in Part VI after Theorem 73.1,
  its Lemmas 73.2-73.3 and at the end of Section 73 and in its list of what it
  leaves open say so.
- Two consequences recorded as the write's observations, not the
  manuscript's: `F_one(s)/s² → 1` (Part IV's single-initial-state family with
  Part VII's bound, which needs no assumption on the initial states; notes in
  Section 52 and Section 76), and Part V's `2(s−1)² + 3` stays the better
  bound for `s ≤ 11` (`s² + 8s` wins from `s = 12`).
- Part I's conclusion, its Appendix A note (the appendices follow Parts
  V-VII too) and Appendix D gain one dated note each for each of Parts V-VII
  (the Appendix A note is one sentence). The title page gains none (it is
  full).

## Notation

Article Section 1.5 has Part I's table (no symbol of manuscript 01 was
renamed). Sections 13.3 and 29.3 have the tables for Parts II and III. Ten
symbols of the batch-66 manuscripts were renamed, with no change of
normalization (and one of Part IV, one of Part V, two of Part VI and one of Part VII):

- Part II: the coordinate hull `𝓗(L)` is printed as Part I's `Rec(L)`;
  the regular delimiter languages `G(K)`, `B(K)` of Section 20.3 as
  `Ĝ(K)`, `B̂(K)`, because they are not Part I's `G_K`, `B_K`.
- Part III: the full closure `𝓗(L)` (`𝓗_R`) as `Rec(L)` (`Rec_R`), the same
  set by Theorem 3.3; the crossover map `𝓒(L)` as `T(L)`; the gap-ray
  language `T_s(a,d)` as `Gap_s(a,d)` and the finite union `T` of
  Lemma 36.1 as `𝒯`; the row equivalence `E_a(i,r)` as `Eq_a(i,r)` (Part I's
  `E_a` is the position support, Part III's `P_a^L`); the family `L_k` as
  `L^fam_k`; the threshold `T = 2^d + 1` in the proof of Theorem 39.2 as `θ`.
- Part IV (Section 46.3 has its table): the gate language `L_m` as
  `L^gate_m`, because Part II's `L_m` is the one-`1` family of Theorem 22.1,
  the very family whose bound Part IV improves. **Not renamed, and easy to
  misread:** Part IV's gate size is `m = s − 2`, Part II's constant is
  `m = s + 2`, and the index `m` of Part II's family `L_m` is its rank. Part IV's `S_m = ⟨m, m−1⟩` is a numerical semigroup, not
  Part I's seed family `S_q`; its `D_∥(s)`, `D_frozen(s)` are maxima over
  `s`-state NFAs, not Part II's `D_L(n)`; its `R(L)`, `F(s)`, `T_s`, `B_s`
  are Part II's.
- Part V (Section 55.3 has its table): the slope `λ_r` and the cycle mean `λ`
  as `σ_r`, `σ`, because Part III's `λ_v` is the velocity of a ray site, also
  a rational number in `[0, 1]`. Part V otherwise uses Part II's symbols.
  **Easy to misread:** its `ρ(v)` without a subscript counts liftable pieces
  of a phase word, not the rank `ρ_L`; its `H_{r,a_0}(m)` is a maximal rank,
  not Part IV's set `H_m`; its `L_3`, `L_4` are slices `L ∩ Σ^n`, not Part
  II's family `L_m`.
- Part VI (Section 66.3 has its table): the deterministic gate language
  `L_m` as `L^dfa_m` (Part II's `L_m` is the one-`1` family, Part IV's gate
  language `L^gate_m`), and the initial state `r` of its gate automaton
  (manuscript Section 6) as `q_in`, the manuscript's own name for an initial
  state, because `r` is a residue. **Easy to misread, and kept as
  delivered:** `C_{r,a}` is a stable alphabet but `C` in Section 73 an SCC;
  `d` is an SCC period (Sections 69, 73), a number of selector bits
  (Section 71) and the sink state (Section 72); its `t, p` in (88) are Part
  II's `T_s, p_s`, but in Section 73 a Schwarz transient and enlarged period;
  `κ_H` are cyclic classes, not Part V's relation-power index `κ`; `B`, `K`,
  `D` are not Part II's `B_s`, `K_s`, `D_L(n)`.
- Part VII (Section 75.3 has its table): the backward layers `B_j` as `R_j`,
  Part II's name for the same sets, because Part II's `B_s` is a constant and
  the manuscript uses `B` for three other things. **Easy to misread, and
  kept:** `F_2(s)`, `F_q(s)` carry the alphabet size as subscript (`F_3(s)` is
  ternary, `F_2(3) = 5`); `Γ_{r,a}` is Part II's `C_{r,a}`, while `C` is a
  component and `C_q = max(8, 2q−4)` a constant; `ω_n = (n−1)² + 1` is not
  Part III's clique number; in the manuscript's proof of Proposition 80.1
  (not reprinted) `H_m` and `T_m` are Part IV's `S_m` and `H_m`, **swapped**.

To watch: `⊗_c` is Hughes's constrained crossover (his `⊗_u` contains
concatenation); `L^[k]` is the parallel iteration, whereas Hughes's iterated
operations, read as for his iterated insertion, give the frozen-source `Y_k`
when both inputs are `L` (Part II writes `Y_{k+1} = Y_k ⊗_c L`, Parts I and
III `L ⊗_c Y_k`: the same set, since `⊗_c` returns both children);
`ρ_L(w)` (aligned-fragment rank) and `d_L(w)` (generation depth) are not
the sibling report's insertion degree `d_{A,B}(w)`; "no gaps" here concerns
ranks on a slice, not insertion spectra. Part II's `M_L(n)` is Part I's
`R_L(n)` on active slices, while Part II's `R(L)` is a supremum over all
lengths and Part III's `R ⊆ ℕ²` a marker mask. Part III's `P_a^L(i,j)` is
Part I's `(i,j) ∈ E_a`, and its zero-based `A_L(n,i)` is Part I's one-based
`P_{n,i+1}(L)`. Words are indexed with zero-based boundaries, `w[i:j]`
being positions `i+1..j` in Part I's one-based letter count.

## Relation to neighbouring reports

- **`automata-and-formal-languages/insertion-degree-spectra`** (*Gaps in
  Bounded-Shuffle Hierarchies*, the "ProveIt report" of Part I's
  Section 1.1, read at the pin; unchanged from the pin to the placement).
  Both reports start from Hughes's preprint, from different parts of it.
  That report answers questions of Hughes's Sections 10-11 on insertion
  degrees and iteration depth; its scope sentence says it addresses "the
  indicated no-gap questions, not the surrounding undecidability results",
  and it never names the crossover question. Part I answers one of those
  surrounding decision problems (Section 4), for crossover. No theorem is
  shared or used across the two. Part I's no-gap theorem for aligned rank
  (Theorem 3.4) is an analogue, for another operation, of that report's
  iteration-depth no-gap theorem (its Theorem 8.2); that report iterates
  with the inserted language held fixed, so its closest crossover
  counterpart here is the frozen-source iteration (Theorem 3.8). Hughes's
  singleton conjecture (that report's Question 21.1) stays open. Article
  Section 1.4 sets this out; that report carries a dated reciprocal remark
  under its scope sentence. Parts II-VII concern crossover only and use
  nothing from that report. A dated batch-66 note there (after its
  Corollary 4.3, commit `8140a0967`) extends that remark to Parts II and
  III, citing the `(2s+5)²` rank bound as "a quadratic bound"; it does not
  mention Part IV. That note stays true (Part IV adds a matching lower order
  for NFAs and changes nothing it says), and Part IV bears on nothing about
  insertion degrees, so no reciprocal note was added there in batch 71.
  The same holds for Part V (batch 73): its bound `2(s−1)² + 3` improves the
  quadratic bound that note cites without making the note false. That note
  also says that Part II places DFA input in PSPACE "whose exact complexity
  it leaves open"; this remains true of Part II, and Part VI (batch 73) now
  settles the DFA complexity (coNP-complete). No note was added there in
  this write; whether that dated note gains a further pointer is left to the
  catalogue step. Part VII bears on nothing about insertion degrees either.
- No other report of the research-report or surreal collections treats
  crossover of languages or cites Hughes's preprint (searched: crossover,
  Hughes, 2608.27755; the other reports using the word "crossover" use it in
  unrelated senses). `shuffle-six-state-bound` in this category concerns the
  state complexity of shuffle and shares no theorem with this report.

## Formal status

ProveIt has no formal development of crossover, aligned rank, context-free
grammars, Post correspondence, Parikh images, semilinear sets, Presburger
counting, distance-automaton limitedness, finite automata, unary
arithmetic-progression normal forms or space complexity classes (no ProveIt
Lean or Rocq file mentions NFAs, DFAs, PSPACE or Savitch; the vendored
`lib/Coq-Library-Undecidability` snapshot contains no grammar or PCP
files). The nearest formal neighbour is `Logic/PresburgerArithmetic`, whose
Lean development proves Cooper quantifier elimination for Presburger
arithmetic over the integers:
`PresburgerArithmetic.Formula.holds_iff_quantifierEliminate` and the
decision procedure `PresburgerArithmetic.Formula.presburgerArithmetic_decidable`
(`Logic/PresburgerArithmetic/Lean/PresburgerArithmetic/Decision.lean`), with
an independent Rocq proof of the one-variable Cooper step
(`Logic/PresburgerArithmetic/Coq/Cooper.v`). Part I's Lemma 8.2 and
Appendix B, and Part III's Lemma 31.4 and Theorems 32.1-33.2, invoke
Presburger decision procedures of this kind as effectivity steps; Part III
names that development as a possible bridge; none of them is connected to
it, and the Parikh and counting theorems they need are not formalized.
Part IV needs, besides finite automata, only the two-generator Frobenius
number (Lemma 49.2); no ProveIt Lean or Rocq file treats Frobenius numbers
or numerical semigroups (searched: `frobeniusNumber`, "Frobenius number"),
and Mathlib's pair-case Frobenius module, a possible formal route, was not
checked here (no Lean package tree is present in this checkout).
Part V needs, besides finite automata, Schwarz's index bound for powers of
a binary relation and maximum cycle means of finite weighted graphs; no
ProveIt Lean or Rocq file treats either (searched: "cycle mean", "relation
power"; the Lean files naming Schwarz use the Cauchy-Schwarz inequality).
Part VI needs strongly connected components and their periods, the
Chinese remainder theorem, and the complexity classes NP and coNP with
3SAT; ProveIt has no formal development of complexity classes or of
reductions (`git grep` for coNP, 3SAT, NP-complete and Cook-Levin over the
tracked Lean and Rocq files outside `lib/` finds only
`plon_NP_complete` in `Logic/Modal/Coq/CorsiVF.v`, a frame-completeness
theorem for a modal logic named NP, unrelated).
Part VII needs primitive digraphs and their exponents (Wielandt's bound and
the Kirkland-Olesky-van den Driessche structure theorems), Hall's theorem in
a regular bipartite multigraph, and the two-generator Frobenius formula; it
cites no formal source, and no ProveIt Lean or Rocq file treats primitive
exponents or crossover. Its small extrema are computer-assisted censuses in
C++ and Python, not certificates.
**Not formalized:** every statement of all seven Parts. No Lean build was
run for this report.

## Building

In a scratch directory holding a copy of `article.tex`:

    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

The committed PDF was built this way with MiKTeX pdfLaTeX (packages include
newtx, `shuffle`, fancyhdr, listings, tikz with the `automata` library,
hyperref; no BibTeX step): 156 US-letter pages, 0 errors, 0 warnings, 0
overfull or underfull boxes, no undefined or multiply-defined references or
citations and no duplicate destinations. The title page is excluded from
page anchors. All fonts are embedded; the two Type 3 fonts are the
`shuffle` package's bitmap symbol, as in the batch-44 build. Do not run
`make pdf` or `make clean` (`code/Makefile`,
`code/03-closure-classification-Makefile`),
`code/02-pspace-stabilization-build.sh`,
`code/04-quadratic-finite-rank-build.sh`,
`code/05-rational-slopes-build.sh`, `code/06-dfa-crossover-build.sh` or
`code/07-sharp-constant-build.sh` in this directory: they would leave
auxiliary files here, or fail. GNU `make` is not installed on the reference
machine anyway.

## Rerunning the checks

Never run a verifier in place: Part I's and Part II's verifiers default to
`data/verification.json`, Part III's always writes it, and that file is
Part I's receipt; Part II's example and Part III's verifier also import
sibling modules under their delivered names. Run each on a copy that
restores the delivered layout (Python >= 3.10, standard library only; `py`
on Windows, `python3` elsewhere).

**Part I:**

    mkdir run1 && cd run1
    cp -r <report>/code <report>/data .
    py code/verify.py

It prints the lines of `data/verification.txt` and rewrites
`run1/data/verification.json`. When Part I was written it was rerun this
way with Python 3.14.4: PASS with 1,766,639 checks in about 36 seconds; the
rewritten JSON equals the shipped one except for `elapsed_seconds` (and is
written with CRLF line endings on Windows), and the console output differs
from `data/verification.txt` only in the elapsed time and the receipt path.
Checks raise exceptions rather than use `assert`, so they stay active under
`python -O`.

**Part II:**

    mkdir -p run2/code run2/data && cd run2
    cp <report>/code/02-pspace-stabilization-verify.py code/verify.py
    cp <report>/code/02-pspace-stabilization-example.py code/example.py
    py code/verify.py --output data/verification.json
    py code/example.py

When Part II was written this ran with Python 3.14.4 in about 33 seconds:
PASS, every count and verdict equal to the shipped receipt; the JSON
differs from `data/02-pspace-stabilization-verification.json` only in
`python` and `elapsed_seconds` (and CRLF line endings on Windows), and the
console output from `data/02-pspace-stabilization-verification.txt` only in
those two lines and the receipt path. The example reports no finite
stabilization for the parity language of Example 22.3, an obstruction `01`
at residue 1, and ranks 3, 5, 9 for 1, 2, 4 pumped copies. Run ordinary
Python, not `python -O` (some checks are `assert`s).

**Part III:**

    mkdir -p run3/code run3/data run3/examples && cd run3
    cp <report>/code/03-closure-classification-verify.py code/verify.py
    cp <report>/code/03-closure-classification-crossover_masks.py code/crossover_masks.py
    py code/verify.py > data/verification.txt
    cp <report>/data/03-closure-classification-two_markers.json examples/two_markers.json
    py code/crossover_masks.py examples/two_markers.json --output examples/two_markers.out.json

(and likewise for `endpoint_cycle5`, `finite_point_exception`,
`five_markers` and `incompatible_velocities`). When Part III was written
the verifier printed PASS with 12,867 checks in about a second; its JSON
receipt differs from the shipped one only in `python` (3.14.4 instead of
3.13.5) and CRLF line endings; the five analyses equal the shipped
`.result.json` files after CRLF normalization. The analyzer alone imports
nothing from the package and may also be run in place on a shipped input,
printing to standard output.

**Part IV:** the checker imports nothing from the package, writes no file
and prints its JSON record to standard output, so it may be run from the
report directory as long as the output goes to a scratch path, never onto
the shipped record:

    py code/04-quadratic-finite-rank-check.py > <scratch>/verification-new.json

(`python3` elsewhere). Never use `python -O`: the checks are `assert`s. When
Part IV was written this ran with Python 3.14.4 in about three seconds
(from Git Bash) and its output equalled
`data/04-quadratic-finite-rank-verification.json` byte for byte; a shell
that writes CRLF line endings on Windows (for example PowerShell
redirection) makes the comparison hold only after normalizing them. The
record has no timing or version fields. Do not run
`code/04-quadratic-finite-rank-build.sh` (see "Building").

**Part V:** both checkers import nothing from the package, write no file and
print their records to standard output, so they may be run from the report
directory with the output sent to a scratch path:

    py code/05-rational-slopes-check_boundaries.py > <scratch>/boundary-verification-new.json
    py code/05-rational-slopes-verify_greedy.py > <scratch>/verification-new.json

(`python3` elsewhere; never `python -O`, the comparisons are `assert`s). The
delivered README's recipe (`python3 verify_greedy.py > verification-new.json;
diff -u verification.json verification-new.json`) is written for the
delivered layout and, run in place, would put new files beside the shipped
ones. When the batch was placed both ran on a copy with Python 3.14.4, the
boundary checker in about a second and the greedy checker in about 67
seconds, and printed the bytes of the shipped records apart from CRLF line
endings (Windows standard output); compare after normalizing them, or as
JSON. The records have no timing or version fields. Do not run
`code/05-rational-slopes-build.sh` (see "Building").

**Part VI:** the four checkers import nothing from the package, write no file
and print their records to standard output:

    py code/06-dfa-crossover-check_stripes_exhaustive.py > <scratch>/stripes-exhaustive-new.json
    py code/06-dfa-crossover-check_rank_family.py > <scratch>/rank-family-new.json
    py code/06-dfa-crossover-check_gate_completion.py > <scratch>/gate-completion-new.json
    py code/06-dfa-crossover-check_stripes_random.py > <scratch>/stripes-random-new.txt

(`python3` elsewhere; never `python -O`, the comparisons are `assert`s).
When the batch was placed the first three ran on a copy with Python 3.14.4
in 7, 8 and 11 seconds and printed the bytes of their shipped records apart
from CRLF line endings (compare after normalizing them, or as JSON). The
random checker takes about six minutes on that machine and prints its one
line only at the end (the two eight-state cases alone take about 72 and 149
seconds), so a run under a three-minute limit is not a hang; it was run in
three parts with the same random stream, and all 1,519 automata passed. The
delivered README's `diff -u` recipe reports spurious differences on Windows
because of CRLF. Do not run `code/06-dfa-crossover-build.sh` (see
"Building").

**Part VII:** its programs need the delivered layout and the unshipped
manuscript (see above), so rerun them in a fresh extraction of the delivered
archive, never in `code/`:

    mkdir run7 && cd run7
    git -C <repo> show f8c3a392a:docs/incoming/common-path-rank-package.zip > p.zip
    unzip -q p.zip
    PYTHONUTF8=1 py check_general.py > general-new.json
    PYTHONUTF8=1 py check.py > verification-new.json
    PYTHONUTF8=1 py check_templates.py
    PYTHONUTF8=1 py alphabet/check_fixed_alphabet_lemmas.py
    PYTHONUTF8=1 py alphabet/check_ternary_bookkeeping.py
    PYTHONUTF8=1 py exact/validate_receipts.py
    PYTHONUTF8=1 py exact/four_state/audit_families.py
    PYTHONUTF8=1 py exact/four_state/check_literal_four.py
    PYTHONUTF8=1 py exact/four_state/validate_receipts.py

(or `sh verify.sh` where `python3` resolves; it works in a temporary copy).
When the batch was placed these ran this way with Python 3.14.4 on the
shared machine, each within about three minutes: all passed, the outputs with
shipped records equalled them apart from CRLF line endings, `check_templates`
printed a pass record that has no shipped counterpart, and the two
`alphabet` checkers rewrote their receipts beside themselves, differing from
the shipped ones only in `"seconds"` (`check_ternary_bookkeeping.py` took
159 seconds on the loaded machine, against 7.5 recorded). Never use
`python -O`. The C++ censuses (`sh verify.sh --compile`,
`sh exact/reproduce.sh`, `sh exact/four_state/reproduce.sh`; g++ with C++17)
were **not** rerun; the receipts validate, and the reproduction scripts
replace result receipts in place, so run them only in such an extraction.

## Other discrepancies

- The delivered PDFs were 23 pages each for Parts I-III, 8 pages for
  Part IV, 11 for Part V, 12 for Part VI and 31 for Part VII; this build is 156, because the seven are one document
  with `[write]` text (Part I's Sections 1.4-1.5, its notes on the title
  page, in Sections 1.1, 2, 7, 10, 11 and 12 and in Appendices A and D;
  Sections 13, 29, 46, 55, 66 and 75; notes in Parts II-VII). The page size stays US letter. The
  contents list Parts II-VII by section only (`tocdepth` 1 from Part II on);
  Part I's appendices are listed under "Appendices to Part I" and are
  printed after Part VII.
- Part IV's bibliography cited this report as `ProveIt` (Part II, Question
  24.2, at the pin); those citations were replaced by internal references.
  Its `To` entry is the report's `To` (same paper; the manuscript adds the
  arXiv v1 date, 6 December 2008); `Manzoni`, `Wielandt` and `Neufeld` were
  added in the report's style. The write added `Sylvester` (J. J. Sylvester,
  *Educational Times* 41 (1884), 21) and `RamirezAlfonsin` (*The Diophantine
  Frobenius Problem*, 2005) for the credit after Lemma 49.2, which the
  manuscript proves directly without naming it. No DOI was checked online.
- Part IV's `lmodern` and `amssymb` packages are not loaded; the TikZ
  library `automata` was added for its figure, and the macros `\runs`,
  `\Lgate`, `\wsevone` and `\waddsevone` for its text and notes. The
  manuscript's `\cut` carried an outer `\mathbin`, which changes no spacing;
  the report's is used.
- Part IV's manuscript lists its four research questions as an unnumbered
  enumeration; they are printed as Questions 53.1-53.4 in the same order and
  words, with titles added by the write.
- Batch-71 notes are dated 1 October 2026, the date of the manuscript and
  the UTC date of the write; the commits carry 30 September 2026 in Pacific
  time.
- Part I's manuscript cites the sibling report by its article title, *Gaps in
  Bounded-Shuffle Hierarchies*; its directory is `insertion-degree-spectra`.
- Part II's and Part III's bibliographies cited Part I as `Repo`, which in
  Part I's own bibliography is the sibling report; those citations were
  replaced by internal references. Part III's `Esparza` entry is Part I's
  `EGKL` (same paper); the other new entries (To, Kao-Rampersad-Shallit,
  Savitch, Parikh, Ginsburg-Spanier, Barceló et al., Hague et al.,
  Ganardi-Ricros, Raz, Karp, Rosser-Schoenfeld) follow Part I's.
- Part III's Lemma 31.4 (effective Presburger supports) is Part I's
  Lemma 8.1, which manuscript 03 does not cite; the write added the credit,
  and the manuscript's transducer proof is kept as a second route.
- Parts II and III each reprove Part I's coordinate-hull theorem
  (Theorem 3.3): printed once, in Part I, with Part II's
  Proposition 15.2 / Corollary 15.3 and Part III's Lemma 31.3 kept as marked
  restatements with second and third proofs. Part IV restates the whole
  rank calculus once more (Proposition 48.1, with its definitions in
  Section 48), kept as a marked restatement with one more proof.
- Part II's tikz library `fit` (loaded by the manuscript, unused) and Part
  III's `lmodern` and `amssymb` packages are not loaded; the report keeps
  Part I's newtx fonts.
- `data/verification.json` records the delivered Part I run's
  `elapsed_seconds` (11.498) and `data/02-pspace-stabilization-verification.json`
  Part II's (8.272): machine timings.
- Part V's bibliography cited this report as `ProveIt` (Part II, Question
  24.3, at the pin) and Part IV's manuscript as `Quadratic`; both were
  replaced by internal references. Its `Manzoni` entry is the report's; its
  `Karp` entry (the 1978 cycle-mean paper) is printed as `KarpCycle`, because
  the report's `Karp` is Karp's 1972 reducibility paper; `CLM`, `DeLucaFici`
  and `Schwarz` were added in the report's style. No DOI was checked online.
- Part V's delivered abstract writes `O(1)` where its theorem writes
  `O_L(1)`; a note says the constant depends on `L` in both. Its `lmodern`
  and `amssymb` packages and its unused macros `\im`, `\runs` were not
  carried over.
- Part V's proof of its aligned path criterion (Lemma 58.1) repeats Part II's
  proof of Lemma 16.1 and is replaced by a pointer; its periodic-interior
  definitions (Section 59) restate Part II's Section 18 and are kept with a
  pointer, and its parity example (Section 63.2) is Part II's Example 22.3
  with the parities exchanged, kept with a note (the manuscript cites
  neither).
- Part V claims only `4 ≤ R(L) ≤ 5` for its second boundary example
  (Section 64.1); a literal computation made at placement (not shipped) gives
  `R(L) = 4` exactly. The delivered record
  `data/05-rational-slopes-boundary-verification.json` accordingly lists
  `"finite_rank_upper_bound": 5` for it, an upper bound, not the value.
- Part V's closing sentence of next questions is printed as Questions
  65.1-65.4, in the same order and words, with titles added by the write.
- Part VI's delivered source lost a `\rm` in one display (the sum over cyclic
  SCCs in Section 69, equation (91)): `\sum_{H\ {` and, on the next line,
  `m cyclic}}`, so its PDF prints the subscript as "H mcyclic"; the write
  prints `\sum_{H\ \mathrm{cyclic}}` and says so in a note.
- Part VI's bibliography cited this report as `ProveIt` (Part II, Question
  24.1, at the pin) and the manuscripts of Parts IV and V as `Quadratic` and
  `Slopes`; all were replaced by internal references. Its `Schwarz` entry is
  Part V's; `SM` (Stockmeyer-Meyer, STOC 1973) and `GLRSS` (Gawrychowski et
  al., arXiv:1702.03961v5) were added in the report's style. No DOI or arXiv
  version was checked online.
- Part VI's macros `\NP` and `\coNP` were added, and `\Ldfa` for the renamed
  language; its `lmodern` and `amssymb` packages are not loaded.
- Part VI's sentence of open refinements is printed as Questions 74.1-74.4,
  in the same order and words, with titles added by the write. Its gate
  lemma (Lemma 72.1) keeps its proof, although its first two assertions are
  Part IV's Lemmas 49.1-49.2 for a differently labelled gate; the note
  before it says so.
- Part VI's two lemmas on actual alphabets and on the joint entry and exit
  budget (Lemmas 73.2 and 73.3) are printed once, here, with their proofs.
- Part VII's bibliography cited this report as `Report` and the manuscripts
  of Parts IV and V as `Quadratic` and `Slopes`; all were replaced by internal
  references (its `Report` entry also called the report "prepared with
  OpenAI", whereas Parts I-III say ChatGPT). Its `Schwarz` entry, not cited in
  its text, is the report's; `KOV` was added in the report's style. No DOI or
  URL was checked online.
- Part VII's proofs of Lemmas 78.1, 79.1 and 79.2, Proposition 80.1 and
  Corollary 83.4 repeat proofs printed in Parts II, IV and VI and are
  replaced by pointers; the statements are kept. Its Lemma 79.1 adds a
  liveness clause to Part VI's Lemma 73.2, and the pointer says how the same
  proof gives it. Its greedy lemma (Lemma 83.1) is Part V's Lemma 57.1 and
  keeps its proof as a second proof; its parser and periodic-middle graph are
  Part V's, with boundary operators added.
- Part VII's manuscript says its lower construction "resolves the
  leading-coefficient question in the pinned report"; at the pin Part II's
  Question 24.2 asked only for the order, and the leading-constant question is
  Part IV's Question 53.1 (a note says so).
- Part VII's manuscript does not credit Part VI (written separately) for
  Lemmas 79.1-79.2 or Part V at its greedy lemma; notes there do.
- Part VII's delivered files are named `hamiltonian-rank.*` and its archive
  `common-path-rank-package`, names that predate its title; its README says
  the file name was kept from an earlier delivery, which is not in the
  repository.
- Part VII's unused macro `\ex` and its `lmodern` and `amssymb` packages were
  not carried over; its census tables are printed as delivered.
- Batch-73 notes are dated 1 October 2026, the date of the manuscripts and of
  the write.
