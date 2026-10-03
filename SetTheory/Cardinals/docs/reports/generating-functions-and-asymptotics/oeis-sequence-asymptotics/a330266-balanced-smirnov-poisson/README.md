# Fixed-Multiplicity Shuffles and Balanced Smirnov Words

**The e^-(k-1) law, Poisson adjacency statistics, and explicit corrections for OEIS A007060, A193624 and A330266, with a rigorous uniform remainder (Part II)**

This research report was first written on 1 October 2026 from one manuscript, manuscript 57 of batch 73 of ProveIt's incoming-reports intake (Part I). On 2 October 2026 a second manuscript, manuscript 11 of batch 77, was added as Part II: it proves the analytic step that Part I had only sketched. Neither manuscript has a personal author line: Part I's author field is the subtitle "A research note on OEIS A007060, A193624, A330266, and related sequences" (the delivered PDF's author metadata is empty), and Part II's reads "Mathematical repair and reproducibility report".

| Source | Manuscript | Archive | Pin | Arrived | Placed | Printed as |
|---|---|---|---|---|---|---|
| Part I | batch 73, manuscript 57 (cluster O2) | `ProveIt_Balanced_Smirnov_OEIS.zip` (main file `article.tex`, 17-page PDF *Fixed-multiplicity shuffles and balanced Smirnov words*) | none | `aa43cc555` | `6e193dd4f` | Sections 1–15, Appendices A–C (written in `728773045`) |
| Part II | batch 77, manuscript 11 (cluster P5) | `balanced-smirnov-repair-reproducibility.zip` (main file `balanced-smirnov-repair.tex`, 10-page PDF *A rigorous uniform remainder for balanced Smirnov asymptotics*, dated 2 October 2026) | `4b874cea0` | `096ee7b87` | `4f11bc9c0` | Part II: Sections II.1–II.9, Appendix II.A |

Part I's manuscript pins no repository revision and cites no repository file; its phrase "the inversion examples in the ProveIt repository" carries a citation (see below). Part II's manuscript pins `4b874cea0` and audits this report as it stood there (its `provenance/sources.json`, shipped as `data/02-repair-sources.json`, records SHA-256 checksums of `article.tex` and `README.md` at that commit; both files were unchanged between the batch-73O2 write `728773045` and that pin, and this write has changed both). Each placement commit deleted its archive from `docs/incoming`; the archives survive in `aa43cc555` and `096ee7b87`.

**Status: AI-assisted, unrefereed, not formalized.** The intake reran the shipped programs of both parts on copies and spot-checked the mathematics (Appendix C and Section II.9 of the article). It did not re-derive every proof.

## Files

```
README.md                                  this guide
sources.md                                 Part I's source notes, as delivered
article.tex                                the report (LaTeX, internal bibliography)
article.pdf                                the compiled report, 33 pages
02-repair-mathematical-audit.md            Part II's independent mathematical audit, as delivered
02-repair-integrated-review.md             Part II's integrated review of its manuscript, as delivered
02-repair-visual-qa.md                     Part II's visual check of its delivered 10-page PDF (not shipped), as delivered
code/verify.py                             Part I: exact enumeration (standard library): OEIS rows, the 52-card value, the convergence table
code/derive_symbolic.py                    Part I: SymPy check of the four factorial cumulants and the n^-3 expansion (prints only)
code/02-repair-check_operator.py           Part II: full operator calculation through N^-3, asserts the displayed identities (SymPy; prints only)
code/02-repair-check_independent.py        Part II: exact multiset-word enumeration, rational remainder-inequality checks, independent symbolic coefficients (SymPy; prints only)
code/02-repair-replay.sh                   Part II: the delivery's replay script (needs the delivered layout; see below)
data/verification.csv                      Part I: recorded convergence table (CRLF line endings, as delivered and as regenerated)
data/standard_deck.txt                     Part I: recorded 52-card computation and approximations
data/oeis_proposed_updates.txt             Part I: proposed OEIS comments, unsubmitted
data/02-repair-operator.txt                Part II: recorded output of the operator check
data/02-repair-independent.txt             Part II: recorded output of the independent check
data/02-repair-clean-replay.txt            Part II: the delivery's record of its clean replay (names /workspace paths)
data/02-repair-environment.txt             Part II: the delivery's Python, SymPy and TeX versions
data/02-repair-requirements.txt            Part II: sympy==1.14.0
data/02-repair-sources.json                Part II: source pin, SHA-256 of the inspected host files, literature links
```

Every file except `README.md`, `article.tex` and `article.pdf` is byte-identical to its delivery. `article.pdf` is a build of this `article.tex`, not a delivered PDF.

## Labels

Every label carries the prefix `bsw:`. Part I's 66 manuscript labels and the three added by its write (`bsw:rem:tail-sketch`, `bsw:sec:questions`, `bsw:app:provenance`) are unchanged: 69. Part II's labels carry the sub-prefix `bsw:rp:` — of the manuscript's 31 labels, 22 are kept unchanged after the prefix, one is renamed (`sec:gamma` → `bsw:rp:app:gamma`) and 8 are dropped with the formulas printed once (below); the write added 14 — 37 in all, **106** labels in the report. No label was renamed or removed.

## What is claimed

For fixed k ≥ 2, B(n,k) counts shuffles of kn cards (n ranks of k) with no two equal ranks adjacent, and X(n,k) is the number of equal-rank adjacencies.

| Result | Where | Status of the proof |
|---|---|---|
| Run-transform generating function | Theorem 2.1 | complete |
| Exact Laguerre integral, B(n,k) = ∫ e^-t ((-1)^k k! L_k^(-1)(t))^n dt | Theorem 3.1 | complete |
| Exact rook-number inclusion–exclusion and the factorial PGF | Theorem 4.1; second proof by bond contraction in Section II.3 | complete |
| X(n,k) → Poisson(k−1) by factorial moments | Theorem 5.1 | complete |
| **B(n,k)/(kn)! → e^-(k-1)**, Kirgizov's fixed-k conjecture on A330266 (29 September 2023; the case k = 4 was deduced on the entry by Radcliffe, 9 September 2025) | Corollary 5.2 | complete |
| Gamma representation | Proposition 6.1 | complete |
| All-orders Poincaré expansion of E(1+v)^X, uniform on compact v-sets | Theorem 6.2 | sketched in Part I (Remark 6.3); **proved in Part II** for fixed k: Theorems II.3.1, II.4.2, Corollary II.5.1 |
| Exact factorial-moment domination E(X)_M ≤ (k−1)^M | Theorem II.3.1 | complete |
| Explicit remainder sup over \|v\| ≤ V of the J-term operator expansion ≤ C(k,V,J)/N^(J+1), C(k,V,J) ≤ e^a T_(2J+2)(a), a = (k−1)V, for all n ≥ 1 | Theorem II.4.2 | complete |
| deg_v q_s ≤ s+1 for the log-coefficients, hence κ_r^(F) = O(n^(1−r)) | Theorem II.6.1 | complete |
| Exact factorial cumulants κ_1..κ_4; E X = k−1, Var X = (k−1) − (k−1)²/(kn−1) | Theorem 7.1 | complete (finite algebra) |
| Logarithmic expansion through n^-3; p(n,k) through n^-3; local probabilities to first order | Theorem 8.1, Corollaries 8.2, 8.3 | rest on Theorem 6.2: proved in Part II (Remark II.6.3; coefficients re-derived from the full operator in (70)) |
| Specializations k = 2..5, count and ratio expansions | Sections 9–10 | proved in Part II (Section II.7, with a second proof of the ratio) |
| Lambert-W inverse, error O(N0^-1) | Section 10.3 | proved in Part II, sharpened to O(1/(N0 log N0)) along the exact count sequence (71) |
| Exact 52-card value B(13,4) and initial terms for k = 5 | Sections 4, 9; Appendix B | exact computation |

**The tail estimate, sketched in Part I, is proved in Part II (batch 77P5).** Part I's Theorem 6.2 passed from the exact coefficientwise operator rule to an expansion uniform in v by asserting gamma Chernoff bounds, superexponential smallness of high-degree terms and cancellation of odd half-powers; Remark 6.3 recorded the gap and named the device that would close it, a uniform factorial-moment bound of the type proved in the path-forest report [`a189281-path-forest-expansions`](../a189281-path-forest-expansions/) (its Lemma 4.1, label `spf:lem:moment-bound`). Part II proves such a bound for this model directly (Theorem II.3.1), turns it into an explicit remainder that needs no gamma-tail estimate and no half-power cancellation (Theorem II.4.2, Corollary II.5.1), proves separately the degree statement behind the factorial-cumulant scale that Theorem 8.1's proof used (Theorem II.6.1; the existence of the expansion alone would not give it), and verifies the gamma-tail route as well (Appendix II.A). Every item Remark 6.3 lists as resting on the sketch is therefore proved, for fixed k (Remark II.6.3). Dated notes of 2 October 2026 say so at the editorial note, Remark 6.3, after Theorem 7.1, in the proof of Theorem 8.1, in Section 10.3, in Section 13, at research questions 7 and 11, and in Appendix C. The intake's numerics, kept as evidence: for k = 2..5 the residual after the n^-3 term, times e^(k-1) n^4, is 0.0598/0.0590, 0.153/0.151, 0.228/0.226, 0.232/0.230 at n = 100/400.

Every coefficient displayed in Part I is unchanged: Part II's manuscript re-derives them all (third-order log-PGF, log p and p, the k = 2..5 table, local masses, A_1..A_3, the ratio) and finds them identical. Nothing in Part I was false, so nothing is retracted.

## What is not claimed

- No complete literature search and no historical priority; the results should be independently checked before submission or attribution (Part I's scope paragraph). Part II likewise: its literature check is targeted, not exhaustive, and establishes no historical novelty; the Laguerre and rook-polynomial machinery is credited to Gessel, Taylor, Enouen and Eriksson–Martin, and the displayed coefficients to Part I.
- The numerical residual tables are diagnostics, "not used as proof"; Part II's finite checks "support reproducibility but are not substitutes for the proofs".
- The k = 5 terms of Appendix B should be cross-checked before any OEIS edit.
- `data/oeis_proposed_updates.txt` is unsubmitted; nothing has been sent to the OEIS. Its correction terms now rest on Part II's proof.
- Nothing uniform in k: both parts fix k; Part II asserts no uniformity for growing k and no uniform relative local approximation for a growing adjacency count (research question 1 stays open).
- Theorem II.3.1 is factorial-moment domination, not stochastic domination by a Poisson variable. Theorem II.6.1 concerns *factorial* cumulants; ordinary cumulants converge to k−1 and do not decay. The expansion of log Φ holds for the branch normalized at v = 0 (eq. (67) of Part II), not for an unspecified principal logarithm.
- No convergence of the infinite operator series at nonzero w is asserted; Section II.6 works formally in w.
- **The inversion method is not new.** Sections 10.3 and II.7.3 invert a gamma carrier perturbed by a 1/N series, which the canonical transseries volume `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/` treats in general (`p6:thm:gamma`, `p0:thm:perturbed-inversion`; integer thresholds in `p0:thm:staircase`; the dominant-block theorem `p0:thm:lambert-core` is named for contrast). Part II's sharper inverse holds along the exact count sequence only; for Y off the sequence an interpolation or threshold convention must be fixed, and asymptotic notation certifies no finite integer index. Keeping A_2, A_3 inside a single Newton step does not by itself give extra accuracy.
- No Lean or Rocq formalization; Section 12 is a proposed formalization route only. Part II is "not a peer-reviewed publication or a formal proof-assistant development".

## Relation to neighbouring material

- **Companion report** [`a189281-path-forest-expansions`](../a189281-path-forest-expansions/) (batch 73, manuscript 60): the same chain of method (marked-subset PGF, Poisson limit, all-orders 1/n expansion, Lambert-W inversion) for permutations avoiding a fixed positional and value offset, with limit Poisson(θ). Neither theorem specializes to the other: here the "value" relation is n cliques K_k, whose number grows with n, so that report's hypotheses (a fixed number of long paths) fail, and Part II states explicitly that its theorem "cannot simply be imported". Its factorial-moment bound is the device Remark 6.3 named; Part II proves the analogue for this model (Theorem II.3.1). Its first-order law for the whole distribution is the path-forest analogue of Corollary 8.3 here.
- **Fixed-composition excursions** (batch 73, [`a215561-fixed-composition-excursions`](../a215561-fixed-composition-excursions/)) also counts balanced multiset words normalized by (rn)!/(n!)^r, but with a prefix (ballot) constraint, a fixed number r of letters and growing multiplicity — the parameter roles are swapped relative to this report. No shared theorem.
- **Transseries volume**: the inversion apparatus cited above, and its chapter "The subfactorial" (`p8:sec:top`), which treats the derangement numbers by citing the same gamma carrier.
- **Formal status.** Placement in the collection confers no formal status, and no formal development continues this report; none of its statements is formalized.

## Notation of Part II

Part II keeps Part I's symbols where they agree (N = kn, λ = k−1, a_{k,m}, R_k, H_r(M), D = v d/dv, κ_r^(F), A_1..A_3, L, N_0). The manuscript's Φ_n is printed as Φ_{n,k} and its e as Part I's roman e. Renamed because they collide with Part I or with each other (the table of Section II.1 prints the reading to avoid beside each): P_s → 𝒫_s (Part I's P_k(t) are Laguerre kernels), p_j(M) → σ_j(M), truncation order L → J, C_{k,V,L} → 𝒞_{k,V,J} (Part I's C_k(z)), T_w → ℋ_w (the gamma variable T_N), A_w → 𝒜_w (A_1..A_3), S, S_s → Σ, Σ_s (the multiset count S_{n,k}), B_a → ℬ_a (the count B_{n,k}), c_j → γ_j, f(x), h(x) → ψ(x), g(x) in the inverse, and the gamma-tail cut J → M_N. The manuscript expands in N^-s, Part I in n^-s; a coefficient of N^-s is k^-s times that of n^-s. No formula changed its content.

## How Part II was merged

- Formulas Part I already displays — the third-order log-PGF, log p and p, the k = 2..5 coefficients, the local masses, log B with A_1..A_3, and the ratio — are cited, not printed a second time (the manuscript reprinted them in the variable N; the 8 dropped manuscript labels belong to those six displays and to its restatements of R_k and of Theorem 4.1's identity). The new log-coefficients q_1, q_2, q_3 are printed (eq. (70)). The manuscript's contraction proof of Theorem 4.1's identity, its ratio argument and its local computation are kept as marked second proofs.
- The manuscript's citations of "Theorem 6.2", "Remark 6.3" and "Theorem 4.1" of its pinned source, and its bibliography item for that source (this report itself), became cross-references. Its Eriksson–Martin and Enouen items are Part I's; Gessel and Taylor were added to the bibliography.
- Its Section 7 described its archive; it is rewritten to name the shipped files. Its "Source pin" appendix became Section II.9, where the sentence naming the report directory now says it is this report's own.
- Added by the write: the editorial note, Section II.1 (notation), Remark II.6.3 (what Part II settles in Part I), the bracketed notes, the provenance in Section II.9, the dated notes in Part I listed above, and a wider number box for the Part II entries of the contents. Nothing of either manuscript's mathematics, scope statements or disclaimers was removed.

## Building

From a scratch copy of `article.tex`, run

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX) produced the shipped `article.pdf`: 33 pages (Part I pages 1–20, Part II from page 21, bibliography pages 32–33), with no errors, no warnings, no undefined references or citations, no multiply defined labels, no duplicate destinations, and no overfull or underfull boxes. Copy back only `article.pdf`.

## Rerunning the programs

`code/verify.py` writes `data/verification.csv` and `data/standard_deck.txt` relative to the report root (`Path(__file__).parents[1] / "data"`), so running it in place overwrites the shipped records. Run everything on a copy:

```sh
R=SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a330266-balanced-smirnov-poisson
W=$(mktemp -d); cp -r "$R/code" "$R/data" "$W/"; cd "$W"
py code/verify.py                                                          # about 2 s
uv run --no-project --with sympy==1.14.0 python code/derive_symbolic.py     # about 20 s; prints only
uv run --no-project --with sympy==1.14.0 python code/02-repair-check_operator.py    > operator.txt     # about 10 s
uv run --no-project --with sympy==1.14.0 python code/02-repair-check_independent.py > independent.txt  # about 20 s
diff --strip-trailing-cr operator.txt    data/02-repair-operator.txt
diff --strip-trailing-cr independent.txt data/02-repair-independent.txt
```

Part I: the intake's run on a copy reproduced `data/verification.csv` byte for byte (Python's `csv` module writes CRLF on every platform, so the delivered file is CRLF too and is stored with a `-text` attribute). `data/standard_deck.txt` came out equal apart from line endings (CRLF from `write_text` on Windows; the delivered file is LF). `derive_symbolic.py` prints κ_1..κ_4 and confirms the n^-3 logarithmic expansion. Part I delivered no requirements file: `verify.py` needs only the standard library, `derive_symbolic.py` needs SymPy (the intake used 1.14.0).

Part II: both checks print to standard output and write no file. On Windows they write CRLF line endings; compare after converting to LF (`diff --strip-trailing-cr`, as above), or run under a POSIX Python. The intake's runs (SymPy 1.14.0 under Python 3.13.5 and 3.14.4, Windows; about 8 s and 20 s) matched both recorded outputs apart from line endings. **`code/02-repair-replay.sh` does not run in the shipped layout:** it expects the delivered tree (`scripts/check_*.py`, `results/*.txt`, `scripts/build_pdf.sh` and the manuscript `balanced-smirnov-repair.tex`), defaults to `python3`, and compares outputs byte for byte with `diff -u`, which fails on Windows on line endings alone. To use it, extract `balanced-smirnov-repair-reproducibility.zip` from `git show 096ee7b87:docs/incoming/balanced-smirnov-repair-reproducibility.zip` into a scratch directory and run `PYTHON=py bash scripts/replay.sh <new empty directory>` there under a POSIX shell; its PDF stage needs pdfLaTeX and Poppler's `pdfinfo`.

## Disclosures and discrepancies

- **Not shipped (Part I):** the delivered README (replaced by this one), the delivered 17-page PDF (replaced by a build of the edited text), the checksum ledger `MANIFEST.sha256` (verified 10/10 at placement and retired), and `data/pdfinfo.txt`, a `pdfinfo` dump of the delivered PDF.
- **Not shipped (Part II):** the manuscript `balanced-smirnov-repair.tex` (merged as Part II) and its 10-page PDF, the delivery README, the checksum ledger `SHA256SUMS` (verified 17/17 at placement and retired), `scripts/build_pdf.sh` (builds the unshipped standalone PDF; `code/02-repair-replay.sh` calls it), and `results/pdf-build.log` (log of that build). All remain in the archive in `096ee7b87`.
- **Renamed delivered files (Part II):** `scripts/X` → `code/02-repair-X` (`check_operator.py`, `check_independent.py`, `replay.sh`); `results/X` → `data/02-repair-X` (`operator.txt`, `independent.txt`, `clean-replay.txt`, `environment.txt`); `requirements.txt` → `data/02-repair-requirements.txt`; `provenance/sources.json` → `data/02-repair-sources.json`; `review/X` → `02-repair-X` at the report root (`mathematical-audit.md`, `integrated-review.md`, `visual-qa.md`).
- **Delivered files that use delivery names or name unshipped files:** `code/02-repair-replay.sh` (see above); `02-repair-mathematical-audit.md` audits a draft `balanced-smirnov-repair/repair.md` and a local copy `article-source.tex` of this report, and names its own `check.py` and `check-output.txt`, none of which was delivered (its checks correspond to `code/02-repair-check_independent.py`); its section numbers ("Sections 7–8", "Section 9") refer to that draft, not to Part II; `02-repair-integrated-review.md` reviews `balanced-smirnov-repair.tex` (it records that file's SHA-256) and calls Part I's results "Theorem 4.1", "Theorem 6.2" by Part I's numbers, which are unchanged; `02-repair-visual-qa.md` describes the 10-page delivered PDF, not this report's PDF; `data/02-repair-clean-replay.txt` records `/workspace/...` paths of the delivery's machine; `data/02-repair-sources.json` checksums are those of `article.tex` and `README.md` at `4b874cea0`, before this write.
- **Moved file (Part I).** The delivered `oeis_proposed_updates.txt` (archive root) is shipped as `data/oeis_proposed_updates.txt`. The article's sentence naming it carries a note giving the shipped path.
- **Edited text.** `article.tex` is Part I's delivered manuscript with the label prefix, citation commands at the first mentions of the OEIS entries and of the cited works (the manuscript cited none of its twelve bibliography entries), the names and dates of Kirgizov's and Radcliffe's OEIS contributions, the editorial note on the contents page, Remark 6.3, notes marked "[Added 1 October 2026, batch 73O2]" in Sections 10.3 and 13, one bibliography entry (the transseries volume), the label `bsw:sec:questions`, and Appendix C (batch-73O2 write); then the notes dated 2 October 2026, Part II, two bibliography entries (Gessel, Taylor), a clause in the transseries entry, and a macro for the contents (batch-77P5 write). Nothing was removed.
- **Unverified bibliographic detail.** The Mehiri reference is arXiv:2510.26597v2; the record exists, but the year 2026 the manuscript gives for v2 was not verified. Gessel's and Taylor's entries are as Part II's manuscript gives them; they were not re-checked by the intake.
- **Corollary 8.2's title** "No-adjacency transseries" is the manuscript's; the statement is an ordinary power series in 1/n.
