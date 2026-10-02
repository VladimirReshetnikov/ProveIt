# Fixed-Multiplicity Shuffles and Balanced Smirnov Words

**The e^-(k-1) law, Poisson adjacency statistics, and explicit corrections for OEIS A007060, A193624 and A330266**

This research report is dated 1 October 2026. It was built from one manuscript, manuscript 57 of batch 73 of ProveIt's incoming-reports intake. The manuscript has no author or preparer line: its author field is the subtitle "A research note on OEIS A007060, A193624, A330266, and related sequences", and the delivered PDF's author metadata is empty.

| Source | Batch-73 manuscript | Archive | Pin | Arrived | Placed | Printed as |
|---|---|---|---|---|---|---|
| sole | 57 (cluster O2) | `ProveIt_Balanced_Smirnov_OEIS.zip` (main file `article.tex`, 17-page PDF *Fixed-multiplicity shuffles and balanced Smirnov words*) | none | `aa43cc555` | `6e193dd4f` | the whole article |

The manuscript pins no repository revision and cites no repository file; its phrase "the inversion examples in the ProveIt repository" now carries a citation (see below). The archive arrived in `aa43cc555`; the placement commit `6e193dd4f` deleted it from `docs/incoming`, and it survives in `aa43cc555`.

**Status: AI-assisted, unrefereed, not formalized.** The intake reran both shipped programs on a copy and spot-checked the mathematics (Appendix C of the article). It did not re-derive every proof.

## Files

```
README.md                        this guide
sources.md                       the manuscript's source notes, as delivered
article.tex                      the report (LaTeX, internal bibliography)
article.pdf                      the compiled report, 19 pages
code/verify.py                   exact enumeration (standard library): OEIS rows, the 52-card value, the convergence table
code/derive_symbolic.py          SymPy check of the four factorial cumulants and the n^-3 expansion (prints only)
data/verification.csv            recorded convergence table (CRLF line endings, as delivered and as regenerated)
data/standard_deck.txt           recorded 52-card computation and approximations
data/oeis_proposed_updates.txt   proposed OEIS comments, unsubmitted
```

Every file except `README.md`, `article.tex` and `article.pdf` is byte-identical to the delivery. `article.pdf` is a build of this `article.tex`, not the delivered PDF.

## Labels

Every label carries the prefix `bsw:`. The manuscript's 66 labels are kept, unchanged after the prefix. The write added three: `bsw:rem:tail-sketch`, `bsw:sec:questions` and `bsw:app:provenance` (69 in all).

## What is claimed

For fixed k ≥ 2, B(n,k) counts shuffles of kn cards (n ranks of k) with no two equal ranks adjacent, and X(n,k) is the number of equal-rank adjacencies.

| Result | Where | Status of the proof |
|---|---|---|
| Run-transform generating function | Theorem 2.1 | complete |
| Exact Laguerre integral, B(n,k) = ∫ e^-t ((-1)^k k! L_k^(-1)(t))^n dt | Theorem 3.1 | complete |
| Exact rook-number inclusion–exclusion and the factorial PGF | Theorem 4.1 | complete |
| X(n,k) → Poisson(k−1) by factorial moments | Theorem 5.1 | complete |
| **B(n,k)/(kn)! → e^-(k-1)**, Kirgizov's fixed-k conjecture on A330266 (29 September 2023; the case k = 4 was deduced on the entry by Radcliffe, 9 September 2025) | Corollary 5.2 | complete |
| Gamma representation | Proposition 6.1 | complete |
| All-orders Poincaré expansion of E(1+v)^X, uniform on compact v-sets | Theorem 6.2 | **tail estimate sketched** (Remark 6.3) |
| Exact factorial cumulants κ_1..κ_4; E X = k−1, Var X = (k−1) − (k−1)²/(kn−1) | Theorem 7.1 | complete (finite algebra) |
| Logarithmic expansion through n^-3; p(n,k) through n^-3; local probabilities to first order | Theorem 8.1, Corollaries 8.2, 8.3 | rest on the sketched step |
| Specializations k = 2..5, count, ratio and Lambert-W inverse expansions | Sections 9–10 | rest on the sketched step |
| Exact 52-card value B(13,4) and initial terms for k = 5 | Sections 4, 9; Appendix B | exact computation |

**The tail estimate is sketched.** In Theorem 6.2 the passage from the exact coefficientwise operator rule to an expansion uniform in v (gamma Chernoff bounds, superexponential smallness of high-degree terms, cancellation of odd half-powers) is asserted, not derived. A uniform factorial-moment bound of the type proved in the companion path-forest report — [`a189281-path-forest-expansions`](../a189281-path-forest-expansions/), Lemma 4.1 "Uniform factorial-moment bound", label `spf:lem:moment-bound` — would make the truncation rigorous; that lemma is proved there for its own model, not here. Remark 6.3 lists what depends on the sketch. The limit law (Corollary 5.2) does not. The intake's numerics are consistent with the displayed coefficients: for k = 2..5 the residual after the n^-3 term, times e^(k-1) n^4, is 0.0598/0.0590, 0.153/0.151, 0.228/0.226, 0.232/0.230 at n = 100/400.

## What is not claimed

- No complete literature search and no historical priority; the results should be independently checked before submission or attribution (the manuscript's own scope paragraph).
- The numerical residual tables are diagnostics, "not used as proof".
- The k = 5 terms of Appendix B should be cross-checked before any OEIS edit.
- `data/oeis_proposed_updates.txt` is unsubmitted; nothing has been sent to the OEIS. Its correction terms rest on the sketched step.
- Nothing uniform in k: the fixed-k proof does not extend to growing multiplicity (research question 1).
- **The inversion method is not new.** Section 10.3 inverts a gamma carrier perturbed by a 1/N series, which the canonical transseries volume `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/` treats in general (`p6:thm:gamma`, `p0:thm:perturbed-inversion`; integer thresholds in `p0:thm:staircase`). A note there cites it; no novelty is claimed.
- No Lean or Rocq formalization; Section 12 is a proposed formalization route only.

## Relation to neighbouring material

- **Companion report** [`a189281-path-forest-expansions`](../a189281-path-forest-expansions/) (batch 73, manuscript 60): the same chain of method (marked-subset PGF, Poisson limit, all-orders 1/n expansion, Lambert-W inversion) for permutations avoiding a fixed positional and value offset, with limit Poisson(θ). Neither theorem specializes to the other: here the "value" relation is n cliques K_k, whose number grows with n, so that report's hypotheses (a fixed number of long paths) fail. Its factorial-moment bound is the device named above. Its first-order law for the whole distribution is the path-forest analogue of Corollary 8.3 here.
- **Fixed-composition excursions** (batch 73, [`a215561-fixed-composition-excursions`](../a215561-fixed-composition-excursions/)) also counts balanced multiset words normalized by (rn)!/(n!)^r, but with a prefix (ballot) constraint, a fixed number r of letters and growing multiplicity — the parameter roles are swapped relative to this report. No shared theorem.
- **Transseries volume**: the inversion apparatus cited above, and its chapter "The subfactorial" (`p8:sec:top`), which treats the derangement numbers by citing the same gamma carrier.
- **Formal status.** Placement in the collection confers no formal status, and no formal development continues this report; none of its statements is formalized.

## Building

From a scratch copy of `article.tex`, run

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX) produced the shipped `article.pdf`: 19 pages, with no errors, no warnings, no undefined references or citations, no multiply defined labels, no duplicate destinations, and no overfull or underfull boxes. Copy back only `article.pdf`.

## Rerunning the programs

`code/verify.py` writes `data/verification.csv` and `data/standard_deck.txt` relative to the report root (`Path(__file__).parents[1] / "data"`), so running it in place overwrites the shipped records. Run it on a copy:

```sh
R=SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a330266-balanced-smirnov-poisson
W=$(mktemp -d); cp -r "$R/code" "$R/data" "$W/"; cd "$W"
py code/verify.py                                                          # about 2 s
uv run --no-project --with sympy==1.14.0 python code/derive_symbolic.py     # about 20 s; prints only
```

The intake's run on a copy reproduced `data/verification.csv` byte for byte (Python's `csv` module writes CRLF on every platform, so the delivered file is CRLF too and is stored with a `-text` attribute). `data/standard_deck.txt` came out equal apart from line endings (CRLF from `write_text` on Windows; the delivered file is LF). `derive_symbolic.py` prints κ_1..κ_4 and confirms the n^-3 logarithmic expansion. No requirements file was delivered: `verify.py` needs only the standard library, `derive_symbolic.py` needs SymPy (the intake used 1.14.0).

## Disclosures and discrepancies

- **Not shipped:** the delivered README (replaced by this one), the delivered 17-page PDF (replaced by a build of the edited text), the checksum ledger `MANIFEST.sha256` (verified 10/10 at placement and retired), and `data/pdfinfo.txt`, a `pdfinfo` dump of the delivered PDF.
- **Moved file.** The delivered `oeis_proposed_updates.txt` (archive root) is shipped as `data/oeis_proposed_updates.txt`. The article's sentence naming it now carries a note giving the shipped path.
- **Edited text.** `article.tex` is the delivered manuscript with the label prefix, citation commands at the first mentions of the OEIS entries and of the cited works (the manuscript cited none of its twelve bibliography entries), the names and dates of Kirgizov's and Radcliffe's OEIS contributions, the editorial note on the contents page, Remark 6.3, notes marked "[Added 1 October 2026, batch 73O2]" in Sections 10.3 and 13, one bibliography entry (the transseries volume), the label `bsw:sec:questions`, and Appendix C. Nothing was removed.
- **Unverified bibliographic detail.** The Mehiri reference is arXiv:2510.26597v2; the record exists, but the year 2026 the manuscript gives for v2 was not verified.
- **Corollary 8.2's title** "No-adjacency transseries" is the manuscript's; the statement is an ordinary power series in 1/n.
