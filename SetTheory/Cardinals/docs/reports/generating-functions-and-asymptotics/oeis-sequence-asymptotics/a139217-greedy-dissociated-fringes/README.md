# Finite-Fringe Rigidity in Congruence-Restricted Greedy Dissociated Sequences

**Complete signed supports, closed forms, recurrence ranges, generating functions, counting functions and inverse branches for OEIS A139217 and A139218**

This research report is dated 1 October 2026. It was built from two
manuscripts of batch 73O1 (cluster O1 of batch 73) of ProveIt's
incoming-reports intake, written independently on the same day. Both prove
the same theorems, so each shared theorem is printed once and credited to
both, with the other proof as a marked second route. Neither manuscript is
superseded: each has results the other lacks.

| Source | Batch-73O1 manuscript | Archive (arrival commit) | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| base | 50 | `finite_fringe_oeis_A139217_A139218.zip` (`3a9518c52`); main file `finite_fringe_dissociated_sequences.tex`, *Finite-Fringe Rigidity in Congruence-Restricted Greedy Dissociated Sequences*, 20-page PDF | `c79d64038` | `9df4ba51a` | the whole text, in its order (Sections 1–5, 7–13, Appendices A–C) |
| member | 43 | `ProveIt_OEIS_A139217_A139218.zip` (`bdf1a1a73`); `article.tex`, *Boundary-Defect Rigidity in Congruence-Restricted Greedy Dissociated Sets*, 24-page PDF | none | `9df4ba51a` | second proofs and credits throughout; Corollary 3.4, Proposition 3.7, Section 6, the source-43 parts of Sections 7 and 9–12, Appendix D |

Author lines as delivered: source 50, "ProveIt research report (AI-assisted),
prepared for Vladimir Reshetnikov with OpenAI"; source 43, "Research draft
prepared for Vladimir Reshetnikov and the ProveIt project", with
"Computational assistant: OpenAI GPT-5.6 Sol Pro". Source 43 was written
first (archive members 17:23–17:30 UTC, source 50's 18:33–18:39). Source
50's pin `c79d640385588fda4b9fdb0cab9fce44790fd100` already contains source
43's archive, but source 50 never cites it, and the texts share nothing
beyond a 17-word run of LaTeX boilerplate: the two are independent.
The placement commit `9df4ba51a` staged the files below and deleted both
archives, which survive in their arrival commits.

**Status: AI-assisted, unrefereed, not formalized.** The intake re-derived
the sequences from the definition, rechecked the fringes, closed forms,
ranges, cross-identities, tables and counting functions in exact arithmetic,
and reran both verifiers on copies. It did not referee every proof.

## Files

```
README.md                                   this guide
article.tex                                 the merged report (pdfLaTeX, internal bibliography)
article.pdf                                 the compiled report, 35 pages
50-finite-fringe-oeis_update_draft.txt      source 50's proposed OEIS text, not submitted
43-boundary-OEIS_update_draft.txt           source 43's proposed OEIS text, not submitted
code/50-finite-fringe-verify.py             source 50's exact bitset verifier (standard library; prints only)
code/43-boundary-verify.py                  source 43's exact signed-set verifier (standard library; prints only)
data/43-boundary-verification_output.txt    source 43's recorded run of its verifier
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. Delivered name → shipped path:

| Source | Delivered | Shipped |
|---|---|---|
| 50 | `finite_fringe_dissociated_sequences.tex` | `article.tex` (rewritten in the merge) |
| 50 | `README.md` | replaced by this README |
| 50 | `verify.py` | `code/50-finite-fringe-verify.py` |
| 50 | `oeis_update_draft.txt` | `50-finite-fringe-oeis_update_draft.txt` |
| 50 | `finite_fringe_dissociated_sequences.pdf` | not shipped (`article.pdf` is a build of the merged text) |
| 43 | `article.tex`, `article.pdf`, `README.md` | not shipped (merged into `article.tex`; replaced by this README) |
| 43 | `verify.py` | `code/43-boundary-verify.py` |
| 43 | `verification_output.txt` | `data/43-boundary-verification_output.txt` |
| 43 | `OEIS_update_draft.txt` | `43-boundary-OEIS_update_draft.txt` |

## Labels, structure and notation

Every label carries the prefix `gdf:`. The staged base had **57** labels;
all are kept, unchanged after the prefix. The merge added **26** of source
43's 70 labels (also as `gdf:` plus 43's own name; no name occurs in both
manuscripts) and **41** new ones (sections, appendices, questions, the
threshold corollary and the forcing proposition): **124** in all. Source
43's other 44 labels named statements, equations and sections that duplicate
source 50's and are printed once.

Section 1.5 says what came from where; Section 1.6 is the notation table.
Source 50's notation is used throughout. Renamed from source 43: its defect
set `C` → `H`; its offsets `d_n`, `e_n` (the gap `S_n − a(n+1)`) → `−c_n`,
with the sign flipped to source 50's correction `c_n = a(n+1) − S_n`; its
leading constant `α` → `C`; its `Φ` → `Λ`; its truncation order `M` → `K`;
its shift operator `E` → `τ`; its generating-function variable `z` → `x`.
The two readings to avoid: source 43's `d_n` is **not** source 50's
`d_n = a(n+1) − 2a(n)`, and source 43's `C` is a set, not a constant. Text
added in the merge is marked "[Merge note, batch 73O1.]"; material only
source 43 has is marked "(source 43)".

## What is claimed

- For A139217 and every `n ≥ 3`, the signed subset-sum set is
  `[−S_n, S_n] ∖ {±(S_n − 3)}`; for A139218 it is
  `[−S_n, S_n] ∖ {±(S_n − h) : h ∈ {1, 3, 6, 11}}` (both sources).
- A general finite-fringe propagation theorem (source 50) with a sharp
  collision condition; source 43's threshold form `S > 2M + |c|` is its
  corollary, with source 43's direct proof as a second route.
- Closed forms: A139217 `a(n) = 3·2^(n−2) + (1, 1, −2)` from `n = 3`;
  A139218 `a(n) = (39/56)·2^n + (−25/7, 20/7, 5/7)` from `n = 4`; partial
  sums from `n = 3`; the period-three deviations `a(n+1) − 2a(n)`; rational
  generating functions with denominator `(1 − 2x)(1 + x + x²)` (both sources).
- The recurrence `a(n) = a(n−1) + a(n−2) + 2a(n−3)` holds for A139217 from
  `n = 6` (it also holds at `n = 4` and fails at `n = 5`, so OEIS's "n > 4"
  is false) and for A139218 from `n = 7`, as OEIS conjectures (both sources).
- Cross-identities `14v_n − 13u_n ∈ {−63, 27, 36}` (`n ≥ 4`) and
  `14V_n − 13U_n ∈ {54, 81, 117}` (`n ≥ 3`); signed-set sizes `2U_n − 1`,
  `2V_n − 7` (source 43).
- Exact counting functions valid for every real `x`, with
  `N(x) = log₂ x + O(1)` and a log-periodic staircase (both sources; the
  asymptotics are source 43's).
- Convergent logarithmic and ratio expansions in `2^(−n)` (source 50) and
  convergent residue-branch inverse series in `1/x` (both), with an explicit
  truncation bound and explicit low-order coefficients (source 43).

## What is not claimed

- No priority: both sources made targeted, not exhaustive, literature
  searches and found no published proof.
- No classification of the general congruence-restricted greedy problem
  for other `(m, r)`; source 50's ten questions and source 43's 22
  enumerated questions stay open (Section 12). Source 43's item 12 (sharp
  propagation thresholds) is re-scoped by a merge note: source 50's theorem
  replaces the threshold by a collision condition, while the earliest
  stabilization index stays open.
- Nothing is formalized; the verifiers are audits, not proofs of the infinite
  statements.
- The word "transseries" in source 50's title and Section 7 is loose: every
  expansion here is a convergent series, with no exponentially small sectors.
- The proposed OEIS texts have not been submitted.

## Relation to neighbouring material

- **Collection neighbours.** No other report in the repository treats
  A139217, A139218 or greedy dissociated sets. Single-sequence formula proofs
  of the same shape live beside it in `oeis-sequence-asymptotics`, for
  example [`a260306-formula-proof`](../a260306-formula-proof/) and
  [`a003407-dyadic-scaling-rigidity`](../a003407-dyadic-scaling-rigidity/).
  Source 50 mentions [`a290268-unbounded-deficits`](../a290268-unbounded-deficits/)
  only as the pattern it followed; there is no mathematical link (merge note
  in Section 1.4).
- **Transseries.** Source 43 places its inverse expansions in the
  repository's series-and-transseries programme
  (`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion`).
  They are convergent Taylor series of `log(1 − p/x)` and need nothing from
  that volume.
- **Lean.** Neither manuscript ships or cites Lean or Rocq proofs. The Lean
  declarations named in Section 11 (`dissociated_cons_iff_not_mem_signedDiffs`,
  `boundaryModel_propagate`, `subsetSums`, `signedDiffs`, …) are the sources'
  proposals and do not exist in ProveIt. No statement of this report is
  formalized, and placement in the collection confers no formal status.

## Building

From a scratch copy of this directory, run

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX 26.2) produced the shipped `article.pdf`: 35 pages (title
and abstract page 1, contents page 2), with no errors, no warnings, no
undefined references or citations, no multiply defined labels, no duplicate
destinations, no overfull boxes and one underfull line (badness 1173, a
merge note in Section 7.4). Copy back only `article.pdf`.

## Rerunning the verifiers

Both verifiers use only the Python standard library, print to standard
output and write no file, so they can be run in place:

```sh
R=SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a139217-greedy-dissociated-fringes
py "$R/code/50-finite-fringe-verify.py"   # about 1 s; 22 terms, fringes, closed forms, GFs to x^30
py "$R/code/43-boundary-verify.py"        # about 30 s; 17 terms, signed sets, counting functions, n = 5 failure
```

The intake ran both on copies: source 43's standard output equals
`data/43-boundary-verification_output.txt` byte for byte (on Windows,
redirecting `print` output to a file gives CRLF line endings, so compare
ignoring line endings). Source 50 shipped no recorded output; its run ends
with the lines quoted in Section 9.2, plus two `a(22)=…` lines per sequence
that the article abbreviates as `...`. Source 50's verifier does not check
the counting functions, the cross-identities or the failure at `n = 5`;
source 43's does.

## Disclosures and discrepancies

- **Fixes made in the merge** (the delivered files keep their text):
  - Source 43 calls the A139217 range `n ≥ 6` "sharp ... the identity fails
    at n=5". The recurrence also holds at `n = 4`; a merge note gives the
    exact statement (Section 4.3).
  - Source 43 states `V_n = (39/28)2^n + s_n` and `14V_n − 13U_n` for
    `n ≥ 4` only; both hold from `n = 3` (merge notes in Sections 5 and 6).
    The shipped `43-boundary-OEIS_update_draft.txt` still says "For n >= 4"
    for the A139218 partial sums.
  - Source 50's A139218 counting function used
    `max{0, ⌊log_8((56x+200)/39)⌋ − 1}`, undefined for `x ≤ −25/7`. The
    report prints source 43's equivalent `Λ((7x+25)/39)`, defined for every
    real `x` and equal to it for `x > −25/7` (merge note in Section 7.4).
  - Source 50's hard-coded "Section 6" is now a cross-reference, and its
    three uncited bibliography items (the two OEIS entries and the
    repository) are cited.
- **Delivery names in shipped text.** `code/43-boundary-verify.py` says it
  is "not a substitute for the proofs in article.tex", and
  `43-boundary-OEIS_update_draft.txt` refers to "the accompanying research
  article": both mean source 43's manuscript, which is not shipped and is
  printed in the merged `article.tex`. The article's names `verify.py` are
  rewritten to the shipped paths.
- **External claims.** The OEIS formula lines of A139217 and A139218
  ("for n>4", "for n>6", Layman, April 2008) were confirmed live on
  1 October 2026. The other references (Dutta's arXiv preprint and the
  classical papers) were not re-checked.
- **Not shipped:** both delivered PDFs and READMEs, and source 43's
  manuscript. Neither package had a checksum ledger.
