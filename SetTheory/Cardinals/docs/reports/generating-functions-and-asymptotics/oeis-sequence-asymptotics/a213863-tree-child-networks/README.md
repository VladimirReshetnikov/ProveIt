# Airy Asymptotics for Tree-Child Networks

**Fixed combining degree, and the binary total count, deficit law and inverse (A213863)**

This research report, dated 2 October 2026, was built from two manuscripts of batch 77.
Neither manuscript names an author; both are AI-assisted research reports.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 16 (base) | batch 77, manuscript 16 | `d-combining-asymptotics-reproducibility.zip` (main file `d-combining-asymptotics.tex`, 406 lines, 10-page PDF) | none | `34f1acd4b` | Part I, Sections 2–13 |
| 69 | batch 77, manuscript 69 | `tree-child-asymptotics-reproducibility.zip` (main file `article/tree-child-asymptotics.tex`, 1,233 lines, 23-page PDF) | none | `34f1acd4b` | Part II, Sections 14–20 |

Both archives arrived in commit `096ee7b87`. They were placed in this directory by `34f1acd4b`
(batch 77P3) and written into this report in batch 77P3, step 3 of 7. Neither manuscript names a
repository commit, so neither has a pin.

**Status.** AI-assisted research report, unrefereed and not formalized. No statement of this report has a
Lean or Rocq declaration. Each source's audits are independent research review by its producer, not
external peer review, publication, a proof-assistant check or numerical certification. Neither source
was published or submitted anywhere.

## What the report proves, and what it does not

**Claimed (Part I, source 16).** Fix d ≥ 2. Let a_n be the maximal-word diagonal of d-combining
tree-child networks, so that T^(d)_{n,n−1} = n!·a_{n−1}. Then
a_n = γ_d (n!)^(d−1) Γ^n exp(B n^(1/3)) n^ρ (1 + Σ C_{d,r} n^(−r/3)), to every finite order
(Theorem 2.1). Here Λ = (d+1)^(d−1)/(d−1)!, Γ = 4Λ, B = 3z((d−1)/(d+1))^(2/3) with z the largest zero of Ai,
ρ = −η − 1/2, η = (d−1)²/(2(d+1)), and C_{d,r} ∈ ℚ[B]. The amplitude γ_d > 0 is defined by convergent
limits. The same holds for T^(d)_{n,n−1}. For d ≥ 3 the total count gets only its leading equivalent.
Part I also gives the ternary logarithmic coefficients and a Lambert-W inverse with integer brackets.
At d = 2 the diagonal is A213863.

**Claimed (Part II, source 69, d = 2).** Theorem 14.1 is Theorem 2.1 at d = 2, with the explicit coefficients
c₁ = B²/18, c₂ = B⁴/648 and c₃ = B⁶/34992 − 1/9 (B = 3^(1/3) z), and four logarithmic coefficients. It has
its own complete proof in Section 15, printed as a second route. Theorem 16.2 transfers every finite order
to the total number TC_n of binary tree-child networks, with no new constant:
TC_n = (√e γ/12)(n!)² 12^n e^(B n^(1/3)) n^(−5/3) exp{B²/18 n^(−1/3) − 23B/72 n^(−2/3) + 161/288 n^(−1) + …}.
It rests on the Pons–Batle identity, proved by Lin–Liu–Liu–Liu–Xin (arXiv:2601.09551v3), together with
Chang et al. 2024. Theorem 18.1 expands the reticulation-deficit law around Poisson(1/2) with weights
e^(θm). Theorem 18.2 proves the exact eventual identity d_TV = (3/2)(1/ℛ_n − e^(−1/2)), where
ℛ_n = T_{n+1}/((n+1)! a_n), with
d_TV = |B|/(48√e) n^(−2/3) − 1/(192√e) n^(−1) + 167B²/(34560√e) n^(−4/3) + O(n^(−5/3)). Part II also gives
PGF and moment corrections and explicit inverses with integer brackets (Section 17).

**Not claimed by either source:**
- uniformity as d → ∞;
- convergence of any infinite series;
- exponentially small or transseries corrections;
- higher-order total-count corrections for d ≥ 3;
- a d ≥ 3 OEIS accession;
- a closed form, certified digits or an effective error constant for any amplitude;
- a certified threshold algorithm or an unconditional ceiling rule;
- novelty beyond a bounded literature search.

The uncertified diagnostic γ₂ ≈ 2.02264201 (Section 19) is not a claimed value.

The Lambert-W inversions are instances of the repository volume *Transseries and inversion*
(`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`, theorems
`p0:thm:lambert-core`, `p0:thm:perturbed-inversion`, `p0:thm:staircase`; Remark 11.1). No novelty is
claimed for them.

## How the two sources are merged

- **Base.** Source 16 (general d) is Part I, printed in full. Source 69 (d = 2) is Part II, printed in full,
  in its own order. Each Part opens with its source's abstract.
- **No result is dropped.** Source 69's Sections 2–8 prove Theorem 2.1 at d = 2, step by step. They are
  printed as Section 15, a detailed second route, because they hold binary-only explicit material: the
  quasimode φ₂, φ₃, the eigenvalue through ε⁵, s₂…s₇, h₁…h₃, the endpoint expansion and the N^(−4/3)
  coefficient. Four displays are literally identical in both sources and are printed once, in Part I:
  the polynomial–Airy identity, the triangular equation, the convolution estimate and the Catalan smoothing
  bound. Part II points to them.
- **Source 16's red flags** (batch-77 dossier R16.1–R16.3):
  - Its bibliography entry `Binary` had no locator. It is replaced by references to Part II
    (Section 10; bibliography note).
  - Its one-paragraph compactness step is spelled out in Remark 5.1, assembled from its shipped
    `16-dcomb-expanded-proof.md` and source 69's Section 3. The remark adds no new idea.
  - Its hash receipts name `/workspace/shared/…` paths; see the disclosures below.
- **Source 69's red flags** (R69.1–R69.2):
  - Its Sections 9 and 11 were converted Markdown. Their bold "Theorem"/"Proof" paragraphs are now
    environments (Theorems 16.2, 18.1, 18.2), and the inline `\href` citations are bibliography citations.
    The equation tags T1–T24 and D1–D14 are kept, and each now has a label. Source 69 has no tag D12.
  - Its sentence on an "extended-precision run" is qualified in Section 19. NumPy's `longdouble` is the
    80-bit format on x86-64 Linux, and the recorded run shows nonzero differences up to 2.0e−14. On Windows
    a rerun compares double with double and is vacuous.
- **Re-scoped question.** Source 16's open question 1 (all-order total counts) is settled at d = 2 by
  Part II and stays open for d ≥ 3 (Section 12).
- **Notation.** Each Part keeps its source's notation except for the renamings in the table of
  Section 1.4, which also prints the tempting false readings. The main renamings:
  - source 69's d_N(j), a_{N,j} → D_N(j), p_N(j) (Part I's, identical at d = 2);
  - its deficit ratio b_n(m) → β_n(m), and q_{n,m}, Q_m(t), G(t) → ω_{n,m}, Ω_m(t), 𝒢(t);
  - its R_n, r_s, M_n, π(m), p_n(m), ℓ_n(m) → ℛ_n, τ_s, X_n, π_{1/2}(m), π_n(m), lr_n(m);
  - its gap constant c₁ → a₂ (c₁ is also B²/18);
  - α_N → ξ_N in both sources (α is the network exponent);
  - the Duhamel window L → Δ in both;
  - source 16's inversion letters p, r, K, L_j, a, A → 𝗉, 𝗋, 𝖪, 𝖫_j, 𝖺, γ⋆;
  - source 69's generic-inverse letters → sans-serif (Section 17);
  - its target logarithm T → y, and its threshold ρ, η, r, N(Y) → σ, δ_Y, x_Y, 𝒩(Y).

  The renaming in Section 17 was re-verified symbolically: every displayed coefficient of h(x+δ) − y
  vanishes through ϑ³.
- **Bibliographies merged.** Source 16's `Chang` and `Thesis` are source 69's `Chang2024` and
  `ChangThesis`. Source 69's `OEIS` entry, uncited in its own text, is now cited.

## Files

```
article.tex                                   the merged report (standalone LaTeX, internal bibliography)
article.pdf                                   the compiled report, 39 pages (contents on pages 1–2)
README.md                                     this guide
16-dcomb-expanded-proof.md                    source 16's expanded derivation notes, as delivered
16-dcomb-mathematical-audit.md                source 16's independent mathematical audit (of its draft)
16-dcomb-integrated-report-audit.md           source 16's audit of its integrated TeX
69-binary-mathematical-verification.md        source 69's verification scope record
69-binary-coef-certificate.md                 source 69's coefficient certificate
69-binary-coef-numerical-and-field-check.md   source 69's forward-numerics and Q[B] field check
69-binary-sources-source-status.md            source 69's literature and version receipts
code/16-dcomb-verify_reduction.py             exact source-array vs shifted-array checks (d = 2..8)
code/16-dcomb-independent_checks.py           independent normalized-recurrence checks (N <= 20, d = 2..12)
code/16-dcomb-derive_coefficients.py          polynomial-Airy recursion for fixed d (COMBINING_D=2 or 3)
code/16-dcomb-numerical_diagnostic.py         uncertified floating diagnostics
code/16-dcomb-replay.sh                       source 16's replay driver (delivered layout)
code/16-dcomb-build_pdf.sh                    source 16's PDF build script (delivered; see below)
code/69-binary-check_exact_cocycle.py         exact gauge and recurrence checks
code/69-binary-verify_total_transfer.py       deficit polynomials and finite counting identities
code/69-binary-check_inverse.py               generic inverse cancellations
code/69-binary-reproduce.py                   source 69's replay driver (delivered layout)
code/69-binary-coef-derive_coefficients.py    polynomial-Airy recursion, d = 2, order 7
code/69-binary-coef-check_natural_field.py    Q[B] coordinate check
code/69-binary-coef-check_forward_numerical.py   uncertified forward diagnostics to n = 50000
code/69-binary-coef-check_frozen_numerical.py    uncertified tridiagonal eigenvalue check
code/69-binary-verif-check_independent.py          independent coefficient solves
code/69-binary-verif-check_independent_order7.py   the same through order 7
code/69-binary-verif-check_total_transfer.py       independent transfer algebra
code/69-binary-verif-check_total_transfer_order6.py   the same through degree 6
code/69-binary-verif-check_inverse_independent.py  independent inverse expansion
code/69-binary-verif-check_distribution.py         distribution normalization and moments
data/16-dcomb-*.json, *.log                   source 16's recorded outputs (14 files) and its requirements
data/69-binary-*.json, *.log                  source 69's recorded outputs (26 files) and its requirements
```

The `data/` directory holds exactly these 42 files:
- **Source 16 (15):** `clean-replay-summary.json`, `coefficients-d2.{json,log}`, `coefficients-d3.{json,log}`,
  `exact-replay.log`, `hash-receipt.json`, `independent-replay.log`, `independent_checks.json`,
  `integrated-hash-receipt.json`, `numerical-diagnostics.{json,log}`, `quality-checks.json`,
  `reduction-checks.json`, `requirements.txt`.
- **Source 69 (27):** `clean-replay-summary.json`, `coef-coefficients.json`, `coef-forward-numerical.json`,
  `coef-frozen-numerical.json`, `coef-natural-field.json`, `exact-cocycle-checks.json`, `inverse-check.json`,
  `logs-02-derive_coefficients.log`, `logs-03-check_natural_field.log`, `logs-06-check_independent.log`,
  `logs-07-check_independent_order7.log`, `logs-08-check_total_transfer.log`,
  `logs-09-check_total_transfer_order6.log`, `logs-12-check_forward_numerical.log`,
  `logs-13-check_frozen_numerical.log`, `quality-checks.json`, `reproduction-results.json`,
  `requirements.txt`, `sources-source-status.json`, `total-transfer-checks.json`,
  `verif-distribution-checks.json`, `verif-independent-checks.json`, `verif-independent-inverse-checks.json`,
  `verif-independent-order7-checks.json`, `verif-total-transfer-checks.json`,
  `verif-total-transfer-order6-checks.json`, `visual-quality.json`.

Every file other than `article.tex`, `article.pdf` and this README is byte-identical to the delivery.
Shipped names are the delivered names with the prefix `16-dcomb-` or `69-binary-`. Delivered
subdirectories are folded into the name: `reproducibility/` is dropped for source 16, and source 69's
`coefficients/`, `verification/`, `logs/` and `sources/` become `coef-`, `verif-`, `logs-` and `sources-`.
Scripts go to `code/`, recorded outputs to `data/`, and audit Markdown to the root.

**Not shipped (all retrievable with `git show 096ee7b87:docs/incoming/<archive>.zip`):**
- both manuscripts' PDFs, source 69's manuscript TeX and README, and its `article/build_pdf.sh`;
- the checksum ledgers, all verified at placement and retired: source 16's `SHA256SUMS` (29/29) and
  `manifest.json` (29/29), and source 69's `SHA256SUMS` (55/55);
- source 16's HTML renderings of its two audits;
- source 69's `coefficients/coefficients-order7.json`, byte-identical to the shipped
  `data/69-binary-coef-coefficients.json`;
- source 69's `logs/01`, `04`, `05`, `10` and `11`, byte-identical to the shipped JSON receipts
  `exact-cocycle-checks.json`, `total-transfer-checks.json`, `inverse-check.json`,
  `verif-independent-inverse-checks.json` and `verif-distribution-checks.json`.

Source 16's delivered README was staged as this file by the placement commit and is replaced here; it
survives as `git show 34f1acd4b:<this directory>/README.md`. Its scope statement is in Section 1.3 of the
article. No file of either archive was excluded as heavy regenerable data.

## Label prefix

Every label in `article.tex` carries the prefix `tcn:`: `tcn:sec:` and `tcn:part:` for the provenance
section and the two Parts, `tcn:d:` for Part I (source 16) and `tcn:b:` for Part II (source 69). Source 16's
39 labels are kept with the prefix `tcn:d:`. The article has **170** labels; the file staged at placement
had 39. No `tcn:` label has a Lean mapping.

## Delivered text that uses delivery names or names unshipped files

- `16-dcomb-mathematical-audit.md`:
  - It reviews an unshipped draft, `maximal-proof.md`, whose verdict names d ≥ 3. The integrated
    audit and the article claim d ≥ 2.
  - It compares against `oeis-a213863-research/release/tree-child-asymptotics.tex`, which is source 69's
    manuscript (same SHA-256, `86217958…`). That manuscript is not shipped; it is printed as Part II.
  - It mentions an audit directory with replay copies that is not shipped.
- `16-dcomb-integrated-report-audit.md` and `data/16-dcomb-integrated-hash-receipt.json` pin
  `/workspace/shared/d-combining-extension/release/d-combining-asymptotics.tex` (SHA-256 `70a1aab9…`). That
  is the delivered manuscript, i.e. the `article.tex` of the placement commit. The merged `article.tex`
  differs from it. `data/16-dcomb-hash-receipt.json` hashes `/workspace/shared/…` paths, including
  `maximal-proof.md` and source 69's manuscript.
- `16-dcomb-expanded-proof.md` calls source 69 "the frozen A213863 release".
- `data/16-dcomb-quality-checks.json` names `reproducibility/integrated-report-audit.md` and describes the
  delivered 10-page PDF.
- `data/69-binary-quality-checks.json` and `data/69-binary-visual-quality.json` describe source 69's
  delivered 23-page PDF, which is not shipped.
- `69-binary-coef-certificate.md` names `coefficients-order7.json` (see above) and gives commands in the
  delivered layout.
- `69-binary-coef-numerical-and-field-check.md` names `forward-numerical.out` and `natural-field.out`,
  which were never delivered. Its "main proof §7" is Section 15.6 here.
- `data/69-binary-reproduction-results.json` and `data/69-binary-clean-replay-summary.json` use delivered
  paths (`logs/…`, `coefficients/…`, `verification/…`), and the latter counts 53 manifest entries.
- `69-binary-sources-source-status.md` names `source-status.json`, shipped as
  `data/69-binary-sources-source-status.json`.
- `code/16-dcomb-build_pdf.sh` builds the unshipped `d-combining-asymptotics.tex`, so it cannot build this
  report. Use the command below.

## Relation to other reports and to formal work

- `../a082161-airy-amplitudes` (relaxed and compacted trees and automata, written in the same batch)
  proves its amplitudes with the same family of lemmas. Its relaxed-binary identity
  (P″+4(x+a)Q′+2Q)F+(2P′+Q″)F′ is this report's polynomial–Airy identity at c = 2, ℓ = 2a. Neither report
  cites the other, and they stay separate (Section 1.5).
- `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/` supplies the inversion
  machinery cited above.
- No other repository report treats tree-child networks, A213863 or d-combining networks.
- **Formal status.** Placement in the repository confers no formal status. No Lean or Rocq declaration
  states any result of this report. The only related declaration is the real-number bracket lemma
  `staircase_separation` in `Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`, which
  formalizes the separation condition of `p0:thm:staircase` behind the integer brackets. It says nothing
  about these counts.

## Building the PDF

From a scratch copy of `article.tex` (pdfLaTeX, MiKTeX or TeX Live):

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The build has 0 errors, 0 undefined references or citations, 0 multiply defined labels, 0 duplicate
destinations, and no overfull or underfull boxes. It yields 39 pages. Copy back only `article.pdf`.

## Rerunning the programs

The scripts use delivery-relative paths and write their outputs next to themselves, overwriting
same-named files. On Windows they write CRLF line endings. Never run them in this directory. Copy them
into the delivered layout in a scratch directory instead. Python 3 with the pins in
`data/16-dcomb-requirements.txt` and `data/69-binary-requirements.txt` (sympy 1.14.0, numpy 2.3.5,
scipy 1.17.0, mpmath 1.3.0); on Windows use `py` for `python`.

```sh
R=<repository>/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a213863-tree-child-networks
W=$(mktemp -d)

# Source 16 (delivered root: the archive root, scripts under reproducibility/)
mkdir -p "$W/16/reproducibility"
for f in verify_reduction independent_checks derive_coefficients numerical_diagnostic; do
  cp "$R/code/16-dcomb-$f.py" "$W/16/reproducibility/$f.py"; done
cp "$R/code/16-dcomb-replay.sh" "$W/16/reproducibility/replay.sh"
(cd "$W/16" && bash reproducibility/replay.sh)    # calls `python`; on Windows run its five lines with `py`

# Source 69 (delivered root tree-child-asymptotics/, with coefficients/ and verification/)
mkdir -p "$W/69/coefficients" "$W/69/verification"
for f in check_exact_cocycle check_inverse verify_total_transfer reproduce; do
  cp "$R/code/69-binary-$f.py" "$W/69/$f.py"; done
for f in derive_coefficients check_natural_field check_forward_numerical check_frozen_numerical; do
  cp "$R/code/69-binary-coef-$f.py" "$W/69/coefficients/$f.py"; done
for f in check_independent check_independent_order7 check_total_transfer check_total_transfer_order6 \
         check_inverse_independent check_distribution; do
  cp "$R/code/69-binary-verif-$f.py" "$W/69/verification/$f.py"; done
cp "$R/data/69-binary-coef-coefficients.json" "$W/69/coefficients/coefficients-order7.json"  # read by check_natural_field.py
(cd "$W/69" && python reproduce.py)               # add --numerical for the uncertified diagnostics
```

Compare the outputs with the shipped `data/` files using `diff --strip-trailing-cr` or by parsed JSON.
Source 16's driver writes `*.log` and `*.json` into `reproducibility/`. Source 69's driver writes `logs/`,
`reproduction-results.json` and the JSON receipts in place.

The batch-77 intake ran every piece on such copies, on a heavily loaded laptop:
- Source 16: `verify_reduction` 2 s, `independent_checks` 2 s, `derive_coefficients` 162 s at d = 2 and
  23 s at d = 3, `numerical_diagnostic` 57 s.
- Source 69: all 13 commands, 4–122 s each.

All passed. The exact outputs equal the shipped ones apart from CRLF, and the numerical outputs differ
only in the last floating digits. The intake also found that every entry of source 16's d = 2 coefficient
file agrees with source 69's order-7 file, which runs one order further. On Windows,
`check_forward_numerical.py --extended-check` compares double with double; see Section 19.
