# The Logarithmic Deficit of Two Inversion Sequence Classes

**Commitment trees for OEIS A279551 and A279556: the stretched exponential order, non-D-finiteness, the sharp constant and the next logarithmic correction**

This is a research report built on 5 October 2026 (write batch 104) from
three manuscripts of one external research session, Reports 126, 127 and 129
of the session bundle of Reports 1–243, all dated 2 October 2026. They form
one chain on one spine: Britt and Beaton's inversion-sequence classes 247
and 759 (inversion sequences `e`, `0 ≤ e_i < i`, avoiding the patterns
`(000,010,110,120)` and `(010,110,120)`), counted by OEIS
[A279551](https://oeis.org/A279551) (`1, 1, 2, 4, 10, 27, 79, 247, 816, …`) and
[A279556](https://oeis.org/A279556) (`1, 1, 2, 5, 15, 51, 190, 759, 3206, …`),
with growth constants `μ = 8` and `μ = 9`. The subject is the deficit
`𝒟(n) = n log μ − log a(n)`. Throughout `S = ψ(n) = n^{1/3}(log n)^{2/3}`,
`N = log n`, `J = log log n`, `σ_D = (3π²/(2D))^{1/3}` with `D = 1/2` for
A279551 and `D = 1` for A279556 (`σ_D = 3.093667726280136…` and
`2.455445701568578…`).

- **Part I** (Report 126): `cψ(n) ≤ 𝒟(n) ≤ Cψ(n)`, `a(n) ≤ μⁿ` for all `n`,
  strict monotonicity for `n ≥ 1`, the inverse threshold
  `N(T) = log T/log μ + Θ((log T)^{1/3}(log log T)^{2/3})`, smooth boundary values
  with sharp Gevrey order 3, a genuine singularity at `1/μ`, and
  **non-D-finiteness** (hence non-algebraicity) of both generating functions.
- **Part II** (Report 127): the sharp constant, `𝒟(n) = σ_D S + o(S)`, with the
  inverse coefficient `σ/log μ` and the linear term `[log(2D/π²) − 3]k` of
  the boundary-derivative growth.
- **Part III** (Report 129, the base): `𝒟(n) = σ_D S + (7σ_D/3) SJ/N + O(S/N)`,
  with refined inverse and derivative consequences.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| *Commitment trees and the logarithmic stretched exponential scale* (title block "Report 126 … Standalone proof and exact finite verification companion"; no author line) | 126 | `A279551_A279556_Logarithmic_Deficit_and_Inverse_Source.zip` (430,748 bytes, 19 files; `report126.tex`, 1,025 lines, 17 pp.) | none | `612787fb4` | Part I, Sections 1–12, plus the write's Remark 1.2 and Section 11.1 |
| *Sharp logarithmic deficit constants for two inversion sequence classes* (title block "Report 127 … Standalone proof and reproducible source companion"; no author line) | 127 | `A279551_A279556_Sharp_Deficit_Constants_and_Inversion_Source.zip` (485,669 bytes, 19 files; `report127.tex`, 1,612 lines, 24 pp.) | none | `612787fb4` | Part II, Sections 13–28 (14–16 title only), plus the write's Section 27.1 |
| *The next logarithmic correction for two inversion sequence classes* (title block "Report 129 … Full quantitative upgrade with a proved input companion"; no author line); the base | 129 | `A279551_A279556_Loglog_Correction_and_Refined_Inversion_Source.zip` (921,260 bytes, 38 files, 19 of them Report 127's package under `earlier-inputs/report127/`; `report129.tex`, 1,148 lines, 17 pp.) | none (carries Report 127 byte for byte) | `612787fb4` | Part III, Sections 29–38, plus the write's Remark 29.2 and Section 39 |

All three archives arrived unchanged in `60f54ea06` ("Arrival: 177 research
archives from the session bundle of Reports 1-243") and survive there
(`git show 60f54ea06:docs/incoming/<archive> > <archive>`); the placement
commit `612787fb4` (batch 104, cluster 104-INV, subfamily A279551/A279556)
removed them from `docs/incoming/`. The write is batch 104's "Write batch 104
(a279551-inversion-log-deficit): new report, the logarithmic deficit of
A279551 and A279556".

**Status.** Unrefereed; not formalized; no statement has been checked by a
proof assistant. None of the manuscripts names an author, a tool or an
addressee, says it is AI-assisted, or carries "prepared for private review"
wording; each sets an empty PDF author field. Every result, proof, remark,
question and limitation of the three manuscripts is printed; Report 127's
Sections 2–4, which are Report 126's Sections 2–4 character for character, are
printed once, in Part I.

## Why the Parts are in this order

The base is Report 129, the strongest manuscript, and its `report129.tex` was
staged as `article.tex`. It is printed **last**, as Part III, because it is not
self-contained: its Proposition 2.1 (here 30.1) and several later steps cite
proofs that exist only in Report 127 (exact counting, transforms, uniform
entrance and every-integer-time repair, the spatial barrier), which its own
package carries unchanged. Report 127 is therefore printed in full, as Part II.
Report 126 comes first because Report 127 repeats its Sections 2–4, and
because it alone proves non-D-finiteness, the genuine singularity at `1/μ` and
strict monotonicity, by an order-of-magnitude proof (logarithmic staircase,
concave barrier, time tilt) that differs from the variational proofs of Parts
II and III. The order is the order of logical dependence and of writing.

## Files

The directory holds 40 files: 6 at the root, 20 in `code/`, 14 in `data/`.

**Report files**, written in the write: this guide, the merged article and its PDF.

```
README.md
article.pdf
article.tex
```

**Report 126, prefix `126-scale-`** (13 files): the guide to its exact
finite companion; `code/`: the checker and its negative (mutation) suite, the
package integrity checker (also standing for the byte-identical copies in
Reports 127 and 129) and its test, the PDF build script, the repacking and
full-replay scripts; `data/`: the companion's frozen evidence and provenance
records, the recorded checker and negative-suite outputs, and the build
environment (also Report 127's, byte for byte).

```
126-scale-checks-README.md
code/126-scale-build.py
code/126-scale-checks-negative_tests.py
code/126-scale-checks-verify.py
code/126-scale-integrity.py
code/126-scale-repack.py
code/126-scale-reproduce.py
code/126-scale-test_integrity.py
data/126-scale-build-environment.txt
data/126-scale-checks-evidence.json
data/126-scale-checks-provenance.json
data/126-scale-negative_results.json
data/126-scale-verification_results.json
```

**Report 127, prefix `127-sharp-`** (11 files), the same roles:

```
127-sharp-checks-README.md
code/127-sharp-build.py
code/127-sharp-checks-negative_tests.py
code/127-sharp-checks-verify.py
code/127-sharp-repack.py
code/127-sharp-reproduce.py
code/127-sharp-test_integrity.py
data/127-sharp-checks-evidence.json
data/127-sharp-checks-provenance.json
data/127-sharp-negative_results.json
data/127-sharp-verification_results.json
```

**Report 129, prefix `129-loglog-`** (13 files), the same roles, plus its
`build.sh` (which differs from the others):

```
129-loglog-checks-README.md
code/129-loglog-build.py
code/129-loglog-build.sh
code/129-loglog-checks-negative_tests.py
code/129-loglog-checks-verify.py
code/129-loglog-repack.py
code/129-loglog-reproduce.py
code/129-loglog-test_integrity.py
data/129-loglog-build-environment.txt
data/129-loglog-checks-evidence.json
data/129-loglog-checks-provenance.json
data/129-loglog-negative_results.json
data/129-loglog-verification_results.json
```

**Not shipped** (all retrievable from `60f54ea06`): the three PDFs;
`report126.tex` and `report127.tex` (printed as Parts I and II) and the
delivery READMEs of Reports 126 and 127 (Report 129's was staged and is
replaced by this guide); the six checksum manifests (`CHECKSUMS.sha256` and
`checks/manifest.sha256` of each report; verified at placement, 18/18 and 5/5
for Reports 126 and 127, 37/37 and 5/5 for Report 129, 18/18 and 5/5 for its
nested Report 127; repository policy drops checksum manifests); Report 129's
`earlier-inputs/report127/` (19 byte copies of Report 127's delivery, SHA-256
checked); the duplicate `integrity.py` of Reports 127 and 129 and
`build-environment.txt` of Report 127 (byte copies of Report 126's, which are
shipped); and the `build.sh` of Reports 126 and 127, a generic four-line
wrapper (`exec python3 -B build.py`) that is byte for byte
`../a307316-leafless-multigraphs/code/build.sh`. No OEIS data file is
shipped: the companions' counts are internal recomputations.

## Labels and numbering

Label prefix **`ivd:`** (none at HEAD before this report): Part I uses
`ivd:sc:` (Report 126's 47 labels), Part II `ivd:sh:` (92 of Report 127's 104
labels), Part III `ivd:ll:` (Report 129's 77 labels). Report 127's other 12
labels sit in its Sections 2–4, which are Report 126's word for word; they
resolve to Part I's labels (`eq:Q` of Report 127 is `ivd:sc:eq:Q`). The front
matter uses `ivd:sec:guide`, `ivd:sec:status`, `ivd:sec:notation`,
`ivd:sec:provenance`, `ivd:sec:neighbours`. The write added the three Part
labels, 42 section and subsection labels (15 in Part I, 17 in Part II
including the three title-only Sections 14–16, 10 in Part III), the
further-questions labels `ivd:sc:sub:further`, `ivd:sh:sub:further`,
`ivd:ll:sec:further`, the remarks `ivd:sc:rem:bb` (with its display
`ivd:sc:eq:bbforms`) and `ivd:ll:rem:a202061`. 272 labels in all, all
distinct. The manuscripts share many bare label names (21 between Reports
126 and 127, 12 between 127 and 129, 5 between 126 and 129; `thm:main`,
`eq:main`, `cor:inverse` and `eq:inverse` occur in all three); they are
distinct under the Part prefixes, and outside Report 127's repeated Sections
2–4 they name different statements.

Sections are numbered continuously and statements within sections, so a
manuscript's statement numbers shift with its sections only:

| Part | Manuscript | Section here | Statement `k.j` |
|---|---|---|---|
| I | Report 126 | `k` (unchanged, 1–12); 11.1 added | `k.j` (unchanged); Remark 1.2 added |
| II | Report 127 | `k + 12` (13–28); 14–16 title only; 27.1 added | `(k+12).j` |
| III | Report 129 | `k + 28` (29–38); 39 added | `(k+28).j`; Remark 29.2 added |

For example Report 127's Theorem 1.1 is Theorem 13.1, its Corollaries 14.1 and
14.2 are 26.1 and 26.2; Report 129's Theorem 1.1 is Theorem 29.1, its
Proposition 2.1 is 30.1, its Corollaries 8.1 and 9.1 are 36.1 and 37.1.
The two remarks added by the write are the last statements of their sections,
so no delivered statement number moved; a comparison of the build's `.aux`
with separate builds of the three delivered `.tex` files confirmed all 26
non-equation labels under these offsets. **Equation numbers are not kept**:
the manuscripts number equations consecutively through each document, the
merged article within sections (Report 129's `(1)` is `(29.1)`); every
equation keeps its label name. The delivered READMEs, data and code use the
manuscripts' own numbers.

## Notation

No delivered symbol was renamed. The front matter's "Notation across the three
Parts" lists every letter whose meaning changes, with the tempting false
readings, and each Part opens with a short reading-conventions table. In the
write's own text the deficit is `𝒟_j(n)`, because **`D`** is taken: in Part I
`D_j(n)` is the deficit (and `D = w − ℓ` a displacement), in Parts II and III
`D ∈ {1, 1/2}` is a diffusion coefficient (Report 127 itself warns that it is
"not a deficit"). Other collisions: Part III's **`e = N^{-6}`** (a strip height,
beside Euler's `e`), its **`N = log n`** (beside thresholds `N(T)`), **`κ`**
(Part III's root `κ_p` against the barrier constant), **`M`**, **`a`**, **`b`**
(Part III's `b_n = 1 − δ` in Section 34 but `b_n = a(n)μ^{-n}` in Section 37),
**`R`**, **`G`**, **`P`**, **`ρ`**, **`λ`** (tilt, or `log μ` in the
corollaries), **`k`**, **`L`**, **`H`** (Part I's is rounded).

## What the report claims

**Part I (Report 126).**
- Theorem 1.1: `μⁿ e^{−Cψ(n)} ≤ a(n) ≤ μⁿ e^{−cψ(n)}` for large `n`,
  `a(n) ≤ μⁿ` for all `n`, growth constants 8 and 9. Lower bound: completed
  commitment cycles along the staircase `p_k = ⌊k² log(k+1)⌋`, exact
  integer filling (Lemma 5.1) and a fixed endpoint; upper bound: joint
  space–time renewal transforms, the concave barrier
  `exp(κ√((p+2)log(p+2)))` and a time tilt.
- Section 5.4: the ladder `p_k = k²` gives `a(n) ≥ μⁿ exp(−Cn^{1/3} log n)`,
  already excluding a negative `n^{3/8}` term.
- Section 9: `𝒟(n)/n^β → 0` for `β > 1/3`, `𝒟(n)/n^{1/3} → ∞`; strict
  monotonicity `a(n+1) > a(n)` for `n ≥ 1`; Corollary 9.1, the inverse
  `⌈s + dψ(s)⌉ ≤ N(T) ≤ ⌈s + d⁺ψ(s)⌉`.
- Theorem 10.1: smooth boundary values,
  `log‖f^{(k)}‖ = 3k log k − 2k log log(k+2) + O(k)` (and radially), sharp
  Gevrey order 3, `1/μ` a genuine singularity, generating functions not
  D-finite over `ℂ(z)` (André–Chudnovsky–Katz in Fischler–Rivoal's form, with
  a `ℚ`-to-`ℂ` descent), hence not algebraic.

**Part II (Report 127).**
- Theorem 13.1: `log a(n) = n log μ − σ_D S + o(S)`.
- Theorem 18.1 (uniform sharp local root, `c_* = ½ log(π/α)`), Theorem 19.1
  (the singular variational minimum, `f_* = M sin²ϑ`, action `1/M = σ_D`, exact
  quadratic remainder), Lemmas 20.1–20.2 (moments; drift by concavity), Theorem
  21.1 (strip path with its random clock and exact likelihood), Lemma 22.1
  (entrance in time `O(p^{3/2}/√log p)` and repair at every large exact
  length), Lemmas 24.1–24.2 (subcritical rows; spatial tail), Section 25
  (space–time supersolution, smooth duals).
- Corollary 26.1: `N(T) = s + (σ/λ)ψ(s) + o(ψ(s))`; Corollary 26.2:
  `log M_k = 3k log k − 2k log log k + [log(2D/π²) − 3]k + o(k)`, radially plus
  `k log μ`.

**Part III (Report 129).**
- Theorem 29.1: `n log μ − log a(n) = σ_D S + (7σ_D/3) SJ/N + O(S/N)`, with
  explicit envelopes `e^{−G(n) ∓ CR(n)}`; constants not effective.
- Lemma 31.1 (quantitative and anchored local root), Lemma 32.1 (the profile
  for `A` near 1/3, minimum `σ_D(3A)^{2/3}`, integrable `(1+|log f|)/f`),
  Sections 33–34 (upper bound by a dual with an integrated logarithmic
  penalty; lower bound by a shrinking strip, quantitative martingales, exact
  likelihood and repair), Section 35 (error ledger).
- Corollary 36.1: the inverse with the term `(7σ/(3λ))ψ(s) log log s/log s`
  and error `O(ψ(s)/log s)`; Corollary 37.1: the derivative growth with the
  term `−k log log k/log k` and error `O(k/log k)`.

**Added by the write** (all marked `[write]`, dated 5 October 2026):
Remark 1.2 — Britt and Beaton's forms (their (4.12)–(4.13), with their fitted
values) on record, and a proof that no form `C nᵍ μⁿ exp(−b n^β)` with real
`g, b, β` is an asymptotic equivalent of either sequence (extended after the
independent check, below, to `exp(−b n^β (log n)^γ)`); Remark 29.2 — the
parallel with `a202061-ascent-120-deficit`; the three further-questions
sections; dated supersession and cross-reference notes; the front matter.
Section 39 also records the residual
`[𝒟(n) − σ_D S(1 + 7J/(3N))]/(σ_D S/N)` = −2.74, −2.95, −3.02, −3.04
(A279551) and −2.37, −2.63, −2.75, −2.81 (A279556) at `n = 40, 100, 200, 400`,
from a floating-point run of the commitment-tree recursion (placement dossier,
rerun at the write; at `n = 40` it agrees with an exact big-integer run). This
is a hint for question 1, **not a fit**. (The value at `n = 400` was first
printed −3.05, and A279551's `𝒟/(σ_D S)` at `n = 40` was first printed 1.083
in the article's table, both rounded twice from four decimals; corrected after
the independent check to −3.04 and 1.082.)

**Independent check of the write (5 October 2026).** An adversarial check
made by the intake after the write (`80adcb910`) reread the items of the write
that carry mathematics, citations or numbers — Remark 1.2, its proof and its
quotation of Britt–Beaton; Remark 29.2 and each statement it makes about
`a202061-ascent-120-deficit`; "Report 127's Sections 2–4 are Report 126's
character for character"; the numerical hint under question 1 and the numbers
of question 5 of Section 39; and the exact counts behind them — and found every
mathematical claim valid, with no counterexample and no gap in Remark 1.2's
proof (its case analysis covers every `(b, β)`, including `β = 1/3`). Changes,
each dated:

- Two entries of Section 39's table were rounded twice: A279551's
  `𝒟/(σ_D S)` at `n = 40` is 1.082 (true 1.08245…), not 1.083, and its residual
  at `n = 400` is −3.04 (true −3.04499…), not −3.05. Corrected in the article
  (a dated note keeps the first values) and above; the qualitative reading is
  unchanged.
- Remark 1.2: "only the upper half of the deficit bound is needed for
  `β = 3/8`" is restricted to Britt–Beaton's case `b > 0` (for `b ≤ 0` the
  lower half is used); and a paragraph added with the check's proof shows that
  a factor `(log n)^γ` in the stretched term does not repair the form either
  (Theorem 13.1 forces `(β, γ, b) = (1/3, 2/3, σ_D)`, and Theorem 29.1's second
  term is not `O(log n)`).
- Remark 29.2: the A202061 report's local root is its Part III's row threshold
  `(½ log r + log log r − C₀/2)/r`, measured in its exponent `Ψ`, which carries a
  factor `1/α`.

The tests, none of which used the delivered or the write's programs: a
prefix-pruned brute force from the literal triple conditions for `n ≤ 11`; an
independent left-to-right transfer program (not the commitment tree), exact for
`n ≤ 26`; the commitment-tree recursion coded from Part I's Section 2, exact for
`n ≤ 400` and modulo `2⁶¹ − 1` for `n ≤ 1000` — all equal to each other and to
the OEIS b-files of A279551 and A279556 (terms 0–1000, fetched 5 October
2026); the table and question 5's numbers recomputed at 50 digits from the
exact counts (`J/N = 0.2988`, `(7/3)J/N = 0.6972` at `n = 400`); Britt–Beaton's
Section 4.2, (4.12)–(4.13) and their fitted values read in the HTML text of
arXiv:2512.21943v3; Reports 126 and 127 split at their section headings, with
Sections 2, 3, 4 of equal length (4586, 2708, 2055 characters) and equal
SHA-256 digests; and every label, scale, constant (`C_⋆ = 2.2326253…`,
`κ = −1.9401481831…`) and non-citation that Remark 29.2 attributes to the
A202061 report confirmed in its `article.tex`. The record is an unlabelled
dated paragraph at the end of Section 39. This was a careful reading with
numerical tests, not a formal verification.

## What the report does not claim

Every limitation is printed in place. In short: **no coefficient equivalent**,
multiplier, polynomial factor or amplitude in any Part — exponentiating `o(S)`
or `O(S/N)` gives no `1 + o(1)`; the **coefficient of `S/log n` is not
identified** (the constant `c_*` of the local root does not isolate it); no
ratio theorem for `a(n+1)/a(n)` (the remainders are never differenced); no
all-orders expansion or transseries, no effective constants or onsets, no
numerical crossover, no new fit and no digits from data; no unique dominant
singularity, exterior Δ-domain expansion or continuation through other points
of `|z| = 1/μ`; Part I gives no leading constant (its `Θ` is shorthand for two
inequalities, and its inverse constants are existential); Report 127's
"the local `log log p` term is not a global next-order term" stays true as a
statement about that lemma (Part III supplies the accumulation). Britt and
Beaton's forms are refuted only as literal equivalents; their exact trees and
finite enumerations, on which every Part rests, are not disputed, and they
themselves call those forms non-rigorous. No global priority claim. **All
three companions**: finite exact checks prove no asymptotic, martingale, tail,
variational or Gevrey statement; integrity inventories are records relative to
the supplied verifiers, not signatures.

## Further questions, and the standing rule

Parts I and II close with "Further questions and research" (Sections 11.1 and
27.1), which say which of their questions a later Part answers; Section 39
collects the open problems of all three, with sources, sketches and what is
missing (Vladimir's standing rule of 4 October 2026):

1. the coefficient of `S/log n` (Report 129, Section 35) — model: the A202061
   report's Parts IV–V; the residuals above are only a hint;
2. a coefficient equivalent (126 item 2; 127 item 1; 129);
3. ratio asymptotics and their rate (126 item 3; 127 item 3);
4. all orders, transseries, effective constants and onsets (126 items 3–4;
   127 item 4; 129 Theorem 1.1);
5. a numerical crossover and an effective fitting window (126 item 5; 127
   item 4); the two proved terms are still large at `n = 400`
   (`(7/3)J/N ≈ 0.70`);
6. a unique dominant singularity and continuation on the circle (126 Theorem
   10.1; 127 item 5).

Answered inside the merge, with dated notes at the questions: Report 126's
leading constant (by Theorem 13.1); Report 127's global next term (by Theorem
29.1); Report 126's "no quantitative remainder" (by Theorem 29.1's ineffective
`O(S/log n)`). **Nothing in the three manuscripts was found to be wrong.**
The one wrong claim on record is external: Britt–Beaton's numerical
`n^{3/8}` forms, refuted with a proof in Remark 1.2.

## Relation to neighbouring reports

All in `SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/`:

- `a202061-ascent-120-deficit` (120-avoiding ascent sequences, A202061):
  **same method, other sequence.** Same scale `n^{1/3}(log n)^{2/3}`, a
  critical local root of the form `(½ log p + log log p + c)/p`, the potential
  `1/3 + (7/6) log log n/log n` (in its normalization `α/3 + (7α/6)…`), the
  second term with coefficient `7/3` (its `a61:o2:thm:main`), and the exclusion
  of a numerically estimated `n^{3/8}` (Conway, Conway, Elvey Price and
  Guttmann there; Britt and Beaton, with Guttmann's assistance, here). Its
  Parts IV–V go further (the next constant `κ = −1.94…`, every fixed
  inverse-logarithmic order). Its `C_⋆ = (3π²α²/(2v))^{1/3}` uses its own
  normalization; `σ_D = (3π²α/(2v))^{1/3}` here; no relation between the
  constants is asserted. Neither report cites the other. Remark 29.2 gives the
  details; a reciprocal note there is a separate commit. *[Dated note,
  7 October 2026: applied in `32919c4cf`. a202061's article (a dated note
  after `a61:o2:thm:main`) and its README ("Same method, other sequences")
  now point here, so "neither report cites the other" holds of the source
  manuscripts only.]*
- `a279544-inversion-kernel-classes` and `a279571-inversion-cone-walk`
  (placed in the same batch): other Britt–Beaton classes, with algebraic
  kernels or a quadrant cone walk; unrelated methods and regimes, no
  cross-citation. Siblings, not hosts.
- No other report treats A279551 or A279556 (searched 5 October 2026).

## Relation to the formal project

Placement in the collection confers no formal status, and no statement of this
report is formalized: no Lean or Rocq file in the repository mentions
inversion sequences, commitment trees, A279551 or A279556 (searched
5 October 2026).

## Delivery names, renames and discrepancies

- Every delivered file keeps its bytes (all 39 staged files were checked
  against the pristine extraction again at the write: 0 differences;
  `article.tex` and this README then replaced the two staged base files). Only names changed (tables at the
  end). The delivered code and markdown use delivery paths (`checks/…`,
  `data/…`, `report12N.tex`, `report12N.pdf`, `README.md`, `CHECKSUMS.sha256`,
  `build-environment.txt`), which are shipped under other names or not at all.
- **Closed inventories: none of the checkers runs in this directory.** Every
  `checks/verify.py` reads `checks/manifest.sha256` and refuses extra or
  missing members; `integrity.py`, `test_integrity.py`, `reproduce.py` and
  `repack.py` read `CHECKSUMS.sha256` and the delivery layout. Rerun from the
  archive (below).
- Report 129's delivered README (replaced by this guide) named
  `report129.pdf`, `earlier-inputs/report127/…` and output paths under
  `/tmp/`; `129-loglog-checks-README.md` uses `/tmp/…`, and the Report 126 and
  127 companion READMEs use `/path/to/checks/…` and `/tmp/…`. Use a scratch
  directory outside the repository. Part III's text likewise describes "the
  unchanged Report 127 package"; in this report that is Part II and the
  `127-sharp-` files.
- `data/126-scale-checks-provenance.json` and `data/127-sharp-checks-provenance.json`
  pin internal audit and proof documents of the delivering session by SHA-256
  (three and four of them); those documents were never delivered, and the
  companions say that the hashes are identifiers, not certificates.
  `data/129-loglog-checks-provenance.json` names Report 127 as its prior
  report, which is Part II here.

## Rerunning the checks

Run on a copy in a scratch directory, never in this directory. Recreate the
delivered layout from the arrival commit:

```
git show 60f54ea06:docs/incoming/A279551_A279556_Logarithmic_Deficit_and_Inverse_Source.zip > s126.zip
git show 60f54ea06:docs/incoming/A279551_A279556_Sharp_Deficit_Constants_and_Inversion_Source.zip > s127.zip
git show 60f54ea06:docs/incoming/A279551_A279556_Loglog_Correction_and_Refined_Inversion_Source.zip > s129.zip
mkdir r126 r127 r129 && unzip -q s126.zip -d r126 && unzip -q s127.zip -d r127 && unzip -q s129.zip -d r129
cd r129/report129
python3 -B integrity.py
python3 -B checks/verify.py --output ../../v129.json        # also with -O; compare with data/verification_results.json
python3 -B checks/negative_tests.py --output ../../n129.json
python3 -B reproduce.py --output ../../replay129.json       # full replay; needs TeX Live and POSIX
```

and the same `checks/verify.py` and `checks/negative_tests.py` commands in
`r126/report126` and `r127/report127`. Python 3.9 or later and its standard
library suffice; `reproduce.py` and `build.py` also need the recorded TeX
(TeX Live 2025, Debian) for byte-identical PDFs.

**Windows.** The suites are written for POSIX, and three platform effects make
the negative suites fail on Windows for reasons that are not mathematical:
text written in Windows text mode gets CRLF line ends (so Report 126's and
127's outputs differ from the recorded ones only by CRLF, and Report 129's
negative suite compares a child diagnostic ending in `\r\n` with an LF
string); Report 127's `seal()` sorts `Path` objects, which Windows compares
case-insensitively (`README.md` after `evidence.json`), so its resealed
manifest fails "MANIFEST: sorted members"; and Reports 127 and 129 test a
"fifo member" with `os.mkfifo`, which Windows lacks. At placement the suites
were run under a `sitecustomize.py` shim outside the packages (LF newlines,
case-sensitive path ordering, a marker-file stand-in for `mkfifo`); the shim
is not shipped. Use a POSIX system, or such a shim.

Results: at placement (5 October 2026, Python 3.14.4, Windows with the shim,
on copies, recorded in the batch-104 dossier) every suite passed — `verify.py`
of Reports 126, 127 and 129 in normal and `-O` mode (3.5 s, 23 s and 5 s;
outputs byte-identical to the recorded ones, after CRLF normalization for
Reports 126 and 127); the negative suites (Report 126: 70 mutations in both
modes and 4 clean replays; Report 127: 59 mutations and 4 clean replays;
Report 129: 54 mutations, 108 rejections; 2–3.5 minutes each, outputs
byte-identical); Report 129's `integrity.py` (37 files). At the write
(5 October 2026, fresh extraction of Report 129's archive, Windows without the
shim) `integrity.py` passed (37 files) and `checks/verify.py` ran in about 7 s
with output byte-identical to `data/129-loglog-verification_results.json`.
`reproduce.py` was not run (it needs the recorded TeX and POSIX); the three
delivered `.tex` files compile with MiKTeX pdfLaTeX to 17, 24 and 17 pages
with no warnings.

## Rights

Repository contents are MIT-0. No OEIS data file is shipped; the counts in the
companions and in the article are recomputed from Britt and Beaton's
commitment trees (and by brute force for `n ≤ 8`), and the companions say that
they claim no fresh OEIS retrieval. OEIS data are available under CC BY-SA 4.0
([OEIS license](https://oeis.org/LICENSE)). The OEIS entries are credited for
the sequences; Britt and Beaton (arXiv:2512.21943v3) for the classes, the
commitment trees, the word counts and the numerical estimates that Remark 1.2
refutes; André, Chudnovsky and Katz, in Fischler and Rivoal's statement, for
the G-function theorem used in Part I. Nothing was submitted to the OEIS.

## Build

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX), in a scratch copy; commit only `article.pdf`. The write's
build: 69 pages, no errors, no undefined or multiply defined references or
citations, no duplicate destinations, no overfull boxes. The log carries three
underfull-box messages, all in Part III's error-ledger longtable (a build of
the staged base `report129.tex` has the same three), and one "Infinite glue
shrinkage found in box being split" message from the notation longtable
breaking across a page.

Rebuilt on 5 October 2026 after the independent check, in a scratch copy with
four pdfLaTeX passes: 70 pages (69 before; the record and the added paragraph
of Remark 1.2 add a page), no errors, no undefined or multiply defined
references or citations, no duplicate destinations, no overfull boxes, and the
same three underfull-box messages and the same infinite-glue message; all 272
labels keep their numbers (`.aux` compared with a build of the committed text;
page numbers after Remark 1.2 move by at most one).

## Delivered path → shipped path

Report 126 (`126-scale-`):

| Delivered | Shipped |
|---|---|
| `report126.tex` | not shipped; printed as Part I of `article.tex` |
| `checks/README.md` | `126-scale-checks-README.md` |
| `build.py`, `integrity.py`, `repack.py`, `reproduce.py`, `test_integrity.py` | `code/126-scale-<name>` |
| `checks/verify.py`, `checks/negative_tests.py` | `code/126-scale-checks-<name>` |
| `checks/evidence.json`, `checks/provenance.json` | `data/126-scale-checks-<name>` |
| `data/verification_results.json`, `data/negative_results.json` | `data/126-scale-<name>` |
| `build-environment.txt` | `data/126-scale-build-environment.txt` |
| `README.md`, `report126.pdf`, `CHECKSUMS.sha256`, `checks/manifest.sha256`, `build.sh` | not shipped |

Report 127 (`127-sharp-`):

| Delivered | Shipped |
|---|---|
| `report127.tex` | not shipped; printed as Part II (Sections 2–4 in Part I) |
| `checks/README.md` | `127-sharp-checks-README.md` |
| `build.py`, `repack.py`, `reproduce.py`, `test_integrity.py` | `code/127-sharp-<name>` |
| `checks/verify.py`, `checks/negative_tests.py` | `code/127-sharp-checks-<name>` |
| `checks/evidence.json`, `checks/provenance.json` | `data/127-sharp-checks-<name>` |
| `data/verification_results.json`, `data/negative_results.json` | `data/127-sharp-<name>` |
| `integrity.py`, `build-environment.txt` | byte copies of Report 126's; not shipped again |
| `README.md`, `report127.pdf`, `CHECKSUMS.sha256`, `checks/manifest.sha256`, `build.sh` | not shipped |

Report 129 (`129-loglog-`):

| Delivered | Shipped |
|---|---|
| `report129.tex` | `article.tex` (Part III) |
| `README.md` | replaced by this guide |
| `checks/README.md` | `129-loglog-checks-README.md` |
| `build.py`, `build.sh`, `repack.py`, `reproduce.py`, `test_integrity.py` | `code/129-loglog-<name>` |
| `checks/verify.py`, `checks/negative_tests.py` | `code/129-loglog-checks-<name>` |
| `checks/evidence.json`, `checks/provenance.json` | `data/129-loglog-checks-<name>` |
| `data/verification_results.json`, `data/negative_results.json` | `data/129-loglog-<name>` |
| `build-environment.txt` | `data/129-loglog-build-environment.txt` |
| `integrity.py` | byte copy of Report 126's; not shipped again |
| `earlier-inputs/report127/` (19 files) | byte copies of Report 127's delivery; not shipped |
| `report129.pdf`, `CHECKSUMS.sha256`, `checks/manifest.sha256` | not shipped |

## Provenance

Three manuscripts (bundle Reports 126, 127, 129) → one report; base 129,
printed as Part III. Arrival `60f54ea06`, placement `612787fb4`, write batch
104 (5 October 2026). No manuscript pins a ProveIt commit. Merge choices
(dependency order with the base last, Report 127's Sections 2–4 printed once,
Part I kept in full as a second route and for its unique theorems, the merged
bibliography with Report 129's entry for Report 127 pointing to Part II) are
listed in the article's front matter, "Provenance and merge decisions".
