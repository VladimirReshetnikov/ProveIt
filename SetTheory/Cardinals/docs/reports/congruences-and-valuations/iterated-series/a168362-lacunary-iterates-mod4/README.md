# Binary Carry Structure in Iterated Lacunary Series

**A complete modulo-four theorem for OEIS A168362, an exact exception criterion, and a logarithmic counting law; and digit-sum divisibility for every prime power and every integer iterate**

This research report has two Parts.

- **Part I** (Sections 1–14, Appendices A–B) is dated 1 October 2026. It
  was built from manuscript 49 of batch 73 (cluster O1) of ProveIt's
  incoming-reports intake; its author line is "Research note prepared for
  Vladimir Reshetnikov with OpenAI".
- **Part II** (Sections 15–27, Appendices C–D) was added in the write of
  batch 114 (6 October 2026). It is built from the manuscript *Digit-Sum
  Divisibility in Lacunary Iteration: All prime powers, explicit first
  residues, finite automata, and p-adic iteration* (5 October 2026), whose
  title page reads "Prepared for Vladimir Reshetnikov" and "OpenAI
  ChatGPT".

| Source | Intake | Archive | Pin | Arrived | Placed | Printed as |
|---|---|---|---|---|---|---|
| Part I | batch 73O1, manuscript 49 | `ProveIt_A168362_Mod4_Theorem.zip` (inner directory `A168362_Mod4_Theorem/`; *Binary Carry Structure in Iterated Lacunary Series*, main file `article.tex`, 15-page PDF as delivered) | none | `3a9518c52` | `9df4ba51a` | Part I: Sections 1–14 and Appendices A–B |
| Part II | batch 114 (not part of a session bundle) | `Digit_Sum_Divisibility_in_Lacunary_Iteration.zip` (inner directory `lacunary_digit_divisibility/`; main file `article.tex`, 23-page PDF as delivered) | `3412ae0741b95b3fb6d7a43477b7fac7723c36d8` | `e4d5dcf9e` | `99053b5d1` | Part II: Sections 15–27 and Appendices C–D |

Part I's manuscript names no pinned commit; it says the repository was
"inspected October 1, 2026". No other manuscript of batch 73 treats
A168362. Its delivered README, PDF, `MANIFEST.txt` (a file list without
hashes) and `SHA256SUMS.txt` ledger (9/9 verified at placement) are not
shipped and survive in `3a9518c52`.

Part II's source audit pins this report's `article.tex` at blob
`46147fca8f8fb912f7132d504b21217c0c248844`, which is Part I exactly as it
stood until the batch-114 write: the manuscript read Part I as printed here,
without the notes dated 6 October 2026. Its delivered `article.tex`,
`article.pdf`, `README.txt` and `SHA256SUMS.txt` (15/15 verified at
placement) are not shipped and survive in `e4d5dcf9e`.

**Status: AI-assisted, unrefereed, not formalized.** The intake reran the
delivered programs of both Parts on copies and recomputed the main
statements independently (see "Rerunning the scripts"). It did not
re-derive every proof of Part I; for Part II, see "What the intake checked"
below.

## Files

```
README.md                                         this guide
article.tex                                       the report (LaTeX, internal bibliography), Parts I and II
article.pdf                                       the compiled report, 45 pages (numbered 1-45)
oeis_update_draft.txt                             Part I: the proposed OEIS update text (not submitted), as delivered
02-digitsum-SOURCE_AUDIT.txt                      Part II: the manuscript's source audit (pin, sources, novelty limits), as delivered
code/verify_a168362.py                            Part I: exact standard-library verifier (direct composition mod 4, residue sets, exceptions)
code/02-digitsum-verify.py                        Part II: direct and Bell composition; support, valuation, inverse, Fuss-Catalan, OEIS and period checks
code/02-digitsum-leading_residue.py               Part II: sparse digit-polynomial first-residue algorithm and its verifier
code/02-digitsum-cartier.py                       Part II: Cartier (finite-automaton) construction, queries and verifier
code/02-digitsum-make_figure.py                   Part II: redraws the figure from the grid data (needs matplotlib, numpy)
data/verification.json                            Part I: recorded PASS record of the run with --limit 256
data/verification_run.txt                         Part I: the run's captured standard output; byte-identical to verification.json
data/residue_sets.csv                             Part I: R_s for 1 <= s <= 64 (modulus, cardinality, residues)
data/exceptional_indices_to_10m.txt               Part I: the 37 indices n <= 10^7 with a(n) = 2 (mod 4), by the proved criterion
data/02-digitsum-verification.json                Part II: receipt of verify.py
data/02-digitsum-valuation_grid.json              Part II: v_2(A_2(m,N)) capped at 7, 1 <= m <= 48, 1 <= N <= 127 (figure data)
data/02-digitsum-leading_residue_verification.json  Part II: receipt of leading_residue.py --verify
data/02-digitsum-cartier_verification.json        Part II: receipt of cartier.py --verify
data/02-digitsum-document_qa.json                 Part II: the delivery's document QA record (of the delivered 23-page PDF)
figures/02-digitsum-valuation_grid.pdf            Part II: Figure 1, included by article.tex
figures/02-digitsum-valuation_grid.png            Part II: raster preview of Figure 1
```

Every file except `article.tex`, `article.pdf` and `README.md` is
byte-identical to its delivery. `data/residue_sets.csv` is CRLF as delivered
(kept by a `-text` line in `SetTheory/Cardinals/.gitattributes`). Part II's
delivered files carry the prefix `02-digitsum-`; their delivery names are
the same without it (Table 3 of the article maps them).

## Labels and edits

Every label carries the prefix `lim:`. The report has 172 labels.

- **Part I** has 63. The manuscript's 54 labels are kept, unchanged after
  the prefix; the batch-73 write added `lim:sec:collection`,
  `lim:sec:verification`, `lim:sec:questions` and `lim:app:inventory`; the
  batch-114 write added `lim:q:ratio`, `lim:q:higher-precision`,
  `lim:q:odd-prime`, `lim:q:automatic` and `lim:q:other-diagonals` on
  Research questions 13.1–13.5, which had none.
- **Part II** has 109 labels with the sub-prefix `lim:dsd:`: the
  manuscript's 84 (unchanged after the prefix), labels on its ten research
  questions (`lim:dsd:q:…`) and its two appendices, and 13 of the write
  (the Part heading and front Section 15 with its three tables and
  Remark 15.1).

No label of Part I was lost or renumbered (checked on the `.aux` files of a
build of the committed text and of this one), and no theorem, section,
equation or table number of Part I changed. In Part II the manuscript's
Section n is Section n + 15 (so its Theorem n.k is Theorem (n+15).k), its
research questions 1–10 are Research questions 27.1–27.10, its appendices A
and B are C and D, and its equations are numbered consecutively through the
report, as in Part I.

Part I is printed as delivered, apart from the label prefix, the Part
headings, the notes marked `[Write note, batch 73O1]` (seven; listed in the
batch-73 commit and still in place: status box, after Theorem 1.1, Section
1.3, Section 10, before Table 2, after Research question 13.7, Appendix B),
one note marked `[Write note, batch 77P2, 2 October 2026]` after Conjecture
11.1 (a method pointer to the iterated-Bell report), and the notes of the
batch-114 write, dated 6 October 2026:

- before the table of contents: the report now has two Parts;
- after Theorem 1.2, Proposition 5.1 and Proposition 6.1: Part II proves
  each again at p = 2 (pointers to its second routes);
- at Research questions 13.1 (still open), **13.2 (answered)**, **13.3
  (re-scoped, with the counterexample)**, 13.4 (still open; Part II's
  automaticity is a different statement) and 13.5 (advanced in one
  direction only);
- the heading "Appendices", with a note saying which appendix belongs to
  which Part.

The batch-114 write also corrected the names of Part I's cross-references.
Its theorem-like environments share one counter, and `cleveref` cited every
lemma, proposition, corollary, definition, conjecture, remark and research
question as a "Theorem" (for example "Summing Theorem 3.1" for Lemma 3.1).
The preamble now gives `cleveref` each environment's own name (the
`\AddToHook … \crefalias` pattern of `a082528-rounding-extinction`). No
number changed.

No symbol was renamed. Part II keeps the manuscript's symbols; its Table 5
fixes the reading where they collide with Part I's (T and τ, the carry
transform 𝒞 and the class 𝒞_p, R_s and the local R, b(n) of Part I = A112317
and b_p(N) = A_p(N,N), wt₂(N) = s₂(N), and others).

## What is claimed

**Part I.** With F(x) = x + x² + x⁴ + x⁸ + ⋯, G_m = F^{∘m}, g_m(N) = [x^N] G_m(x)
and a(n) = g_n(n) (A168362):

- **Theorem 1.1** (complete mod-4 classification): a(n) is even for n > 1,
  and a(n) ≡ 2 (mod 4) exactly for n ∈ {2, 3, 4, 6} and for n = 2^r + 2^s with
  r > s ≥ 1, r ≥ 3 and (r − s) mod 2^s ∈ R_s, where R_s ⊆ ℤ/2^s is defined by
  s + 2 bit tests. This settles the mod-4 pattern recorded in the OEIS entry
  (P. D. Hanna, 22 May 2026), confirms every listed exception through 520,
  and predicts the rest: 1028, 1032, 2056, 2064, ….
- **Theorem 1.2** (whole iteration array): g_m(N) ≡ 0 (mod 4) whenever N has
  at least three binary 1-bits, for every m; g_m(N) is odd only at powers of
  two. **Theorem 5.2** gives exact mod-4 formulas at one-bit and two-bit
  exponents.
- The tools: a balanced-pair valuation lemma and polarization of the
  lacunary operator mod 4 (Section 3), the carry transform and a one-step
  lift (Section 4), a closed form for the parity iterates via Lucas's
  theorem (Proposition 5.1).
- **Proposition 7.1**: R_s as a symmetric difference, |R_s| ≤ 1 + (s+1)(s+2)/2,
  and every nonzero d ∈ R_s satisfies d ≥ 2^s − 1 − 2s for s ≥ 3;
  **Corollary 8.1**: infinite families, e.g. a(2^r + 4) ≡ 2 (mod 4) iff r is
  even (r ≥ 3).
- **Theorem 9.2** (counting law): the number of exceptions up to X is
  κ log₂ X + O((log log X)³), κ = Σ_s |R_s|/2^s = 2.323930059308106….
- **Section 11**: the rigorous bounds n! ≤ A112317(n) ≤ a(n) ≤ n^{n−1}, hence
  log a(n) = n log n + O(n).

**Part II.** With F_p(x) = Σ_j x^{p^j}, A_p(m,N) = [x^N] F_p^{∘m}(x) for every
integer m (m < 0: iterates of the compositional inverse), s_p the base-p
digit sum and w_p(N) = (s_p(N) − 1)/(p − 1):

- **Theorem 16.1** (uniform digit divisibility): for every prime p and every
  m ∈ ℤ, A_p(m,N) = 0 unless N ≡ 1 (mod p − 1), and
  v_p(A_p(m,N)) ≥ w_p(N); at p = 2, 2^{s₂(N)−1} divides A_2(m,N). So a
  coefficient can be nonzero modulo p^q only if s_p(N) ≤ 1 + (q − 1)(p − 1).
  This **answers Part I's Research question 13.2** for every q.
- **Theorem 18.3**: the class 𝒞_p of integer series with p^{w_p(N)} | a_N is
  closed under composition, and its members with linear coefficient 1 form
  a group; every weighted seed x + Σ b_j x^{p^j} belongs to it (the broader
  composition theorem).
- **Proposition 19.1**: [x^{2p−1}] F_p(F_p(x)) = p. For odd p this is a
  nonzero coefficient modulo p² at base-p digit sum p > 2, so the suggestion
  in **Part I's Research question 13.3** ("digit sum at most two") is false;
  the question is re-scoped there with this counterexample and its one-line
  proof. This corrects a suggestion in a research question, not a theorem.
- Equation (51): A_p(m,p^r) ≡ (−1)^r C(−m, r) (mod p), and **Corollary 19.2**:
  p | A_p(N,N) for N > 1.
- **Theorem 20.1** (explicit first residue of the second iterate, a
  digit-polynomial formula for A_p(2,N)/p^{w_p(N)} mod p), **Theorem 20.3**
  (highest-digit stability), **Theorem 20.4** (three infinite families
  where the bound is attained, weights 1, 2, 3).
- **Theorem 21.1**: the inverse of x + x^p (Fuss–Catalan) attains the bound
  at every supported degree, so the bound is optimal in the class.
- **Theorems 22.1, 22.2**: candidate counts C_{p,q}(L) ~ L^R/R! (sparse
  support for every choice m = m(N)) and v_p ≥ (1/2 − ε) log_p N on a set of
  density one.
- **Theorem 23.4**: for each fixed m ≥ 0, prime p and q, N ↦ A_p(m,N) mod p^q
  is p-automatic, by an explicit Cartier construction.
- **Theorems 24.1, 24.2**: a coefficientwise p-adic iteration group
  z ↦ F_p^{∘z}, z ∈ ℤ_p, and a sufficient period p^{q − w + ⌊log_p d⌋} of
  each coefficient modulo p^q in the iteration parameter.

Part II proves three results of Part I again at p = 2, as special cases;
each is printed once, in Part I, with a write note in Part II recording the
second route: Theorem 1.2 (from Theorem 16.1; a different route, by integral
exponential series and Legendre's formula), Proposition 5.1 (from the
mod-p row formula; the same Frobenius-operator mechanism) and Proposition
6.1 (from Corollary 19.2). Part II does not re-prove Theorems 1.1, 5.2(c,d)
or 9.2; at p = 2, m = 2 and weights 0 and 1 its residue formula computes
the same residues as Theorem 5.2.

**The OEIS examples of A168365 and A168366** (Remark 15.1). The manuscript
says that the entries' prose examples have "an extraneous factor". The
intake confirmed it on the live entries (5 October 2026): both EXAMPLE
sections say "define F_{n}(x) = F_{n-1}(x*F(x)) as the n-th iteration of
F(x)", which taken literally gives F_1(x) = xF(x); the rows printed beneath
(114 and 110 entries), the DATA (19 and 18 terms) and the PARI programs are
all those of plain composition. Recorded only; nothing was submitted to
OEIS.

## What is not claimed

The manuscripts' non-claims are all kept in the text.

Part I:

- The OEIS ratio conjecture a(n+1)/a(n) ~ e·n (Hanna, 22 May 2026) is **not
  proved**; Section 11 says the arithmetic and the asymptotic questions "live
  at different scales". Conjecture 11.1 (a(n) = n^{n−2} L(n), L slowly
  varying) is a conjecture, supported only by Table 2.
- **Table 2** (R_n and C_n for n ≤ 299) is numerical orientation. No shipped
  program produces it; the intake recomputed the row n = 20 exactly and
  agrees to all printed digits, and did not reproduce the other rows.
- No Lean or other formal proof; Section 12 only sketches a formalization
  route.
- No publication priority; independent review is recommended before the
  proposed OEIS update (`oeis_update_draft.txt`, Appendix A) is submitted.
- **Research question 13.7** (A086753, distinct trinomial coefficients) is
  an aside unrelated to A168362. Its conjectural asymptotic
  (n² + 6n − 12)/12 in the OEIS entry is Vladimir Reshetnikov's own.

Part II:

- The digit bound is a necessary support condition, not an equality:
  extra divisibility is common (Figure 1). Apart from the second-iterate
  formula and families, no valuation is determined exactly.
- For the full second iterate, sharpness is proved only at weights 1, 2
  and 3; optimality at every degree only in the class 𝒞_p^1, through the
  inverse of x + x^p.
- Automaticity only for each fixed m ≥ 0 and fixed precision: not for the
  diagonal m = N, not for p-adic time, not for negative iterates modulo
  higher prime powers. The period of Theorem 24.2 is sufficient, not
  minimal; the automaton setup can grow quickly.
- The ratio conjecture is not touched; Part I's diagonal classification and
  counting constant are credited, not re-proved; its candidate count at
  q = 2 is coarser than Part I's counting law.
- Novelty only relative to the inspected sources (a bounded search); the
  classical tools (Legendre, Hurwitz-series composition, Lagrange inversion,
  Fuss–Catalan, the kernel criterion, Frobenius lifting) are credited.
- No peer review and no formal verification. The source audit's "two
  independent mathematical reviews" were, by `02-digitsum-document_qa.json`,
  two AI audits; that is a process claim the intake cannot verify.
- Appendix C is a draft OEIS note, not submitted. No repository file or OEIS
  entry was modified by the manuscript's authors.
- Its ten research questions (Section 27: diagonals mod 8 and 16, sharpness
  at depth w ≥ 4, residues of higher iterates, minimal Cartier
  representations, inverse-iterate automaticity, optimal periods, typical
  excess valuation, automaticity for weighted seeds, the ratio conjecture,
  formalization) are open; the write found no other unproved claim and no
  wrong statement in the manuscript.

## Relation to neighbouring material

- **No other host.** A168362, A168365, A168366, A112317, A122888 and
  A086753 occur nowhere else in the repository except the catalogue and the
  pointer from the iterated-Bell report below, and no other report proves
  anything about iterates of Σ x^{2^j} or Σ x^{p^j}. (A339422, the
  coefficients of a reciprocal series built from the Rueppel sequence, is
  cited in `rueppel-binary-run-determinants`; a reciprocal is not an
  iterate, and there is no overlap.)
- **Siblings in `iterated-series`**, congruences of compositional iterates
  of other series, no overlap:
  [`a396807-self-iterating-series`](../a396807-self-iterating-series/)
  (A(x) = x + A^{[5]} A^{[6]} modulo 10 and 100; it also treats iterates of
  every integer order and p-adic-time iteration of its own series, as Part
  II does for F_p) and
  [`compositional-tree-series-congruences`](../compositional-tree-series-congruences/)
  (A_l = x·exp(A_l^{∘l}) modulo prime powers; its wider class of tree
  specifications excludes ordered children and arbitrary degree
  restrictions, which F_p needs). Part II's source audit names both as
  methodological neighbours, not sources.
- **A candidate method for Conjecture 11.1 (pointer only):**
  [`a139383-iterated-bell-diagonals`](../../../generating-functions-and-asymptotics/oeis-sequence-asymptotics/a139383-iterated-bell-diagonals/)
  (batch 77) proves all-orders asymptotics for the diagonal
  `n! [z^n] (e^z − 1)^{∘(n+k)}` of the iterated Bell numbers by a fixed
  contour, an effective Fatou coordinate and uniform cut estimates. It is a
  candidate route to the refined asymptotic here, not a proof: `F` is
  lacunary with natural boundary |x| = 1, its quadratic and cubic Taylor
  coefficients (1, 0) differ from those of `e^z − 1` (1/2, 1/6), and the
  normalizations differ. The conjecture stays open (dated note after
  Conjecture 11.1).
- **Same technique:**
  [`a000139-binary-carries-parity`](../../a000139-binary-carries-parity/)
  uses binary carries (Kummer–Lucas) for the parity of a different sequence.
- **Lean.** Placement in this collection confers no formal status. No Lean
  or Rocq declaration of the repository concerns these iterates, and none
  of the statements of this report is formalized (Part II's Research
  question 27.10 proposes it).

## Building

From a scratch copy of this directory (the figure
`figures/02-digitsum-valuation_grid.pdf` must be present), run

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX 26.2) produced the shipped `article.pdf`: 45 pages, with no
errors, no warnings, no undefined references or citations, no multiply
defined labels, no duplicate destinations, and no overfull or underfull
boxes. Copy back only `article.pdf`.

## Rerunning the scripts

**Part I.** By default `code/verify_a168362.py` writes `verification.json`,
`residue_sets.csv` and `exceptional_indices_to_10m.txt` into `data/` under
its parent directory, so a run in place **overwrites the shipped records**.
Pass `--root` with a scratch directory:

```sh
R=SetTheory/Cardinals/docs/reports/congruences-and-valuations/iterated-series/a168362-lacunary-iterates-mod4
W=$(mktemp -d)
py "$R/code/verify_a168362.py" --limit 256 --root "$W" > "$W/verification_run.txt"
```

The script needs only the Python standard library and runs in about a
second. The intake ran it this way on a copy (exit code 0):
`residue_sets.csv` is byte-identical to the shipped file, and
`verification.json`, `exceptional_indices_to_10m.txt` and the captured
standard output are equal up to line endings (on Windows `Path.write_text`
and the console write CRLF; the delivered files are LF).

Independently of the delivered code, the intake composed F modulo 4 with
its own code to degree and iterate 1100. The diagonal exceptions are
2, 3, 4, 6, 20, 24, 40, 68, 136, 260, 520, 1028, 1032, as Theorem 1.1
predicts (the last two are its first predictions beyond the OEIS list), and
Theorem 1.2 holds for all m ≤ 300, N ≤ 1100. It also recomputed
a(1), …, a(10) exactly (equal to the OEIS data), R_1, …, R_8 from the
definition (equal to Table 1), |R_s| for s ≤ 16, the tail bound
Σ_{s>64}(1 + (s+1)(s+2)/2)/2^s = 285/2^61 used for κ, and the row n = 20 of
Table 2. The OEIS statements the article quotes (A168362's comments of 22
May 2026, A112317, A122888, A086753) were confirmed on the live entries on
1 October 2026.

**Part II.** The programs need Python 3.10 or later and only the standard
library (`make_figure.py` also needs matplotlib and numpy). They expect the
delivered layout: run them on a copy with the prefix removed, never in
place. `make_figure.py` reads `data/valuation_grid.json` and writes
`figures/valuation_grid.pdf` and `.png` under its parent directory, so in
this directory it fails (the data file has another name), and in a copy of
the delivered layout it overwrites the copy's figure.

```sh
R=SetTheory/Cardinals/docs/reports/congruences-and-valuations/iterated-series/a168362-lacunary-iterates-mod4
W=$(mktemp -d); mkdir -p "$W/code" "$W/data"
for f in verify leading_residue cartier make_figure; do cp "$R/code/02-digitsum-$f.py" "$W/code/$f.py"; done
cd "$W"
py code/verify.py --output data/verification.json --heatmap data/valuation_grid.json
py code/leading_residue.py --verify data/leading_residue_verification.json
py code/cartier.py --verify --verification-output data/cartier_verification.json
py code/leading_residue.py --prime 3 --degree 51         # weight 2, normalized residue 1
py code/cartier.py -p 2 -q 3 -m 2 -n 1125899906842630    # A_2(2, 2^50+6) = 4 (mod 8)
```

The intake ran these on 5 October 2026 (Python 3.14.4, Windows): all
three verifiers pass in about a second each (`verify.py`: 4,236 support,
valuation and integrality checks, 336 Bell comparisons, 750 Fuss–Catalan
valuations, 30 OEIS fixtures, the odd-prime identity at p = 3, 5, 7, 11;
`leading_residue.py`: 1,204 coefficient checks, stability and families;
`cartier.py`: 2,052 comparisons), the four regenerated JSON files equal the
shipped ones up to line endings (on Windows they are written CRLF), and the
two queries return the values shown. `make_figure.py` was not run.

Independently of the delivered code, the intake composed the series with
its own exact integer code: 3,340 coefficients (p = 2 with 1 ≤ m ≤ 6,
N ≤ 160, and m = −1, −2, −3, N ≤ 60; p = 3 with m ≤ 5 and m = −1, −2; p = 5;
p = 7) satisfy Theorem 16.1 without exception; its own implementation of the
residue formula of Theorem 20.1 agrees in 160, 80, 40 and 20 cases for
p = 2, 3, 5, 7; [x^{2p−1}] F_p(F_p) = p for p = 2, 3, 5, 7; the first two
families have the stated valuations where in range; the Fuss–Catalan
valuation identity holds for 60 values of k at each of p = 2, 3, 5; and the
counts 1350 and 6195, the exponential coefficients 1, 1, 3, 315 and
A_2(2,7) = 8 are right. All terms of A168362, A168365 and A168366 on OEIS
(21, 19, 18) equal A_2(n,n), A_2(n−1,n), A_2(n+1,n) by plain composition and
are divisible by 2^{s₂(n)−1}.

OEIS data used as fixtures (A168362, A168365, A168366) are available under
CC BY-SA 4.0.

## Disclosures and discrepancies

- **Two identical records (Part I).** `data/verification_run.txt` is the
  captured standard output of the recorded run, which prints the same JSON
  as it writes; the file is byte-identical to `data/verification.json`.
  Both are shipped, as delivered.
- **A hash inside the data (Part I).** `data/verification.json` carries a
  field `direct_table_sha256` (the digest of the 256 × 256 direct table, also
  printed in Section 10). It is delivered data, not a checksum of any
  shipped file.
- **Delivery names in shipped text (Part II).** The text of Part II, the
  source audit (`02-digitsum-SOURCE_AUDIT.txt`, which mentions `data/*.json`)
  and the JSON receipts name the delivered files without the prefix; the
  document QA record `data/02-digitsum-document_qa.json` describes the
  delivered 23-page PDF, which is not shipped (this report's PDF is a build
  of the merged text).
- **Not shipped:** Part I's delivered `README.md`, `article.pdf`,
  `MANIFEST.txt` and `SHA256SUMS.txt` (in `3a9518c52`); Part II's delivered
  `article.tex`, `article.pdf`, `README.txt` and `SHA256SUMS.txt` (in
  `e4d5dcf9e`). Appendices B and D of the article (delivered text, each
  followed by a write note) list some of these as delivery files.
- **Paths.** Every Part I file keeps its delivered path;
  `oeis_update_draft.txt` stays at the root. Part II's files are in `code/`,
  `data/`, `figures/` and the root with the prefix `02-digitsum-`.
- **Bibliography.** Part I's delivered bibliography lists Stanley's
  *Enumerative Combinatorics 1*, Flajolet–Sedgewick's *Analytic
  Combinatorics* and the ProveIt repository without citing them; they are
  kept, and the write note of Section 1.3 cites them as background and as
  the inspected repository. Part II also cites Flajolet–Sedgewick, for
  Lagrange inversion. Part II's entries for the three OEIS sequences and
  for Flajolet–Sedgewick are merged into Part I's; its other entries carry
  the keys `dsdrepo` (this is Part I), `dsdBCM` and `dsdRY`. The intake
  checked Theorem 1.8 and the congruence in the proof of Proposition 1.9 of
  Rowland–Yassawi against arXiv:1310.8635v2 (same numbering; the journal
  version was not read), and the arXiv record of Barbero–Cerruti–Murru
  against the printed reference.
