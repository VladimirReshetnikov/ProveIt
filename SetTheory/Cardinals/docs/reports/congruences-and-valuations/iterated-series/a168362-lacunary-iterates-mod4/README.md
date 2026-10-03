# Binary Carry Structure in Iterated Lacunary Series

**A complete modulo-four theorem for OEIS A168362, an exact exception criterion, and a logarithmic counting law**

This research report is dated 1 October 2026. It was built from one
manuscript, manuscript 49 of batch 73 (cluster O1) of ProveIt's
incoming-reports intake. Its author line is "Research note prepared for
Vladimir Reshetnikov with OpenAI".

| Source | Batch-73O1 manuscript | Archive | Pin | Arrived | Placed | Printed as |
|---|---|---|---|---|---|---|
| single source | 49 | `ProveIt_A168362_Mod4_Theorem.zip` (inner directory `A168362_Mod4_Theorem/`; *Binary Carry Structure in Iterated Lacunary Series*, main file `article.tex`, 15-page PDF as delivered) | none | `3a9518c52` | `9df4ba51a` | the whole report, Sections 1–14 and Appendices A–B |

The manuscript names no pinned commit; it says the repository was
"inspected October 1, 2026". No other manuscript of batch 73 treats
A168362, so nothing was merged. The delivered README, PDF, `MANIFEST.txt` (a
file list without hashes) and `SHA256SUMS.txt` ledger (9/9 verified at
placement) are not shipped and survive in `3a9518c52`.

**Status: AI-assisted, unrefereed, not formalized.** The intake reran the
verifier on a copy and recomputed the main predictions independently (see
"Rerunning the script"). It did not re-derive every proof.

## Files

```
README.md                                this guide
article.tex                              the report (LaTeX, internal bibliography)
article.pdf                              the compiled report, 17 pages (numbered 1-17)
oeis_update_draft.txt                    the manuscript's proposed OEIS update text (not submitted), as delivered
code/verify_a168362.py                   exact standard-library verifier (direct composition mod 4, residue sets, exceptions)
data/verification.json                   recorded PASS record of the run with --limit 256
data/verification_run.txt                the run's captured standard output; byte-identical to verification.json
data/residue_sets.csv                    R_s for 1 <= s <= 64 (modulus, cardinality, residues)
data/exceptional_indices_to_10m.txt      the 37 indices n <= 10^7 with a(n) = 2 (mod 4), by the proved criterion
```

Every file except `article.tex`, `article.pdf` and `README.md` is
byte-identical to the delivery. `data/residue_sets.csv` is CRLF as delivered
(kept by a `-text` line in `SetTheory/Cardinals/.gitattributes`).

## Labels and edits

Every label carries the prefix `lim:`. The manuscript's 54 labels are kept,
unchanged after the prefix; the write added four, `lim:sec:collection`
(Section 1.3), and `lim:sec:verification`, `lim:sec:questions` and
`lim:app:inventory` on Section 10, Section 13 and Appendix B, which had no
labels. The report has 58. No theorem, section, equation or table number of
the manuscript changed.

The text is printed as delivered, apart from the label prefix and seven
notes marked `[Write note, batch 73O1]`:

- in the status box on page 1;
- after the residue sets of Theorem 1.1: since R_1 = ∅, case (ii) never
  holds with s = 1, so the condition "r > s ≥ 1" is effectively s ≥ 2 (kept
  as stated);
- Section 1.3 "Place in the ProveIt collection": provenance, status, the
  intake's checks, the two uncited bibliography entries, neighbouring
  reports;
- Section 10: the rerun hazard and the identity of the two recorded files;
- before Table 2: the table is numerical orientation only;
- after Research question 13.7: the A086753 aside;
- Appendix B: which inventory files are shipped.

One later note, marked `[Write note, batch 77P2, 2 October 2026]`, follows
Conjecture 11.1: a method pointer to the iterated-Bell report (see
"Relation to neighbouring material"). It adds no label.

No symbol was renamed.

## What is claimed

With F(x) = x + x² + x⁴ + x⁸ + ⋯, G_m = F^{∘m}, g_m(N) = [x^N] G_m(x) and
a(n) = g_n(n) (A168362):

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

## What is not claimed

The manuscript's non-claims are all kept in the text:

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

## Relation to neighbouring material

- **No repository host.** A168362, A168365, A168366, A112317, A122888 and
  A086753 occur nowhere else in the repository, and no report proves
  anything about iterates of Σ x^{2^j}. (A339422, the coefficients of a
  reciprocal series built from the Rueppel sequence, is cited in
  `rueppel-binary-run-determinants`; a reciprocal is not an iterate, and
  there is no overlap.)
- **Siblings in `iterated-series`**, congruences of compositional iterates
  of other series, no overlap:
  [`a396807-self-iterating-series`](../a396807-self-iterating-series/)
  (A(x) = x + A^{[5]} A^{[6]} modulo 10 and 100) and
  [`compositional-tree-series-congruences`](../compositional-tree-series-congruences/)
  (A_l = x·exp(A_l^{∘l}) modulo prime powers).
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
  of the statements of this report is formalized.

## Building

From a scratch copy of this directory, run

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

No figures or other inputs are needed. pdfLaTeX (MiKTeX 26.2) produced the
shipped `article.pdf`: 17 pages, with no errors, no warnings, no undefined
references or citations, no multiply defined labels, no duplicate
destinations, and no overfull or underfull boxes. Copy back only
`article.pdf`.

## Rerunning the script

By default `code/verify_a168362.py` writes `verification.json`,
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

## Disclosures and discrepancies

- **Two identical records.** `data/verification_run.txt` is the captured
  standard output of the recorded run, which prints the same JSON as it
  writes; the file is byte-identical to `data/verification.json`. Both are
  shipped, as delivered.
- **A hash inside the data.** `data/verification.json` carries a field
  `direct_table_sha256` (the digest of the 256 × 256 direct table, also
  printed in Section 10). It is delivered data, not a checksum of any
  shipped file.
- **Not shipped:** the delivered `README.md` (replaced by this guide),
  `article.pdf` (replaced by a build of this text), `MANIFEST.txt` and
  `SHA256SUMS.txt`. Appendix B of the article (delivered text, followed by a
  write note) lists `article.pdf` and `README.md` as delivery files.
- **Paths.** Every shipped file keeps its delivered path;
  `oeis_update_draft.txt` stays at the root.
- **Uncited bibliography entries.** The delivered bibliography lists
  Stanley's *Enumerative Combinatorics 1*, Flajolet–Sedgewick's *Analytic
  Combinatorics* and the ProveIt repository without citing them. They are
  kept; the write note of Section 1.3 cites them as background and as the
  inspected repository.
