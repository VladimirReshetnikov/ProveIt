# Editorial log

The dated log of revisions and checks of the continuously revised editions
of the six articles in this directory. Its baseline is the edition as it
stood on 13 September 2026. The editorial notes themselves are consolidated
per article in `<year>/jones<year>_editorial_notes.md` (every discrepancy
between a naive OCR reading of the printed article and the edition, with
classification and justification).
Every change to a source in `Papers/` since the baseline is listed here with
its location in the original pagination, the old and new text, a
classification, and the reason. Checks that found nothing are recorded too,
so that they need not be repeated. Dates are 2026-09-13 unless stated.

Classifications are those of the editorial notes: **OCR** (transcription
defect), **ORIG** (error in the printed original), **CLAR** (clarification
or proof completion, marked as editorial in the text), **TYPO**
(typographical or cross-reference slip, no mathematical content), **BIB**
(bibliographic), **EDN** (edition metadata), **BUILD** (build or
packaging).

Verification programs for the checks recorded here live in `verification/`
and write a `round4_<year>_results.json` next to themselves. Run them with
`PYTHONUTF8=1 python verification/round4_<year>_checks.py`.

---

## 1976 — Diophantine Representation of the Set of Prime Numbers

**Status: read twice in full (the baseline source against the OCR; second
reading 2026-09-14 against the scan); numeric checks passed. One TYPO fix and one
BIB fix in the first reading; ten typographical and fidelity items in the
second. No mathematical error.**

### Checks performed (`verification/round4_1976_checks.py`)

- The displayed polynomial (1) has total degree 25 in 26 variables, and equals
  `(k+2){1 - Σ(equation of Theorem 2.12 with k replaced by k+1)^2}` exactly
  (symbolic identity), as the text claims.
- The introduction's example value **−76** is attained: at
  `a=b=c=d=0, e=1, f=6, g=0, h=2, i=1, j=0, k=0, l=0, m=1, n=0, o=2, p=1,
  q=0, r=s=t=0, u=1, v=0, w=0, x=1, y=0, z=4` the value is −76. (A first
  hand-built candidate gave −108; the value −76 was then found by search.)
- Formula (5) for the n-th prime, exactly as typeset (upper limit n², inner
  sum from j=0, the convention r(y,0)=y), returns p_n for n = 1..40. The j=0
  term contributes 1, which is what makes `∸n` correct; this is not a defect.
- Lemma 2.3: the least n with e³(e+2)(n+1)²+1 a square is 2, 20, 244, 4060,
  87814 for e = 2..6, each ≥ e−1+e^(e−2) as stated.
- Lemma 2.4: congruence checked for a=1..8, p=0..11, n=0..8, including the
  degenerate (a,p)=(1,1) case handled by the editorial clarification 1976-17; the
  inequality "right side ≤ left side when 0<p^n<a" holds in that range.
- Lemma 2.10: the double inequality holds for k=1..4 on sample (n,p) at the
  boundary (2k)^k ≤ n, n^k < p.
- Hand-checked the inequality chains in Lemma 2.10 (i)–(iv), Lemma 2.11
  (sufficiency and necessity, including h,j ≥ 0), Theorem 2.12 (the modulus
  inequalities a < 2a(n+1)−(n+1)²−1 etc. and p ≥ 3), Lemmas 3.1–3.6, the
  estimates (2)–(21) in the proof of Theorem 3.9, and the necessity
  construction (23). No gap found beyond those already closed in the edition
  (`1976/jones1976_editorial_notes.md`).
- Counts at the end of §3: 10 unknowns + 1 = 11; 12-variable P; degree
  2·6848+1 = 13697. Consistent.
- **Theorem 3.9, numerical instance** (`verification/round4_1976_theorem39.wl`,
  Wolfram Language, about nine minutes): for k = 1 the necessity witnesses
  were built exactly as in the proof: n = 244 (the least n with U(2,n) a
  square), x + 1 = ψ₄₉₁(490)/490 (1461 digits, U(2n,x) a square), w from
  ⌊(x+1)ⁿ/xᵏ⌋ = C(n,k) + (w+1)x, M = 16nx(w+2)+1 (354,894 digits),
  K = ψ_M(244) (86,239,183 digits), L = 2Mx, R = 2Mnx, C = ψ_{M(x+1)}(245)
  (86,950,427 digits). With σ′ = C/(KL) − (w+1)x computed from the exact
  integer numerator, σ′ = 244.000… = C(n,k) and β = 1.000… = k!, with
  |β − k!| < 10⁻¹⁹⁹, so (XIV) holds; the Case-1 bounds (15) and (17) hold
  too. (A first run silently failed because `C` is a protected symbol in
  Wolfram Language; the script now uses `CC`.)

### Comparison with the OCR of the scan

- "Our construction here yields a polynomial in 19 variables and degree 29"
  (p. 449) is the original wording. It refers to an intermediate elimination,
  not to (1); retained.
- "M > 160·10¹⁰" in (5) of §3 is the original bound (OCR line 511); it is
  true and harmless; retained.
- The example value −76 is in the original.

### Second full reading (2026-09-14)

An independent line-by-line reading against the scan (zoomed where the
OCR was doubtful) and the discrepancy register of the edition, with SymPy checks in a
scratch script. Found: no mathematical error; the ten typographical and
fidelity items 76-R4-03 … 76-R4-12 below. Checks that found nothing, for
the record:

- Polynomial (1) equals `(k+2){1 − Σ eq_i²}` with the fourteen equations of
  Theorem 2.12 under `k → k+1`, term by term against the scan.
- Lemmas 2.1–2.4 (the Lemma 2.3 step `(a−2)(a−1)+(a−1)^(a−2) < (2a−1)^(a−2)`
  holds for `a ≥ 3`, the case `a = 2` being excluded by `e ≥ 2`; Lemma 2.4's
  inequality by brute force for `a ≤ 39`, `n ≤ 13` and by hand for all `n`),
  Lemmas 2.5–2.6 (`v = 0` exclusion), Lemma 2.10 (i)–(iv) including
  `2k²k! ≤ (2k)^k` with equality at `k = 1, 2`, Lemma 2.11 both directions.
- Theorem 2.12: (1′)–(4′) from Lemma 2.3 with `e = 2k` and
  `e = p+q+z+2n`; all nine modulus inequalities; the three applications of
  Lemma 2.4 with `(P,N) = (n+1,k), (p+1,n), (p,k)`; necessity uses `p^k < a`,
  which is what the sign of `t` needs.
- §3: Lemmas 3.1–3.6 (3.4 numerically for `k ≤ 8` and by hand; the hint
  "as in 2.10(iv)" is right because only `k−1` factors are nontrivial);
  Lemma 3.8 and the system (I)–(XXI) identical to the scan; every estimate
  (2)–(23) including the need for `n ≥ k+3` in (17); the
  denominator-clearing identity for (XIV); the ten-unknown count; (24)'s
  second factor `≡ 1 (mod T)`, `2(n+1) | j`, degree `2·6848+1 = 13697`.
- §4: the rewritten proofs of Theorems 4.2 and 4.4 read step by step; no
  gap found.
- Cross-references: all citation keys, tags (1′)–(8′), (1)–(24), (i)–(iv),
  lemma and theorem numbers, and the pointer "the convention before Theorem
  4.2" resolve; the gaps in the equation numbering (no (2) in §1, no
  (6)–(7) in §4) are in the scan. All twenty references check against the
  scan; [5] and [15] are uncited in the scan too.
- The formula (5) as printed (outer parentheses, three proper subtractions)
  returns `p_n` for `n = 1..15` in the scratch script, in addition to the
  `n = 1..40` check of `round4_1976_checks.py`.

### Changes

| id | location (orig.) | class | old | new | reason |
|---|---|---|---|---|---|
| 76-R4-01 | §3, proof of Theorem 3.9, display (2) | TYPO | "by Lemmas 2.3 and 3.7" | "by Lemma 2.3 and Definition 3.7" | 3.7 is a definition (of U(x,y)), not a lemma. Original wording; cross-reference precision only. |
| 76-R4-03 | §2 opening (p. 451); (12) p. 458; (23) p. 461 | TYPO | `$\lfloor x\rfloor$ denotes the greatest integer`; `\left\lfloor (x+1)^n/x^k \right\rfloor` in (12) and (23) | `$[x]$ denotes …`; `\left[ (x+1)^n/x^k \right]` | The printed article defines and uses `[x]`; the edition kept `[ ]` in (131), Lemma 3.3 and the necessity proof but had switched the definition, (12) and (23) to `⌊ ⌋` (an earlier, unrecorded change). One notation throughout, the printed one. |
| 76-R4-04 | (1), p. 449 | EDN | display begins `P(a,b,\ldots,z)=(k+2)\{1 …` | `(k+2)\{1 …` | The name prefix is not in the printed display (scan p. 449: "(k+2){1 − [wz+h+j−q]² …"); it had been inserted earlier without a register entry. Removed for fidelity; the text names the polynomial `P` in the following paragraph anyway. |
| 76-R4-05 | (5), p. 450 | EDN/OCR | `\left[1 ∸ (…) \right], \qquad n\geq1.` | `\left(1 ∸ (…) \right).` | The scan prints outer parentheses (the edition's brackets read as an integer part under the article's own `[x]` convention) and no qualifier `n ≥ 1`; both changes had been made earlier, together with the repair of the formula (1976-11), without being recorded. Printed form restored; the formula as printed is verified for n = 1..40 (`round4_1976_checks.py`). |
| 76-R4-06 | proof of Theorem 3.9, display before (22), p. 459 | OCR | `using (18) (16) and (10)` | `using (18), (16) and (10)` | The comma after (18) is in the scan; the OCR dropped it. |
| 76-R4-07 | proof of Theorem 3.9, remark after (22), p. 461 | TYPO | `Lemmas 2.7, 2.8, 3.1-3.7, equations (I)-(XIII)` | `Lemmas 2.7, 2.8, 3.1--3.6, Definition 3.7, equations (I)--(XIII)` | Second occurrence of the "Lemma 3.7" slip corrected by 76-R4-01 (3.7 is the definition of U(x,y)); original wording. |
| 76-R4-08 | Theorem 2.12 proof, display after "(3′) and (4′)", p. 454 | TYPO | `p<a,(n+1)^{k}<a \quad \text{and}` | `p<a, \quad(n+1)^{k}<a \quad \text{and}` | Spacing as in the two sibling displays (`q<a, \quad(p+1)^n<a`; `z<a, \quad p^{k+1}<a`) and in the scan. |
| 76-R4-09 | Lemma 2.3 statement, p. 451 | TYPO | `it is possible to satisfy 2.3 with $n$` | `… satisfy (2.3) with $n$` | The condition is tagged (2.3) and cited as "(2.3)" everywhere else; printed original reads "2.3". |
| 76-R4-10 | §2 (p. 452), Theorem 2.12 proof (p. 454), Theorem 3.9 proofs (pp. 458, 461) | TYPO | `I-VIII`, `(1)-(14)`, `(I)-(XXI)` (twice), `(XV)-(XX)` | en dashes | Ranges elsewhere in the edition use `--`; the hyphens were OCR carry-overs. |
| 76-R4-11 | edition note after Theorem 1 (footnote, clarified) | BUILD | `\noindent\footnotesize … \normalsize` followed by a blank line | `{\footnotesize\noindent … \par}` | `\normalsize` was issued before the paragraph end, so the paragraph was set in footnote-size type on the normal baseline skip. Text unchanged. |
| 76-R4-12 | editorial verification note after Theorem 5 | EDN | a pointer to "the companion editorial report" and to `PRIMALITY_87.md` | a pointer naming the earlier editorial report and its `1976/PRIMALITY_87.md`, which are not part of this project | The certificate file was not next to this source, so the pointer was made precise; superseded by 76-R4-13. |
| 76-R4-02 | reference [8] (p. 464) | BIB | "Soviet Math., Doklady, 11 (1970) 354--358" | "… 354--357" | The printed range is 354–358. The *Journal of Symbolic Logic* Reviews entry for this paper (Cambridge Core, "Ju. V. Matijasevič. Enumerable sets are diophantine. English translation … by A. Doohovskoy. Soviet mathematics, vol. 11 no. 2 (1970), pp. 354–357. See Errata, ibid., vol. 11 no. 6, p. vi.") gives 354–357, as do Matiyasevich's own publication list and the 1974, 1982 and 1984 articles. The editions of 1978 and 1980 had already been emended to 357; this makes the corpus consistent. See the corpus-wide note below. |
| 76-R4-13 | editorial verification note after Theorem 5 | EDN | the pointer of 76-R4-12 to notes that are not part of this project | "in the file `jones1976_primality87.md` of `Papers/verification/` and is checked in Lean, in `Lean/Diophantine/Paper1976/PrimalityCertificate.lean`" | The certificate document is regenerated there by `verification/jones1976_verify_87_operations.py`; see the corpus-wide item on the consolidated notes. |
| 76-R4-14 | proof of Lemma 2.11 (Sufficiency), p. 452 | TYPO | "conditions I-VI" | "conditions I--VI" | The scan has an en dash; the last range missed by 76-R4-10. |

---

## 1982 — Universal Diophantine Equation

**Status: fully read; block structure of Theorems 1–3 re-derived by hand and
symbolically; section-2 lemmas brute-force checked; universal-pair list and
two wording points compared with the OCR. No change required.**

### Checks performed (`verification/round4_1982_checks.py`)

- Digit and carry Lemmas 2.1–2.8, 2.10, 2.15, 2.16 verified by brute force on
  small ranges (bases 2..32, arguments < 70, N ∈ {2,4,8}).
- Lemma 2.9 verified exhaustively for z ∈ {2,4}, m ≤ 2, all y and all
  candidate Y below the bound.
- Pell Lemmas 2.19, 2.20, 2.21 checked for A=2..7; Lemma 2.22(iii) and the
  χ-form congruence D ≡ W + C(A−V) checked for A=2..11, V<A, B=1..6.
- The packed expression for r in Theorems 2 and 3 equals
  S(N²−N)+(T+1)(N²−1) with S, T, N built from (U12)–(U24) and N = q¹⁶
  (symbolic identity), and the three binomial coefficients of Theorem 1 are
  exactly the three (S_i, T_i) pairs. This re-confirms the edition's exponent
  corrections q⁷ and q⁸ (1982-08) from the block structure: N₁N₂ = q⁷ and
  T₃ = (b⁵−2)q sits at q⁷·q = q⁸.
- Theorem 3 was mapped equation by equation onto Lemma 2.25 (B1)–(B14) with
  the χ-form congruence and Corollary 2.29 (Q1)–(Q3): p = 2M²U with
  M = rsn², U = wn²; k = R+1+h(P−1); 4(c−ksn²)²+η = k² is (B3) with Y = n²s;
  a = M(U+1); c = 2r+1+φ; d = bw + c(a−2) + γ(4a−5); (d+of)² … is (Q3).
  All consistent.
- §5 variable count: 53 listed variables (34 capital, 19 lower-case) − 17
  eliminated + 22 new = 58. The nine-unknown degree 47216·5⁵⁸+9728 ≈
  1.638×10⁴⁵ as stated.
- Hand-checked the sufficiency and necessity estimates (1)–(14) of Lemma
  2.25, Lemma 2.26 (13)–(14), the size inequalities in §4 (the Lemma 2.9
  hypotheses, 4zb² < B, elg² < q², 0 ≤ S₃), and the §5 bound |h_j| < B/2.
- **Lemma 2.25, numerical instance** (`verification/round4_1982_lemma225.py`):
  with R = 63 (six binary ones, so 2⁶ | C(126,63)), N = b = 8, the witnesses
  were built exactly as in the necessity proof (w = 2¹²⁴, U = 2¹³⁰,
  Y = [ρ] with 8191 bits, A with 8326 bits, C = ψ_A(127) with 1,049,200
  bits, K = ψ_P(64) with 1,041,010 bits). All of (B1)–(B14) with (B8') hold
  exactly, including the sharper |C/K − Y| < 1/4 of the proof, the χ-form
  congruence D ≡ W + C(A−V) used in Theorem 3, and [ρ] ≡ C(2R,R) (mod U).
  Runtime about three seconds.

### Comparison with the OCR of the scan

- Theorem 4 in the 1982 original lists exactly the twelve pairs shown; the
  1980 announcement's sixteen-row table is the longer list. No row is
  missing from either edition.
- "Equation (A5) is due to R. Krisnis" is the original spelling; retained.
- Lemma 2.25, necessity: "since A ≥ 32768" is the original; sufficiency
  derives A ≥ 33280. Both are true (33280 > 32768); retained as printed.

### Second full reading (2026-09-14)

An independent line-by-line reading against the scan and the discrepancy
register of the edition (now `1982/jones1982_editorial_notes.md`), with a
normalized word-level diff against the OCR (253 hunks, every one accounted
for by that register or pure formatting) and SymPy checks in a scratch
script. One error in the printed original was found (82-R4-01 below); no
mathematical error. Checks that found nothing:

- §2 by hand: Lemmas 2.1–2.13 (including the `B = 2` edge of 2.8 and the
  `m > n` extension of 2.9), Theorem 2.14, Lemmas 2.15–2.17, 2.19–2.24,
  every step (1)–(12) of Lemma 2.25 in both directions (`A ≥ 33280` against
  the printed 32768 is the documented item 1982-36), Lemma 2.26 (13)–(14),
  the congruence properties of both `G` forms in Lemmas 2.27–2.28,
  Corollary 2.29. By script: the identity of Lemma 2.16, Lemma 2.21 for
  `A ≤ 60`, 2.19/2.20 for `A ≤ 8`, 2.22(iii) for `A ≤ 14`, explicit
  positive witnesses for (Q1)–(Q3) at five `(A,B)` pairs, the congruences
  of the alternate `G`, the four-sign product identity of §5.
- §3–§5: the `β`-bound giving `|coeff| < B/2`, the degree
  `(2δ+1)(δ+1)^ν`, the block bounds with `N₁ = 2B^((2δ+1)(δ+1)^ν+1)`, the
  (B3′) stacking, the eight-unknown residue list; in §4 both size
  inequalities before Lemma 2.9, the mask (U9), the corrected chain
  `elg² < 4zb²B^((δ+4)K) < B^(2L)`, `0 < D₀ < zλ`, the series lengths of
  (4.9)–(4.11), `0 ≤ S₃` (needs `32z ≤ B`, `xB < q`), `(U6′) ⇔ (U1) ∧ (U6)`,
  the block sizes `q³, q⁴, q⁹`, Theorem 3 against (B1)–(B14)/(Q1)–(Q3)
  equation by equation including `p = 2ws²r²n⁶` and
  `d = bw + ca − 2c + 4aγ − 5γ`; in §5 the bounds from (D2), (D7), (D8),
  the mask (D11), the no-carry bound with `ν+2 ≤ 2^(ν+1)`, the
  correspondences (D3)–(D5) ↔ (C1′)–(C3′), (D25) ↔ Lemma 2.26,
  (D30)–(D37) ↔ (P1)–(P7), and the Lemma 2.26 size chain.
- Counts: 12/14/28 unknowns; 28 + 30 = 58; 34 capitals + 19 lower-case =
  53 = 58 − 22 + 17; the 22 auxiliaries make every (D) equation quadratic
  (including `S` with the `c⁴Q³` auxiliary); `q = b^(5^60)` for `ν = 58`;
  `D₉ = 47216·5^58 + 9728`; the symbolic identity of the Theorem 2/3 `r`
  with `S(N²−N)+(T+1)(N²−1)` from (U12)–(U24).
- Cross-references: every (U), (D), (B), (A), (P), (Q), (C), (M), (3.x),
  (4.x) label resolves; "Lemma 2.4 of [9]" matches the 1976 edition;
  "ν = 108 [7]" matches the 1978 table; the front matter and MSC codes
  match the scan. Theorem 4 lists twelve pairs (the sixteen-row table is
  the 1980 announcement's); the twelve overlap entries agree.
- Left as printed: the text before (5) in the proof of Lemma 2.25 lists
  "(B6), (B7), (B9), (4)" although (B5) and (B12) are used too; (13) writes
  `N^N ≤ U^R` in one chain and `N^N < U^R` in the other (the strict form
  holds); reference [13] lacks "pp.", [10] has "pp.49-59", [3] a spaced
  colon, all as in the scan; [5], [6], [20] are uncited in the original.
  The printed qualifier "with ν ≥ 13" omitted by the edition (1982-89) is corroborated:
  §3-type systems keep the `B^((δ+1)^(ν+1))` terms, so only the pairs
  with `ν ≤ 12` can come from §3; the printed "ν ≥ 13" is the wrong way
  round and the omission stands.

### Changes

| id | location (orig.) | class | old | new | reason |
|---|---|---|---|---|---|
| 82-R4-01 | §2, p. 555 (after the definition of χ_A, ψ_A) and p. 556 (proof of Lemma 2.23) | ORIG | "(cf. [23], [24], [15], [4], [18], [8] for proofs)"; "(cf. [23], [24] or [18])" | "[25], [24], …" in both places, with an editorial footnote at the first | [23] is Kummer's 1852 paper on the reciprocity laws (cited correctly for Kummer's theorem on p. 551, "[23], [26]") and contains nothing on Pell equations; [25], Julia Robinson's *Existential definability in arithmetic*, the standard source of these lemmas (cited for them by the 1976 and 1978 articles), is otherwise never cited in the article. The scan prints "[23], [24]" in both places, so this is an error of the printed original, most likely a citation left unrenumbered after [23] was inserted. |
| 82-R4-02 | Theorem 4 heading, p. 552 | CLAR | "The following universal constructions are reported; the large degrees in scientific notation are approximate sizes, not exact integer degree bounds:" | the printed "The following pairs (unknown, degree) are universal:" with a footnote *Editorial clarification: the four degrees in scientific notation are the author's rounded sizes …; they have not been rederived in this edition.* | An earlier rewording in the edition replaced the author's claim without a mark and dropped "(unknown, degree)", the only statement of the tuple order $(\nu,\delta)$. The qualification is kept, now marked. |

---

## 1980 — Undecidable Diophantine Equations

**Status: fully read.** The three theorem systems agree with the 1982
Theorems 1–3 term by term (the 1982 packing check above covers them, and the
checker `verification/corpus_cross_review.py` parses both sources). The sixteen-row table
matches the 1982 Theorem 4 list where the two overlap. No change to the
article source so far.

### The operation count o = 100 and Theorem 5 (2026-09-14)

Satellite article `1980/jones1980_theorem5_operations.tex` (+ `.pdf`), with
the companion program `verification/round4_1980_operation_count.py`
(results in `round4_1980_operation_count.json`) and the table generator
`verification/round4_1980_schedule_table.py`, which writes
`1980/jones1980_theorem5_schedule.tex` from the verified schedule. Until
then the edition recorded 100 as the author's count, not reconstructed.

- **Where 100 comes from.** Counting every `+`, `−` and `×` sign of the
  printed Theorem 3 once, as written, with exponentiation not counted and
  the equation q = b^(5^60) omitted, gives exactly 100 (33 additions, 15
  subtractions, 52 multiplications; 44 exponentiations not counted). The
  per-equation totals are 6, 3, 2, 2, 2, 0, 32, 4, 3, 5, 4, 5, 3, 10, 3, 4,
  12. The same rule gives exactly 87 for the fourteen equations of Theorem
  2.12 of the 1976 paper (the authors' count) and 241 for the 36 equations
  (1.3) of the 1978 paper (author's count 243; the two missing signs were
  not located). No other rule tried (powers as repeated multiplication with
  or without reuse, numeral coefficients free, one operation per power)
  reproduces both 87 and 100. Conclusion: Jones's o is the count of
  indicated operation signs, exponentiation being treated as notation, and
  "modified to do away with q = b^(5^60)" means the exponential equation is
  set aside, not that its polynomial replacement was counted. Recorded
  inconsistency: the 1978 remark "would increase this number to 350"
  charges one squaring per equation (350 − 243 = 36 + 36 + 35).
- **Explicit certificate under the strict convention** (calculator with +
  and × only, any auxiliary integers supplied for free, intermediates
  reused, every power by repeated multiplication, subtraction checked as an
  addition). The exponential equation is replaced, by Lemma 2.26 of the 1982
  paper with B = b, Q = q, B₁ = 5^60, by c = 2r+1+κ+φ and
  μ = q + κ(a−b) + ρ(2ab−b²−1), (a²−1)κ²+1 = μ², κ = 5^60 + Δ(a−1)
  (four new unknowns κ, μ, ρ, Δ; the exponent is a numeral). The article
  proves that the modified 20-equation system in 32 unknowns still defines
  x ∈ W_⟨z,u,y⟩ (hypotheses 3·5^60 ≤ b from b > xy ≥ y ≥ 2^(5^59), b < q
  from (E2), q ≤ n ≤ r; positivity of ρ and Δ; re-choice of φ by (14) of
  Lemma 2.26). A straight-line certificate of **129 operations** (75
  multiplications, 37 additions, 17 subtractions) verifies all twenty
  equations; SymPy checks every residual against the source polynomials.
  Generating the numerals 2, 4, 5 and 5^60 from 1 costs 10 more (139).
  Economies: shared q², q³, q⁴, q⁸, q¹⁶ and b², b⁴, b⁵; Horner form of the
  first bracket of (E7) avoiding q⁵ and q⁷; shared wn², sn², rsn² with
  p = 2(wn²)(rsn²)²; (p²−1)k²+1; r+1+h(p−1); bw+c(a−2)+γ(4a−5);
  (a²−1)(ic²)²+1; modulus 2ab−b²−1 = (a²−1)−(a−b)². The printed system
  with (E0) merely deleted needs 127 under this convention even with full
  sharing, so 100 is not attainable as a strict count of Theorem 3;
  optimality of 129 is not claimed.
- **Theorem 5** is proved in certificate form: for an effectively
  axiomatizable T with Thm_T = W_⟨z,u,y⟩, P is provable iff the modified
  system is solvable iff a valid 129-instruction certificate exists; the
  seventeen polynomial equations it verifies carry the 100 indicated
  operations. The article states what is not claimed (integer sizes, bit
  cost, search, proof length).
- **How the count arose.** The article's §7 collects the authors' own
  words: 1978 defines o as "the number of operations (additions and
  multiplications), necessary to write the system" and calls it "very
  closely associated with the number of symbols necessary to write down
  the equation"; 1976 says the 87 "is easily calculated from the equations
  of Theorem 2.12"; 1982 says "it can be seen that o = 100". So o was a
  typographical size measure, inherited from 1976 (where sign count and
  straight-line count coincide), and the proof-theoretic corollary was
  attached to it afterwards. The 350 remark (one squaring charged per
  transposed equation) shows the exponent-free rule was not a considered
  position.
- **80-R4-01 (EDN), original pagination marks.** The corrected source now
  carries margin numbers [859]–[862] (`\origpage{n}`, via `marginnote`) on
  the lines where the pages of the Bulletin printing begin, checked against
  the scan: p. 860 begins inside "The existence of such a universal
  polynomial", p. 861 inside "one exponential function appear", p. 862 at
  "A different measure of size". Line accuracy only; no inline break mark.
  The two forced `\newpage`s of the edition (before Theorem 1 and before
  Theorem 3) are kept for layout, with comments saying they are not the
  original breaks. The edition notice mentions the marks.
- **80-R4-02 (EDN, 2026-09-24), pointers to earlier notes.** The index
  convention before Theorem 1 said that the coefficient convention is
  recorded in earlier editorial notes, and the note under Theorem 4 cited
  the same notes for a distinction concerning evaluation; those notes are
  not part of this project. Both now name the
  editorial notes with their entries (1980-08, 1980-18 of
  `1980/jones1980_editorial_notes.md`), which reproduce that content.
  The satellite article's reference to the 1976 certificate
  now names `Papers/verification/jones1976_primality87.md`.
- The footnotes to Theorem 5 in `1980/jones1980_corrected.tex` and
  `1982/jones1982_corrected.tex` ("not independently reconstructed") were
  reworded on 2026-09-14 together with the edition notices; see the item
  on edition notices in the corpus-wide section.

### Lean formalization of the announcement (2026-09-14)

`Lean/Diophantine/Paper1980/` was started under the relaxed axiom policy
stated by the project owner for this article (well-known theorems proved
before 1980 and obvious common-sense facts may be axioms); no axiom was
needed. Theorems 1–3 are not restated: they are `Jones1982.theorem_1`,
`theorem_2`, `theorem_3` with `ν = 58`, and those docstrings now record
the double appearance (the transcription check that the two printed
systems agree term by term is `verification/corpus_cross_review.py`). New:
`Jones1980.indexCode_injective` proves the editorial footnote after
Theorem 1 that `v = ((zuy)²+u)²+y` is injective on positive triples (two
applications of "a square plus a remainder at most twice the root
determines both"; the remainders `y` and `u` are at most `zuy ≤ (zuy)²`).
`Jones1980.theorem_5` formalizes Theorem 5 in the edition's certificate
reading: for every recursively enumerable `S ⊆ ℕ` (Mathlib's `REPred`,
standing for the Gödel numbers of the theorems of an effectively
axiomatizable theory) there are a normalized quartic in 58 witnesses and
an index `⟨z,u,y⟩` such that, for every positive `x`, `x ∈ S` iff the
eighteen equations of Theorem 3 have a solution in positive integers. The
count 100 is a statement about the printed syntax and is not part of the
Lean statement. Row `(58, 4)` of Theorem 4 is `Jones1982.universal_quartic58`;
the other fifteen rows are reported constructions and are not formalized.
Status table in `Lean/STATUS.md`.

### Agreed 1980 formalization scope and index reduction (2026-09-14)

**80-R4-SCOPE (EDN).** The project owner's completion criterion is now
Theorems 1–3 together with an **abridged Theorem 4 containing only the
proved universal pair `(58, 4)`**. The other fifteen reported pairs are
excluded for now, and Theorem 5 is intentionally excluded. This records
the scope of the formalization; the historical statements and their
editorial discussion remain in the edition. The earlier axiom allowance
described above is superseded: **no new axioms may be introduced**. No
project mathematical axiom was introduced under the earlier allowance.
The [1980 formalization audit](../Lean/PAPER1980_AUDIT.md) records the
retained statements, proof contracts, exclusions, and validation receipts.

The retained Lean contracts preserve positive inputs, admissible positive
coding triples, and the positive witnesses of the printed systems. The
quartic representation uses natural witnesses obtained by shifting the
positive quadratic witnesses; its degree bound includes the input and
58 witnesses after the three index parameters have been fixed. Thus the
joint polynomial's degree in the index parameters is not being asserted
to be at most four.

The newly proved
`Jones1980.rePred_single_parameter_systems` in
[SingleParameter.lean](../Lean/Diophantine/Paper1980/SingleParameter.lean)
adjoins the literal equation `indexCode z u y = v`. Injectivity of the code
on positive triples lets one positive `v` serve all positive inputs while
`z`, `u`, and `y` become three additional positive witnesses: the counts
are 15, 17, and 31 for the three systems. This establishes the stated
existential index reduction, without an additional decoder or effective
enumeration claim. No new article error was found in this audit, and no
article formula was changed by this scope note. Final integration
validation is recorded separately in the audit and Lean status.

### Lean formalization of the alternative universal systems (2026-09-15)

Following the owner's request to formalize the alternative Turing-complete
systems explored under `1980/` (excluding the standalone MRDP extraction), the shared machinery of
both routes and the whole tag route are now in Lean.

*Shared*: the base-three Pell kernel of `1980/EXPLORATION_UNIT_TWO_TERNARY_KERNEL.md`
(soundness at `D₀ ≥ 81, r ≥ 27, r < 2D₀`, giving `U = 3^(2r+1)`, `D₀` a power of
three and `D₀ ∣ C(2r,r)`; and the positive converse for even `r`) in
`Lean/Diophantine/Paper1980/Kernel3.lean`, together with the unit-two ternary
mask via Kummer's theorem (`TernaryMask.lean`). The ratio block is the
90-operation one with `A = a + 3`; the exponent decoding uses the direct
congruence `T_j ≡ 3^j (mod 6a + 8)` rather than the cubic criterion, since the
kernel's scale `U ≥ 81` is too small for the latter.

*Transcriptions*: `System100.lean` (22 equations, 34 unknowns, parametric in the
compiled ROM constants) and `System91.lean` (18 equations, 29 unknowns,
parametric in the tag constants), each checked field by field against its
receipt by `verification/lean_sys100_transcription_check.py` (22/22) and
`verification/lean_sys91_transcription_check.py` (18/18 in both leading
branches). Both reach the kernel from positivity alone (`Bootstrap100.lean`,
`Bootstrap91.lean`).

*The counter route*: the radix geometry (`Geometry100.lean`), the pre-typing
bounds of §2 (`Bounds100.lean`), the twelve doubled fields (`Fields100.lean`),
the leading-trit toolkit of §4 (`LeadingTrit.lean`), the three borrow
exclusions of §§3–4 (`Borrow100.lean`), the carry descent that joins them
(`Carry100.lean`), the guard estimate of §5 (`Guard100.lean`), the conditions
the compiled program already supplies (`Compiled100.lean`), the compiled
controller and its ROM (`Controller100.lean`), the rows of the state word
(`Rows100.lean`), the row transport (`Transport100.lean`) and the fixed grid
(`Grid100.lean`).

The descent runs all twelve levels of §3 and settles every carry; §5's guard
estimate supplies the two remaining nonnegativity statements; and the layout
conditions on the fixed table turn out to be consequences of the fixed grid
inequalities, or, for the route residue, of the cyclic route read modulo the
state modulus.  The upshot, `decode_controller100`, is that every solution over
a compiled controller has all twelve conceptual fields equal to twice a Boolean
ternary word, on one remaining input.

Beyond the note's own text, the ROM machinery it cites is proved directly: the
coordinates are a Sidon set, the table is a Boolean ternary numeral, and the
projection reads a selected state's successor, marker and two labels.  The
transport carries that reading along the rows, and the fixed grid's width
equation is identified as the grid word with the threshold's position deleted.

The fixed ROM and count-marker argument that §5 hands to the 101 and 102
predecessors is now proved directly (`OneHot100.lean`), and `Decode100.lean`
supplies its hypotheses from the twelve fields, so `decoded_controller100`
recovers the controller path itself: row `i` of the halved state field is the
single state `f^[i] 0`.  This needed one more property of the compiled program,
recorded as `ROM100.Grid`: the on-grid word marks the target columns and both
port columns, and only grid positions.  Two corrections to earlier drafts of
this entry: the junk pair *does* give the target-column exclusion, once the
on-grid word is read as a Boolean grid word rather than a single power; and the
merged-program note's single-power threshold is a choice specific to that
counterexample.

The decoded-control bound `2q ≤ R D` is now proved too (`decode_bound100`).
The path decoding never reads the guard pairs, so it runs without the bound;
the last row's successor is then forced to be the cyclic entry by the
next-state word's wraparound row, and the compiler's convention that every
predecessor of the entry carries the no-zero-request label sets the zero
field's top row.  The bound was previously the one unproved input of the
twelve-field decoding.

The grid layout is also shown non-vacuous (`GridCompiled100.lean`): with
spacing nine and odd port offsets, a numeral marking the target columns, the
port columns and one high column meets both the fixed grid inequalities and the
grid layout.  `decoded_compiled100` therefore decodes the controller path of
every positive solution over a compiled controller's own ROM, assuming only the
terminal convention and odd port offsets, both choices of the compiler.

**Correction to the three paragraphs above.**  The controller formalized in
`Controller100.lean` through `GridCompiled100.lean` has a single successor
function.  It is therefore the *deterministic* router of
`EXPLORATION_FIXED_PROGRAM_ROUTING.md`, and "the fixed ROM and count-marker
argument that §5 cites" overstated it: no count marker is needed there, and
the grid layout's requirement that the junk avoid the target columns is the
deterministic router's junk test.  The counter note's ROM is the
*nondeterministic* router of `EXPLORATION_NONDETERMINISTIC_PROGRAM_ROUTING.md`,
which keeps every permitted edge in the table, lets unchosen edges remain as
junk in target columns, and uses a column-count marker to force one state per
row.  Branching is essential for universality, since a deterministic controller
cannot branch on a zero test.  The deterministic results stand as proved
theorems, and the counter history does not depend on determinism, but reaching
universality requires the nondeterministic router.

**The nondeterministic router, formalized.**  `Graph100.lean` through
`GraphHistory100.lean` now prove the counter note's §5 for its own ROM.  A graph
controller's table carries every permitted edge; the count marker counts the
states selected in a row (`count_marker`); and `Graph.path_run` recovers a path
of permitted edges from the route with the junk allowed in target columns,
needing it to vanish only inside the marker block, which lies off the spacing
grid.  `graph_decoded_compiled100` builds a grid numeral meeting `ROM100.Ok` and
the port-grid layout for every graph controller, and `graph_serial_run100`
reads every positive solution over that ROM as an accepting run of the serial
labelled-counter relation of `EXPLORATION_SERIAL_RAW_COUNTER_COMPOSITION.md`
§1.  One convention differs from that note: the run is cyclic (the last state
has an edge back to the entry) rather than ending at a separate final state,
matching the 100-operation system's `I`-only route; and the compiler's terminal
convention, that every predecessor of the entry carries the no-zero-request
label, is what makes the zero field's top row set.  No error was found in the
note's argument.

**Both directions for three-counter programs.**  `CounterProgram100.lean`
through `CounterIff100.lean` formalize §§4–6 of
`EXPLORATION_THREE_RAW_COUNTER_UNIVERSAL_COMPILER.md` and the positive
converse of the counter note's §6: for every three-counter program and every
positive input, the program accepts exactly when `Sys100` over its compiled ROM
has a positive solution (`accepts_iff_solvable100`, axioms `propext`,
`Classical.choice`, `Quot.sound` only).  Two conventions of the Lean compiler
differ from the note's text, neither affecting the operation count: the run is
cyclic, so the halt's last lane leads back to the entry, and the halt bank
requests zero tests on all three registers, so accepting computations end with
empty registers without a separate cleanup being visible to the graph.  The
parity the kernel's index needs comes from the layout (six blocks per
instruction plus a six-block prefix), and the positivity of both track words
from splitting the even input block so that each half gets a nonzero digit.
The input loader and the two-stack simulation of §§1–3 are now proved too
(`TuringStack100.lean`, `TuringCounter100.lean`, `TuringSim100.lean`), against
Mathlib's `TM0` machines; the "choose a Turing machine" step is assembled from
Mathlib's verified `ToPartrec`, `TM2to1` and `TM1to0` compilers
(`TuringPartrec100.lean`), whose input tape carries one marker cell before the
binary digits, so the simulating program pushes that fixed prefix after loading.
`universal100_re` states the result: for every recursively enumerable set there
is a fixed ROM such that the 100-operation system has a positive solution at
`x > 0` exactly when `x` is in the set.  No new axiom is used.  The
alternative 100-operation architecture is therefore formally universal; it
does not improve the established 90-operation bound.

Two things are left, and both are the note's own boundary.  The bound
`2q ≤ R D` says the reconstructed zero-request word is positive; the note calls
it a conclusion of decoded control and states plainly that it was not used in
§§2–4.  And §5 obtains the decoded controller itself by handing its four
support hypotheses to the fixed ROM and count-marker argument of the published
101 and 102 predecessors, rather than reproving it; reaching universality means
formalizing that separate chain.  No error was found in the note.  One
strengthening was needed that the note does not state: the two port heights are
carried as controller fields, because the note asks only that the ports sit
above all state coordinates, while its own conclusion that all table exponents
are distinct needs them higher.

*The tag route, both directions*: `sound91` (a positive solution halts the actual
tag machine) and `witness91` (an accepting computation halting at the
single-symbol word `0` gives a solution), combined in `tag_equiv91`. The
decoding chain is the notes': radix geometry, the nine Boolean fields by greedy
base-`q` chunking, the row projector, the length path and the signed content
rows with their first-discrepancy argument. Only the standard axioms are used.

Two points the formalization had to make explicit. The content transport is
read row by row through an invariant that carries the *actual* content of the
queue, so the identification of a row is what licenses the next step; and the
converse needs the index parity as a hypothesis, which the notes discharge by
choosing between the canonical and the zero-edge-padded history. That padding
is not yet formalized, so `witness91` takes the parity as an explicit
hypothesis, stated cleanly as `2 ∣ (Σ_{i<t} nᵢ) + m t`. No error was found in
the notes.

*The tag route, completed (2026-09-16)*. The padding is now formalized
(`witness91_gen`, `TagPad91.lean`), and `tag_iff91` (`TagEquiv91.lean`) gives
both directions on the notes' completeness domain with no run-specific
hypotheses: for `β ≥ 2`, `a ≥ 2`, `β ≤ |W₀|`, `K²Lᵢ < C` and the first-zero,
positive-startup and single-zero-terminal promises, the certificate is
solvable at the encoded input exactly when the tag system halts. The width
is chosen odd, the startup coordinates are positive by the promises, and an
odd canonical index is flipped by the wrapped zero-edge padding.

The notes cite Neary (STACS 2015) for the universality of binary tag systems
`0 → 0`, `1 → u`; under the no-new-axioms policy this is proved rather than
assumed, by a chain of simulations: Turing machine → three-counter program
(the 100-operation route) → single-register machine on `2^a 3^b 5^c`
(`TagGoedel91.lean`) → a tag system with deletion 30 whose division rounds
detect residues by phase shifts (`TagRound91.lean`, over the chunkwise
reading lemma of `TagRead91.lean`) → a binary track system in the spirit of
Neary's Lemma 9 (`TagBinary91.lean`). The binary construction is not Neary's
verbatim: letters are `0^{2(x+1)} u 0^{L−2(x+1)}` among garbage copies of
`u`, and halting is arranged by an all-zero track for the halting letter,
which flips the parity of every later reading phase so that every `u` then
emits zeros and the queue decays to a single `0`; `s` even with
`s ≡ 1 (mod β − 1)` and a padded initial length make that final word exactly
`0`, and the first-zero and positive-startup promises hold by construction.
`tag91_re` (`TagUniversal91.lean`) is the universality statement: for every
recursively enumerable `S` a binary tag system with fixed `k, Ut, ε, B, cc`
such that `x ∈ S` exactly when the 18 equations are solvable at
`(content W_x, 3^|W_x|)` with `C_x = 3^γ_x`; `tag91_undecidable`
(`TagDecide91.lean`) adds that `x ↦ (γ_x, content W_x, 3^|W_x|)` is primitive
recursive and that solvability over the family is not computable. Only the
standard axioms are used.

One point the notes leave implicit: the admitted domain `K²Lᵢ < C` forces
`C` to grow with the input, so in the encoded family `C` and `j` vary with
`x` (computably) while the other tag constants stay fixed.

### Lean formalization of the 90-operation system (2026-09-15)

Following the owner's request to formalize the current best certificate,
the 90-operation system (`1980/BINARY_PRODUCT_90_PROOF.md`,
`1980/BASE_TWO_PELL_90_PROOF.md`) is now proved universal in Lean:
`Jones1980.universal90` and `universal90_re` in
`Lean/Diophantine/Paper1980/Universal90.lean` (all `*90*` modules; axioms
`propext`, `Classical.choice`, `Quot.sound` only). The transcription
`Sys90` is checked against `round37_1980_binary_product_certificate.json`
by `verification/lean_sys90_transcription_check.py` (22/22). The
formalization follows the two notes: the base-two Pell block with the
exact binomial tail (`2 Σ_{m<r} C(2r,m) + C(2r,r) = 4^r`, so the fractional
part is below `1/4` once `U = 2^{2r+1}`), the half-parameter index fixing
through the odd-index polynomial `Q_h` with `χ_X(2h+1) = X·Q_h(X²)`, the
binary compiler with base-seven weights, two reserved helper groups, seed
and reverse rows, helper complements at every negative position, resets
four positions below each tested start, the padding `2xX`, and the two
binary unit tests. One point the formalization had to make explicit: a seed
row (negative `x²`) must carry no other monomial, since a helper pair of a
seed has degree two and could otherwise coincide with a base term of the
same row; the compiler's seeds satisfy this. No error was found in the
notes.

### Lean formalization of the straight-line certificate (2026-09-14)

Goal set by the project owner: formalize the encodings of the reduced
certificate and prove that they yield a universal Diophantine equation.
The system targeted is the 93-operation one
(`AFFINE_RADIX_95_PROOF.md` with the 94/93 refinements). **Completed**
(`Lean/Diophantine/Paper1980/*93*.lean`, `PellRelaxed*.lean`,
`CodeDigits.lean`, `MaskDigits.lean`, all without project axioms;
`Jones1980.universal93` and `universal93_re` in `Universal93.lean`): for
every Diophantine (equivalently recursively enumerable) set `S` there is
a fixed index `(V, H, Tindex)` such that, for every positive `x`,
`x ∈ S` if and only if the 22 equations `Sys93` have a solution in
positive integers. The transcription `Sys93` is checked against the
receipt by `verification/lean_sys93_transcription_check.py`.

The sufficiency direction follows Sections 3–6 of the note: the
bootstrap bounds, the Pell block (relaxed auxiliary norm, doubled index,
ratio and exponent decodings), the three masks as an equivalence with
`n² ∣ C(2r,r)`, the canonical code (1982 Lemma 2.9), the digit reading of
`g`, the polynomial coefficient isolation of `D(T)C(T)²` (exponents in
three residue classes modulo six, bands `d₀` apart, dummies excluded), the
three-digit windows with the reset and padding carries, the unit tests
forcing `δ = 1`, and the decoding of the compiled circuit. The necessity
direction follows Section 7: three-way splits with the forbidden bit
clear, a power-of-two radix `B ≥ 2H₀` exceeding every digit and `7x²`,
the canonical codes, the three masks proved digit by digit, and the Pell
witnesses with `Y = ⌊(U+1)^{2r}/U^r⌋` and the relaxed `i = (A² − 1)·i_old`.

Points recorded for the notes while formalizing.

- The circuit compilation used in Lean differs slightly from Section 1:
  every circuit coordinate gets three groups of three physical
  coordinates (`P, Q, R`, with copy rows `Q = P`, `R = P`) so that every
  product has distinct factors without per-row fresh copies; `X` is the
  input's own group `P_inp` (with the normalization row `P_inp² = x²`),
  and `δ'`, unlike the note, is a single physical coordinate. The
  paired-row and unit-row layout, the padding sets `P₅ = P_inp ∪ Y`,
  `P₇ = P₅ ∪ Z`, and the decoding are as in the note.
- The bound (12) is used in the form `128 D₁ (m+1)² < B`, where `D₁ =
  Σ_h |[T^h]D|` and `m` counts the physical coordinates; the dummy digits
  do not enter the coefficient bound because the coefficients below
  `t_{s−1} + 2` are those of `D · C_main²`.
- `L` need not be a power of two; `L = 3K + 3` is used. `H₀` is chosen as
  the power of two `2^{j_H}` with `j_H ≥ 4L + 3`, `128 D₁ (m+1)²`,
  `3L + 3` and `10`.
- The relaxed-norm proof's step `gcd(c², T ψ_F(ep)) = c·gcd(c, D)` is not
  needed; the weaker `c ∣ T h` (hence `c ≤ D h`) suffices for the
  contradiction `2c < A D² < c`, and that is what the Lean proof uses.
- The ratio upper bound `c/k < ξ + 1/2` is proved from `ξ < Y + 1`
  (`upper_estimate'`), which is what the necessity direction needs; the
  interval equations then give the same bound in the sufficiency
  direction.

The certificate was reduced to 92, 91 and 90 operations and further
while this was being written; the version-independent
parts carry over, as recorded in `Lean/STATUS.md`.

### Second reading of the edition and of the satellite article (2026-09-14)

An independent line-by-line reading of `jones1980_corrected.tex` against
the OCR and of the satellite documents (`jones1980_theorem5_operations.tex`
with its input sections, the generated schedule tables, and the
`*_PROOF.md` notes) against the JSON receipts, with SymPy checks of the
algebraic claims. The edition itself needed no change: every difference
from the OCR is a documented item of `1980/jones1980_editorial_notes.md`; the unknown lists (12, 14, 28),
the variable inventory of Theorem 3, the citation numbers, the sixteen-row
table (against the twelve rows of the 1982 Theorem 4) and
`D₉ = 47216·5^58 + 9728` were re-verified. The satellite documents had one
gap in a proof and two count slips, all now repaired:

- **80-R4-S1 (satellite, proof gap; corrected).** The proof of the
  theorem "x ∈ W iff Σ is solvable" (`thm:sigma`, the modified system with
  (E0) replaced by (E18)–(E20)) established the hypothesis `n ≤ r` of
  Lemma 2.26 from `S ≥ g ≥ 1`, citing the block bounds `0 ≤ S_i, T_i` of
  the 1982 §4. That derivation of `0 ≤ S₃` uses `xb⁵ ≤ q`, which the 1982
  paper obtains from `q = B^(5^59)`, i.e. from the very equation (E0) that
  Σ omits (the Lean lemma `UEqs.S3_nonneg` likewise uses (U3)); so the
  sufficiency argument was circular as written. Without (E0), (E1)–(E2)
  give only `q > b^(4.5)`, and solutions of (E2) with `b < q < b⁵` exist
  (`q⁴ ≡ 1 (mod b⁵−1)` has such roots for composite `b⁵−1`), so the bound
  cannot be recovered from those two equations. Repair, now in the text:
  (E7) factors as `r = (n−1)(Sn + (T+1)(n+1))`; since `r ≥ 1`, the second
  factor is a positive integer, and it equals 1 only if `n | T`; but
  `0 < T < n` follows from `e ≥ y + θ ≥ b⁵` (E3, E5, `m ≥ 1`, `y ≥ 2z`),
  hence `ℓ < q²` by (E1), `T > q³ − ℓ(b−1) > 0`, and `θλ < q⁴`, hence
  `T < q³ + q⁷ + b⁵q⁸ < q¹⁶ = n`. Therefore `r ≥ 2(n−1) ≥ n`, which also
  supplies `r ≥ 8` and `r > b` for Lemma 2.25 without (E0). The later
  systems of the optimization sections were not affected: they split the
  inequality (E1) into `eℓg² < q²` and `xy < b`, and `e, ℓ ≥ B` then gives
  `q > B` directly (the sentence saying so now shows the intermediate step
  `q² > eℓg² ≥ B²`). The sentence introducing the size checks now says
  that the 1982 bounds on `r` are the ones that use (E0). The script
  `verification/round4_1980_sigma_size_check.py` records the evidence:
  (E2) has solutions with `b < q < b⁵` for every `b ≤ 12` (e.g. `b = 4`,
  `q = 32`; `b = 6`, `q = 6532`), the factorization of (E7), the
  characterization "second factor = 1 iff `n | T`", and `0 < T < q¹⁶` on
  2000 random instances of the inequalities the repaired proof uses.
- **80-R4-S2 (satellite, TYPO).** "five occurrences of `b⁵`" → six
  ((E2), (E3) and four in (E7)); the total of 44 exponentiations was
  right.
- **80-R4-S3 (satellite, TYPO).** In the breakdown of the 32 signs of
  (E7) the contributions summed to 31; the join `+` before
  `2(e−zλ)(1+xb⁵+g)⁴` was missing (7 → 8). The per-equation vector and
  the total 100 in the companion receipt were right.
- **80-R4-S4 (optimization section, CLAR).** The list of companion
  programs for the 123-instruction theorem included
  `round4_1980_recoded_certificate.py`, whose own receipt records the 126
  instructions of the recoding alone; a sentence now says where the 123
  count lives (`recoded_system_123` in the optimized checker's receipt).
- Recorded, not changed: the symbol `M` is used in the optimization
  section for `rsn²`, then for `5^58`, and in the Pell section for `RY`;
  the generated schedule tables keep legacy intermediate names (`lq2`,
  `xb5`, `q4p1`, `S3q4`, `Sq3`, `Tq3`, `b5m2q8`, `b5m2`) whose values
  changed in later schedules (`ℓq`, `xB`, `q²+1`, …), which the checker
  does not mind but a reader may; and the running counts in this file
  stop at 114/123 while the two 113-instruction variants are recorded
  only in `QUADRATIC_MASK_PROOF.md` and `PELL_SHIFTED_BASE_PROOF.md`
  and their receipts (62 mult + 51 add, 33 unknowns, 21 tests, 120 with
  numerals; 63 mult + 50 add, 32 unknowns, 20 tests, 122 with numerals).
  These belong to the concurrently edited optimization work.
- Checks that found nothing: every count quoted in the satellite
  documents against the receipts (129, 128, 127, 126, 123, 120, 119, 118,
  117, 114 and the numeral chains 139/131/123); the eight replaced
  instructions of Theorem 4.6; the addition chains for `5^60` and `5^64`;
  `log₂(3·5^60) < 141`; the algebraic identities (the triangular (E7) and
  (E17) corrections, `G−1 = (f²−1)(f²−a+1)`, `G = 1+(a+1)(f²−1) ≡ 1 (mod c)`,
  `2ab−b²−1 = (a²−1)−(a−b)²`, the Lemma 2.25 dictionary); the Pell
  congruences for `A ≤ 8`; the bounds in the `*_PROOF.md` notes
  (`a ≥ 20r`, `A > RU^R`, the 3/65 error, the short-mask digit bounds,
  the 1830 Sidon weights of the quadratic mask); the quotations from the
  1976, 1978, 1980 and 1982 papers (verbatim, pages correct); and all
  `\ref`/`\cite`/`\input` targets.

---

## 1978 — Three Universal Representations of Recursively Enumerable Sets

**Status: fully read; the 36-equation system (1.3) re-derived from the
section-3 construction and matched symbolically; section-2 lemmas checked;
one BUILD change. No mathematical change required.**

### Checks performed (`verification/round4_1978_checks.py`)

- Lemmas 2.1, 2.2 (relation-combining), 2.5 (binomial congruence) and 2.6
  (partial binomial expansion) verified by brute force on small ranges.
- The Cantor pairing J is a bijection with K(y), L(y) ≤ y; the recursive
  enumeration P_k of §3 satisfies "X_i occurs in P_k only if 3i+2 ≤ k",
  has no constant term, and P_0 = P_1 = 0 (k ≤ 59).
- **System (1.3):** all 36 equations were re-typed from the edition and
  compared, one by one, with U1–U8, B1–B8, T1–T9 (with the stated variants
  5(C−KLY)² ≤ K²L² and M = 9NXY) and Q2–Q4 under the letter substitutions
  listed at the end of §3 (A→a, …, Z→z, b_i→f'…j', c_i→k'…p', d_i→q'…u',
  J = Z⁶, U7 taken modulo q). Every equation agrees exactly. The system has
  67 unknowns (n and x are parameters) and maximum degree 38, attained by
  (1.3.09) (16 + 20 + 1 + 1); (1.3.06) has degree 26.
- **Combined divisibility (end of §3):** the edition's form (1978-51)
  F·M(u)² | M(u)²(H−C) + F(hM(v)−x)² is equivalent to F | H−C and
  M(u) | hM(v)−x whenever gcd(F, M(u)) = 1 (which A3 with e₀ = M(u)
  guarantees), because a² | b² ⟺ a | b. The printed form with M(u)(H−C) is
  not: for M(u)=2, F=3, H−C=−3, hM(v)−x=−8 both conditions hold but
  2·(−3)+3·64 = 186 is not divisible by 12. The correction stands.
- Hand-checked: the BQT proof (Lemma 2.3), including the pairwise
  coprimality of the factors of (4) and estimate (3); Lemma 2.7's chains
  (9), (10) and the coprimality (N−r, z!) = 1; Lemma 3.5's estimate
  |A(y)B(y)C(y)| < Z⁹⁰ (a rough bound gives about Z⁸⁶) and the inequality
  chain ending in J^(J−2); the derivation of 3 ≤ R from U2–U4 (R = 0 is
  impossible because U3 and U4 then contradict each other, so θ ≥ 1); and
  the least-residue arguments behind A(y), B(y) for every β ≥ 2.
- Theorem 2 is the literal translation of Theorem 1 by the three stated
  principles; the shared witness e is used in disjoint cases, so no clash.
- Lemma 2.8 (Matiyasevich–Robinson partial-binomial conditions T0–T9),
  necessity direction, checked on six instances (N, Z, X) up to
  (5, 3, 600): with K = ψ_M(N−Z+1), L = ψ_MX(Z+1), C = ψ_A(N+1) the
  inequality T3 holds, and the variant 5(C−KLY)² ≤ K²L² with M = 9NXY holds
  whenever its hypotheses 8N^Z < X and Y > 1 do.

### Comparison with the OCR of the scan

- The Bhagavad-Gītā epigraph is chapter 11, verse 7 (correct).
- "Received December 8, 1975; revised August 30, 1976" is as printed.
- U8 uses the factor (T₁+g−r) in the original too; the BQT's z₁ is g here.

### Second full reading (2026-09-14)

An independent reading of all 17 pages against the scan (p. 337 rendered at
400 dpi for the sign-by-sign comparison of (1.3)), the discrepancy
register of the edition (now `1978/jones1978_editorial_notes.md`) and this
file. No mathematical error, no
wrong emendation; the typographical items 78-R4-02 … 78-R4-08 below.
Checks that found nothing:

- The 36 equations of (1.3) against the scan sign by sign, and derived by
  hand from U1–U8, B1–B8, T1–T9 (with the `5(C−KLY)² ≤ K²L²`, `M = 9NXY`
  variants) and Q2–Q4 under the stated letter map; the roles of ρ, γ, ι,
  φ, ϕ, ψ, δ, ε, ν, υ, a′–e′, τ; 67 unknowns; degrees 38 for (1.3.09),
  26 for (1.3.06), 12 for (1.3.36); sum of squares 76. The scan prints the
  B-factor modulus of (1.3.09) as `(1+β+βr)²`, the edition `(1+β+rβ)²`
  (identical polynomials; on record only).
- Theorem 1 ⇔ (3.3) ⇔ the residue coding, including `i = 0`, `i = n`,
  the overlapping cases `j = s = w`, and `a = 0` or `b = 0`; Theorem 2 from
  Theorem 1 by the three combining principles.
- Lemmas 2.1, 2.2 (both directions), the Divisor Lemma (`s = 0`), the
  Bounded Quantifier Theorem in both directions (the factorization (4),
  pairwise coprimality, (5)–(7), the filler `z_{y,1} = y−τ`, `τ = 0`),
  Lemma 2.4 numerically (least `r` for `J = 2..6` is 2, 20, 244, 4060,
  87814 against the bound 2, 5, 19, 129, 1301) and its converse via the
  period of `ψ_{J+1}` mod `Jz`, Lemmas 2.5–2.7 (both directions of 2.7,
  with the `d_i` choice (12) and the modulus `(N−z_i)/(N−z_i, z!) = σ+d_i`),
  Lemmas 2.9/2.10 (`e₀ ⊥ F`, `Q3 = P3+P4`, `Q4 = P1+P5–P7`).
- §3: `J` bijective; `P_k` well founded; the `W_{i,j}` order; `M(i)`
  pairwise coprime when `τ! | β`; Lemma 3.2's induction; U2–U4 ⇔ the
  residue conditions with the nonnegativity of ρ, h, φ, ϕ, γ; `A(y)`,
  `B(y)`, `C(y)` disjoint mod 3; Lemma 3.4 both directions; Lemma 3.5
  (`2 ≤ β`, `3 ≤ R`, `Z ≥ 30`, `|ABC| ≪ Z^90`, the displayed chain, the
  `g`-shift of 1978-48, the squared combined divisibility of 1978-51, the
  34 → 40 unknown count, the `n = 5` example of 1978-40).
- Citations, tags (1)–(14), (D), (A), (U0), (3.2)–(3.4), (1.1)–(1.2);
  the sixteen universal pairs; the 27 references; the epigraph's
  Devanagari and IAST; footnote numbering. The sign count of (1.3) is 241
  with numeral coefficients counted as multiplications and 224 with them
  free, reproducing the finding recorded in the 1980 section. Uncited [6],
  [15], [18], [19], [22] are uncited in the original too.

### Changes

| id | location | class | old | new | reason |
|---|---|---|---|---|---|
| 78-R4-02 | §1 p. 338 (twice), p. 339, §3 p. 347, p. 349 (twice) | OCR | `2 , is`, `9 . Yuri`, `9 . It`, `AB=0$ , $A=0`, `2 .`, `38 .` | space before the punctuation removed | Mathpix artefacts; the scan has none. |
| 78-R4-03 | §1 p. 335, p. 336; §3 p. 347, p. 349 | TYPO | `"focused"`; `" $\wedge$ " (and), " $\vee$ " (or) and " $\longrightarrow$ "`; `" $<n$ "`, `" $<u+v$ "`, `" $j=s$ "`, `" $R$ "`, `" $\beta$ "`, `" $a$ "`, `" $b$ "` | ``…'' without the inner spaces | With fontspec the ASCII `"` set as a straight quote and the padding spaces were printed; the scan has “∧” (and), “j = s”, etc. |
| 78-R4-04 | nine lines of §2–§3 | BUILD | a lone `\` at the end of the line (remnant of the OCR's `\\`) | removed | Dead markup (a control space at a line end); no change to the output. |
| 78-R4-05 | §1, p. 336 | TYPO | `$\exists^{2} \forall \exists^{4} \forall{ }^{2} \exists{ }^{2}$` | `$\exists^{2}\forall\exists^{4}\forall^{2}\exists^{2}$` | Same prefix as on the previous page, which had been cleaned of the OCR's empty groups. |
| 78-R4-06 | §2–§3, thirteen ranges | TYPO | `B0-B8`, `T1-T9`, `A1-A7`, `(i)-(iv)`, `Lemmas 2.3-2.10`, … | en dashes | The edition already used `Q1--Q4`, `A1--A7` on p. 348; one convention (cf. 76-R4-10). |
| 78-R4-07 | §3, p. 349, collected system | CLAR | "with $z_1,\cdots,z_5$ replaced by $b,e,g,s,w$ respectively," | adds "(Lemma 2.3 singles out $z_1$ in its condition (i) only by the choice of names; in U8 that factor is carried by $g$)" | Read literally the printed sentence makes `z₁ = b`, whereas U8 and (1.3.09) carry the factor `(T₁+g−r)`, i.e. `z₁ = g`, as the edition's proof completion also assumes. Harmless (the theorem is symmetric in the `z_i`), now said. |
| 78-R4-08 | reference [12], p. 351 | BIB | "Acta Arithmetica (in press in the original bibliography)." | "Acta Arithmetica (in press)." with an editorial note giving the published data, Acta Arith. 35 (1979), 209–221 | The gloss was embedded in the reference text; the printed text is restored and the gloss moved to a note. |
| 78-R4-09 | header comments; front matter, "Editorial convention" notice | EDN | header and notice: a pointer to `../EDITORIAL_NOTES.md` for recent changes and pointers to an earlier editorial report, change list and revision history that are not part of this project; revision date 14 September 2026 | header and notice point to `Papers/1978/jones1978_editorial_notes.md` (every discrepancy, with justification) and to `Papers/EDITORIAL_NOTES.md` (the dated log of revisions and checks); revision date 24 September 2026; `\allowbreak` in the two `\texttt` paths | The consolidated notes are the record (see the corpus-wide item on them). The `\allowbreak` avoids an overfull line; text unchanged. |
| 78-R4-10 | p. 335, footnote 2 (epigraph) | EDN | "The English paraphrase is retained from the original article; the Sanskrit and transliteration have been corrected." | "In the original this paraphrase is itself footnote 2, attached to the transliteration, and ends '—Bh.G., 11, text 7.' The Sanskrit, the transliteration and the paraphrase are as printed, except that the transliteration writes the anusvāra ṃ where the original has ṁ." | Against the print only the ṁ→ṃ convention changed; the corrections were to the OCR (1978-01 to 1978-03). |
| 78-R4-11 | p. 335, margin mark | EDN | `\origpage{335}` at the third paragraph of §1 ("In this article we construct…") | at the first line of §1 ("In his celebrated paper…") | The first two paragraphs are also on p. 335; the mark now sits at the start of the article text, as in the 1984 edition. |
| 78-R4-12 | §1 p. 337 | CLAR | "although the same class of relations is obtained … after the appropriate change of variables." (silent) | same, with an editorial note quoting the printed "although it makes no difference whether we specify nonnegative integers, positive integers or integers." | 1978-10: make the clarification visible. |
| 78-R4-13 | §1 p. 338 (twice), Corollary 1 | CLAR | "effectively axiomatizable" ×3 (silent) | editorial note at the first occurrence quoting "any other axiomatizable theory", "an axiomatic theory $T$", "any axiomatizable theory $T$" | 1978-15: make the added hypothesis visible. |
| 78-R4-14 | §1 p. 338 | CLAR | "Hence from Theorem 3 we obtain a uniform bound on the arithmetic-operation count for checking such a Diophantine certificate. This is not a bound on the sizes of the integers, the time needed to find them, or the length of an ordinary formal proof." | printed sentence restored: "Hence from Theorem 3 we obtain an absolute epistemological upper bound on the complexity of mathematical proofs.", with the qualification in an editorial note | 1978-16: a philosophical claim, not a mathematical error; the author's words are kept and the precise reading goes into a note. |
| 78-R4-15 | §2 p. 340, Divisor Lemma | CLAR | "For $n\geq1$ and any integers …" (silent) | same, with an editorial note quoting "For any integers $s,t_1,\cdots,t_n$, $s\geq0$, if" | 1978-21. |
| 78-R4-16 | §2 pp. 340–341, BQT preamble, Lemma 2.3, proof of necessity | CLAR | $n\geq1$, positive $R(z)$ for $z\geq1$, "integers $z\geq1$ and $r,z_1,\ldots,z_n\geq0$", "$z\geq\max(1,\tau)$" (silent) | one editorial note in the preamble quoting the three printed phrases | 1978-23. |
| 78-R4-17 | §2 p. 341, after (4) | TYPO + CLAR | corrected identity and two added sentences (silent) | editorial note quoting "The identity $j(r+1/j-1)-i(r+1/i-1)=i-j$ implies that the factors of (4) are pairwise relatively prime." | 1978-27. |
| 78-R4-18 | §2 p. 342, Lemma 2.5 | CLAR | "For $d>0$, if …" (silent) | same, with an editorial note quoting "If $a\equiv b\pmod d$" | 1978-28. |
| 78-R4-19 | §2 p. 344, after Lemma 2.9 | CLAR | $e_0$ in A3, in the paragraph and on p. 349 (silent) | editorial note: the original writes $e$ in all these places, including "If we take $e=M(u)$ in A3" | 1978-33. |
| 78-R4-20 | §3 pp. 345–346 | CLAR | index ranges of $P_k$; "when $k\geq2$; $P_0=P_1=0$" (silent) | same, with an editorial note | 1978-36. |
| 78-R4-21 | §3 pp. 346–347 | CLAR | rewritten nonnegative-witness paragraph ($\widehat W_n$, $S_+$) (silent) | rewrite kept; editorial note quoting the whole printed paragraph and giving the $n=5$ failure | 1978-40: the printed text is mathematically wrong (reuses $S$ for another residue; "$x\in W_n\Leftrightarrow$ (3.3)" fails at $n=5$), so the replacement stays. |
| 78-R4-22 | §3 p. 347 | CLAR | "We now return to the integer-witness enumeration $W_n$ …" (silent) | same, with an editorial note quoting "We continue using Lemma 3.2. We also continue with the modulus" | 1978-42. |
| 78-R4-23 | §3 p. 348, after U0–U8 | CLAR | added sentence on scalar $J$ and on $Z$ (silent) | same, with an editorial note: sentence added; the print has $z$ in U0 and omits $u,v$ from the unknowns | 1978-47 (and 1978-46). |
| 78-R4-24 | §3 p. 348, proof of necessity of Lemma 3.5 | CLAR | witness-bound and $g$-shift completions (silent) | editorial note quoting "It is not difficult to show that these numbers, when they exist, need never be as large as $T_1+R^3$" and "…find $b,e,g,s,w,\pi,T,P$ satisfying U7 and U8" | 1978-48. |
| 78-R4-25 | §3 p. 349, collected conditions | CLAR | "with $z=Z$" and the $z_1$/$g$ parenthesis (silent) | editorial note quoting "hold with $z_1,\cdots,z_5$ replaced by $b,e,g,s,t$ respectively and $B\leq C$ dropped from A1." | 1978-50 (with 1978-49). |
| 78-R4-26 | §3 p. 349, final paragraph | CLAR | "the Pell-sequence definition A1–A7 by the alternative definition Q2–Q4, using T9 for $B\leq C$" (silent) | same, with an editorial note quoting "replacing conditions A1–A7 by the equivalent equations Q2–Q4" | 1978-53. |
| 78-R4-27 | §3 p. 349, combined divisibility | LAYOUT | footnote mark directly after $F(hM(v)-x)^2$ | footnote mark after "in A1 by", before the formula | The mark after the square read as part of the exponent ("²¹⁸"); note text unchanged (1978-51). |
| 78-R4-01 | preamble (font setup) | BUILD | `\newfontfamily\devanagarifont{Noto Serif Devanagari}…` | `\IfFontExistsTF{Noto Serif Devanagari}{…}{\newfontfamily\devanagarifont{Nirmala UI}…}` | The epigraph needs a Devanagari font; Noto Serif Devanagari is not part of MiKTeX/TeX Live, so the source did not build on a stock installation. Nirmala UI ships with Windows. Text unchanged; only the fallback glyph shapes differ. At the time of this change the committed PDF was still an earlier build with Noto. |

---

## 1974 — Recursive Undecidability—An Exposition

**Status: read twice in full; every printed machine simulated; counts and
Table 1 re-derived for n ≤ 3. One restored wording in the first reading;
nine typographical and pointer items in the second (2026-09-14). No
mathematical error.**

### Checks performed (`verification/round4_1974_checks.py`, and the checker
`verification/jones1974_verify_counts.cpp` compiled with g++ -O3)

- Example 1: on a blank tape halts after 6 shifts with 4 ones; started on
  the leftmost of n ones (n = 1..7) halts after 4 shifts scanning the
  leftmost of n+2 ones. Matches the text and the displayed trace.
- Example 2 computes f(x) = 2x for x = 0..8 under the unary convention
  (x+1 ones in, 2x+1 ones out, head on the left end, rest blank), and loops
  on a blank tape, as stated in §5.
- The machine M^(2) as printed equals the general construction described
  below it; M^(x) prints x+1 ones and halts on the leftmost for x = 1..6.
- The composition T[M^(x)] (relabel into disjoint blocks, redirect halts)
  prints 2x+1 ones with x+6 states, as used in the proof of Theorem 1.
- The extra card of §5 (state n+1) adds exactly one 1 to a halting machine.
- Exhaustive enumeration of all (4n+4)^(2n) labelled tables: n=1 gives
  64 tables, H=32, Σ=SC=SH=1; n=2 gives 20736 tables, H=9784, Σ=4, SC=4,
  SH=6, and 4·12³ = 6912 immediate halts (the bound L_n). The C++
  checker gives n=3: 16,777,216 tables, H=7,571,840, Σ=6, SC=7, SH=21.
  These are the Table 1 entries and the quotients 0.500, 0.472, 0.451.
- 20⁸ = 25,600,000,000 four-state tables; L_n > U_(n−1) for n = 2..11.

### Comparison with the OCR of the scan

- Table 1's lower bounds (Σ(5) ≥ 16, Σ(8) ≥ 9×10⁴¹, SH(7) ≥ 10⁶⁹³,
  Σ(10) ≥ 10^(2×10⁴⁴), …) are exactly the printed 1974 figures. They are
  historical and are not updated (the table is labelled as such).
- A diff of every multi-digit number between the OCR and the edition found
  only documented corrections of the edition (Invent. Math. 12, 177–209; Monatsh.
  38, 173–198; the quotient 0.472 = 9784/20736 correctly rounded) and one
  undocumented wording change, repaired below.

### Second full reading (2026-09-14)

An independent line-by-line reading against the scan and the discrepancy
register of the edition, with every machine re-simulated in a scratch script and by an
independent C++ enumerator. Found: no mathematical error; the
typographical and pointer items 74-R4-02 … 74-R4-10 below. Checks that
found nothing:

- Example 1 on the blank tape: 6 shifts, 4 ones; from the leftmost of `n`
  ones (`n = 1..9`): 4 shifts, leaves the leftmost of `n+2` ones; the
  five-configuration trace matches the printed display. Example 2 computes
  `2x` for `x = 0..12` and loops on the blank tape. Every card of Examples
  1–2, of card `n+1`, and of `M^(2)` matches the scan images. `M^(x)`
  (`x = 1..8`) has `x+1` states and prints `x+1` ones, halting on the
  leftmost; `M^(0)` never halts, so the text's `x ≥ 1` is necessary (as the
  Lean note above records). `T[M^(x)]` has `x+6` states and prints `2x+1`
  ones; `M[T[M^(x)]]` prints `f(2x)+1` ones with `x+6+c` states.
- Counts: `(4n+4)^{2n} = 64, 20736, 16777216`; `H = 32, 9784, 7571840`;
  `Σ = 1, 4, 6`; `SC = 1, 4, 7`; `SH = 1, 6, 21`; `L_n = 32, 6912,
  4194304`; quotients `0.500, 0.472, 0.451`; `20⁸ = 25600000000`;
  `L_n > U_{n−1}` for `n = 2..59`; `SH ≤ n·SC·2^SC` on every halter with
  `n ≤ 2`. All nine rows of Table 1 agree with the scan, including the
  blanks.
- Theorems 1–2, Corollary 1, (1)–(4), the hyperimmune/immune/retraceable
  claims, the r.e. set `{(m,n): m ≤ H(n)}`, the game's winning condition
  and the `n ≥ 12+2c` arithmetic: verified by hand.
- A sentence-level diff of the prose against the OCR (113 changed blocks):
  every difference is a documented item of the register (now
  `1974/jones1974_editorial_notes.md`), 74-R4-01, or a cosmetic
  normalization. All 42 references compared with
  the scan; all citation keys resolve; [3], [36], [38] are uncited as in
  the original. The "21 variables" attributed to [24] agrees with the
  1976 paper's addendum. The printed "Dokl. Acad." in [22] (against
  "Dokl. Akad." in [1], [24]) is left as printed.

### Changes

| id | location (orig.) | class | old | new | reason |
|---|---|---|---|---|---|
| 74-R4-02 | throughout (pp. 725–732) | TYPO | straight ASCII double quotes `"…"` (20 pairs: "Game of Life", "add 2", "0" (blank), "yes", "thesis", the Gauss, Gödel and Post quotations, …) | ``…'' | Under T1 encoding `"` typesets as a straight double quote; the scan uses typographic quotes everywhere, and the edition already used ``…'' in two places. Also removed a stray space inside the quotation "$v$ is the $2u$th Fibonacci number" (p. 728, OCR carry-over). |
| 74-R4-03 | §4, p. 729 | TYPO | `The $i$ th card` | `The $i$th card` | OCR spacing; only the second `$i$th` of the sentence had been fixed. |
| 74-R4-04 | §5, p. 731 | TYPO | `$25,600,000,000$` | `$25{,}600{,}000{,}000$` | In math mode the commas set as punctuation with following space ("25, 600, 000, 000"); Table 1 already uses `{,}`. Value `20⁸` correct. |
| 74-R4-05 | §6, p. 733 and §7, p. 734 | TYPO | `$(4 n+4)^{2 n} n$-state` (twice) | `$(4n+4)^{2n}$ $n$-state` | The `n` of "n-state" was inside the math group, so no space was set between the count and the word (checked in the PDF text). |
| 74-R4-06 | §3, p. 727, editorial footnote on integration | BUILD | line break between the sentence and `\footnote{…}` | `%` at the end of the line | The line break set a space before the footnote mark ("hypotheses. ¹"). |
| 74-R4-07 | §2, p. 726 | TYPO | `1912-14` | `1912--14` | En dash as in `1954--56`, `1963--64` and the scan. |
| 74-R4-08 | §7, editorial proof detail after (4), p. 735 | EDN | "is given in the editorial notes" | a pointer to earlier notes that are not part of this project | The `3n`-state construction was then only in those earlier notes; the unqualified pointer was dangling from `Papers/`. Superseded by 74-R4-11. The construction was re-implemented and run on every halting 1- and 2-state table (32 + 9784): each simulation halts with strictly more ones than the original's actively scanned squares, with at most `3n` states. |
| 74-R4-09 | §7, editorial proof detail, p. 735 | CLAR | "The machines which halt on their first blank-tape transition already give `L_n ≤ H(n) < U_n`." | "… already give `L_n ≤ H(n)`, and (2) gives `H(n) < U_n`." | The immediate halters give only the lower bound; the strict upper bound is inequality (2), which needs a non-halting table. |
| 74-R4-10 | reference [9], p. 737 | BIB | `\emph{American Mathematical Monthly}` | roman | The only entry with an italic journal title (the edition expanded the printed "this Monthly"); every other entry sets the journal in roman. |
| 74-R4-11 | §7, editorial proof detail after (4), p. 735 | EDN | the pointer of 74-R4-08 to earlier notes that are not part of this project | "is given in the editorial notes, `Papers/1974/jones1974_editorial_notes.md` (entry 1974-59), and is formalized in `Lean/Diophantine/Paper1974/Doubling.lean`" | The consolidated notes are the record; the construction is §5.2 (g) of them. |
| 74-R4-01 | §2, p. 726, word problem paragraph | EDN | "In the mid-1950s, P. S. Novikov and W. W. Boone …" | "During the period 1954--56, P. S. Novikov and W. W. Boone …" | Restores the author's printed wording. An earlier revision of this edition had replaced the date range by a vaguer phrase without a stated reason; the range is the author's historical statement and is not wrong (Novikov 1955, Boone 1954–57). |

---

## 1984 — Register machine proof of the theorem on exponential Diophantine representation of enumerable sets

**Status: fully read; Example 1 and its trace table reproduced; the whole
encoding (24)–(39) checked as integers on six accepted inputs; section-2
and section-4 identities checked. No change required.**

### Checks performed (`verification/round4_1984_checks.py`, an independent
re-implementation, standard library only)

- Example 1 with input 2 stops after exactly 18 transitions with all
  registers zero; the printed 19-column table (four R rows and fifteen L
  rows, time increasing to the left) is reproduced column by column.
- Inputs 2..60 are accepted exactly when prime; inputs 0 and 1 have not
  stopped after 20,000 transitions (the general divergence proof is in
  `1984/jones1984_editorial_notes.md`). No subtraction from a zero register occurs on any run.
- For inputs 2, 3, 5, 7, 11, 13 (18, 57, 192, 405, 1042, 1495 steps) the
  numbers Q = 2^(x+s+l+2), I, R₁..R₄, L₀..L₁₄ were built from the actual
  computation and conditions (24)–(33), the fall-through conditions, (34),
  (35) at L2, (36) at L6, L8, L9, L10, L11, L13 (with the constant 0 encoded
  as history 0), and the register equations (38), (39) all hold as integer
  ≼-relations. This is the necessity direction of §3, checked with the
  printed formulas and no reinterpretation.
- Borrow analysis of (35)–(37), written out by hand: in the fall-through
  case the block below the decision block is negative, so the borrow makes
  the decision block odd; in the jump case no borrow arrives. Both need
  l_{k,t} = 0 whenever l_{i,t} = 1, which is exactly why a self-targeting
  conditional jump (k = i) must be normalized away, as the edition
  states.
- (8) gives the binomial coefficient uniquely for n ≤ 8, k ≤ n+2 (including
  the convention C(n,k) = 0 for k > n); (9) holds for x ≤ 5, 2 ≤ y ≤ 5
  (including x = 0); (10)–(13), the Lucas lemma (r ≼ s ⟺ C(s,r) odd) and
  (43) verified by brute force; the multiplication macro (45) computes the
  product for all 0 ≤ a, b ≤ 11.
- (47) and (49) (with the edition's term +L_p) hold on synthetic register
  histories; the printed "+I" form of (49) fails already for the history
  (3, 5, 2, 7) with the halving line executed at time 0 and Q = 16, which
  confirms the edition's correction.

### Second full reading (2026-09-14)

An independent reading of all 597 lines against the OCR, with the scan
consulted wherever the edition departs from the OCR, and an independent
simulator/encoder script (standard library only). No mathematical error;
the typographical and structural items 84-R4-01 … 84-R4-08 below. Checks
that found nothing:

- Example 1: input 2 stops after exactly 18 transitions with all registers
  0; all 19 × 19 entries of the printed trace table match the simulation;
  inputs 0–59: primes stop with zero registers, composites enter the
  L10/L11 two-state cycle, 0 and 1 have not stopped after 200000 steps; no
  decrement from a zero register on any run; every statement of the
  editorial invariant check (1984-20) holds.
- The encoding (24)–(39) built from the actual computations with
  `Q = 2^(x+s+l+2)` for inputs 2, 3, 5, 7, 11 (`s = 18, 57, 192, 405,
  1042`): every condition holds as an exact integer `≼`-relation, all
  conditional targets satisfying `k ∉ {i, i+1}`.
- The carry/borrow analysis of (35)–(37) redone independently: the carry
  out of block `t` is exactly `[r_j = 0]`, `[r_j ≥ r_m]`, `[r_m ≥ r_j]`,
  independent of the incoming carry as long as carries are `≤ 1`, which
  holds for `t < s` from `r_{j,t} ≤ x + t`; digit-wise reading of
  (38)/(39); singlefoldness of `s` via (33).
- §2 identities (8) for `n ≤ 8`, (9) for `x ≤ 6`, `2 ≤ y ≤ 5`, (10), (11)
  on all `64³` triples, (12) with the `a > 0` guard, (13) with `Q = 16`,
  the Lucas lemma for `r, s < 130`, (4) singlefold for `c > 0`, the
  divisibility footnote (including `0 ∣ 0`), (43), the clearing macro, the
  multiplication macro (45), (47) and (49) on 300 random histories, (40)
  on a one-line program; `Q = 2^(s+|x|+l+3)` satisfies (25), (26), (46).
- The edition note on `Q = 2^(x+s+l)`: the only accepting computation
  violating (24)–(26) is `x = s = l = 0`, as the note says. (37) is stated
  with `k ≠ i+1` only, (36) with `k ∉ {i, i+1}`: consistent, since only
  (36) has `L_k` in its second condition.
- A sentence-level diff against the OCR: every wording difference is a
  documented item of the register (now `1984/jones1984_editorial_notes.md`)
  except the dropped "say" (84-R4-05). The scan confirms: "l < Q, by (25)"
  (so 1984-22 is a sharpening), "(12)" without `a > 0` (1984-10), "say at
  the end", "Ri ← 0 is obtained by iterating (42)" (1984-30 correctly a
  source error), "oonarnoe" (the unary parenthesis).
- All tags (1)–(54) present once and in order; every citation year has a
  bibliography entry; the bibliography data check against memory for all
  entries; Melzak 279–293 stands. Left as printed: the text's
  "J. M. Barzdin'" against the bibliography's "Ja. M. Barzdin'" (the scan
  has the same); Jones [1982] and Matijasevič [1977] are uncited in the
  original too.

### Changes

| id | location (orig.) | class | old | new | reason |
|---|---|---|---|---|---|
| 84-R4-01 | §4, p. 828 | OCR | `$A \in N P$` | `$A\in\mathrm{NP}$` | The OCR's italic "N P"; the three other occurrences were already `\mathrm{NP}`. |
| 84-R4-02 | §1 p. 819 and §4 p. 827 | TYPO | `170-172, 204-206` (Minsky page ranges, twice) | en dashes | Bibliography and the rest of the edition use `--` in ranges. |
| 84-R4-03 | §2 p. 821, §3 pp. 822–825, §4 p. 827 | OCR | `2 :`, `1 , in place`, `$x$ ).`, `2 .` (twice), `1 .`, `)$ :` | space before the punctuation removed (seven places) | Mathpix spacing artefacts; the scan has none. |
| 84-R4-04 | §1 p. 819 / §2 p. 820 | EDN | one editorial note at the §2 domain-conventions sentence covering both the conventions and the "corrupted Russian parenthesis in the definition of unary" | the note is split: the domain sentence keeps its part; a new note hangs on "Unary (one-place)" in §1, where the emended text is | The emendation was on p. 819 but its marker was a page later. The scan confirms the printed "Unary (Russian, oonarnoe)". |
| 84-R4-05 | §3, p. 825 | EDN | "the STOP command appears only once, at the end of the program" | "… only once, say at the end of the program" | Restores the printed "say" (scan p. 825), dropped earlier without a note; the convention that STOP is last is then a choice, as the author phrased it, and the later editorial sentence "the unique STOP remains last" still applies. |
| 84-R4-06 | preamble | BUILD | `\newcommand{\originalpage}[1]{} % Original locations are recorded in editorial_notes.` | removed | Unused since the `\origpage` marks (corpus-wide item on pagination marks); the comment pointed to a file that is not next to the source. |
| 84-R4-07 | §4 p. 828; references Matijasevič [1979], Minsky [1961] | TYPO | `"and"`, `"Nauka"`, `"tag"` | ``…'' | Straight ASCII quotes under T1 encoding; the journal printing uses typographic quotes. |
| 84-R4-08 | §3, editorial invariant check after Example 1 | CLAR | "causing line 10 to increase $k$" | "in which case line 10 returns to line 1, which increases $k$" | Line 10 is `IF R1 < R3, GO TO L1`; it changes no register. |
| 84-R4-09 | §1 p. 819, definitions of *singlefold* and *unary* | TYPO | "(Russian odnokratnoe; French univoque)"; "Unary (one-place)" with a footnote replacing the printed "(Russian, oonarnoe)" | "(Russian однократное; French univoque)"; "Unary (Russian, унарное)" with a footnote giving the printed transliterations | The printed *oonarnoe* is a phonetic spelling of унарное (standard *unarnoe*), not a corruption, so the Russian parenthesis is restored; both Russian terms are set in Cyrillic (`[T2A,T1]{fontenc}`, Tempora). |
| 84-R4-10 | edition notice | EDN | "OCR repairs and mathematical emendations are documented in the accompanying *Editorial notes*; substantive interventions are also marked below." | "Substantive interventions are also marked in the text." | The preceding sentence of the notice now names the consolidated notes. |

---

## Corpus-wide checks and decisions

- **Original pagination marks in all six editions (2026-09-14; EDN).**
  Every `Papers/<year>/jones<year>_corrected.tex` now loads
  `marginnote` and defines `\origpage{n}`, which sets a bold `[n]` in the
  margin on the line where page n of the journal printing begins (the title
  page is marked at the first body paragraph). Placement is to the line, not
  to the word. Method: the first words of every scan page were extracted
  from the text layer of the JSTOR/AMS PDFs and matched to the corrected
  sources; the matches were checked, and the unmatched or ambiguous starts
  (pages beginning inside a display, a program listing, a lemma statement,
  or a reference list: 1974 pp. 731, 733, 736, 738; 1976 pp. 453, 455, 457,
  459, 463; 1978 pp. 341, 344, 347–350; 1982 pp. 550, 551, 554, 556, 557,
  560, 570; 1984 pp. 823, 824, 828) were placed by hand from the scans.
  Where the edition reworded a passage, the mark sits at the corresponding
  step of the rewritten text (1976 p. 463: the analytic-continuation step
  of the proof of Theorem 4.2; 1974 p. 736: the sentence introducing the
  historical table). Marks inside `align`/`array`/`equation` displays use
  `\marginnote` directly, which works in math mode. All six PDFs were
  rebuilt with their engines (pdfLaTeX; LuaLaTeX for 1978; XeLaTeX for
  1982); page counts are unchanged and every mark renders (checked by
  extracting the `[n]` strings from the PDFs). Counts: 1974 15, 1976 16,
  1978 17, 1980 4, 1982 23, 1984 12.

- **Edition notices, headers and the operation-count footnotes
  (2026-09-14; EDN).** All six sources still described themselves as a
  fixed reviewed edition and pointed to an editorial report, a change list
  and a revision history, none of which exists next to `Papers/`, although
  the files had carried changes since the pagination marks. The project
  owner decided on 2026-09-14 that the edition will not be frozen as a
  snapshot: all further work happens incrementally under `Papers/`. The
  header comments and the visible notices of all six editions therefore
  now describe them as continuously revised, point to
  `Papers/EDITORIAL_NOTES.md` for the dated log of revisions and checks
  (the pointers to the earlier record were replaced on 2026-09-24 by the
  consolidated notes; see the next item), and, where the notice did not
  already say so, explain the bracketed margin numbers. The three
  footnotes that called the operation counts "not independently
  reconstructed/rederived" (1978 Corollary 1, 1980 Theorem 5, 1982
  Theorem 5) now state what the checks recorded here found: the counts
  100 and 87 are reproduced by counting every indicated sign once
  (exponentiation not counted), 243 comes out as 241, and whether that is
  the intended reading, and what the count is under a calculator model
  with powers by repeated multiplication, are examined in the satellite
  article. The sign-count reading is presented there as evidence, not as
  settled. The 1980 edition's last page needed `\enlargethispage` (4
  lines instead of 2pt) to keep the address block on the fourth page; the
  1982 notice needed an `\allowbreak` in a file path. All six PDFs were
  rebuilt (page counts unchanged: 16, 18, 18, 4, 24, 14).

- **Consolidated editorial notes (2026-09-24; EDN).** The editorial notes
  are consolidated per article in `<year>/jones<year>_editorial_notes.md`:
  every discrepancy between the naive OCR of the scan and the edition, in
  its final state, with classification and justification. The header
  comments and the visible notices of all six editions name that file and
  this log; the in-text pointers are 74-R4-11, 76-R4-13, 80-R4-02 and the
  satellite article's reference to the 1976 certificate. The article
  checkers in `verification/` are `jones1974_verify_machines.py`,
  `jones1974_verify_counts.cpp`, `jones1976_verify_mathematics.py`,
  `jones1976_verify_87_operations.py` (with `jones1976_primality87.json`
  and `.md`), `jones1978_validation.py`, `jones1982_verification.py`,
  `jones1984_verification.py` (with `jones1984_example1_trace.csv`),
  `corpus_cross_review.py` and `corpus_review.py`. They read the current
  sources (one anchor was updated for 76-R4-04), and all pass.
  `Lean/STATUS.md` and the docstring of `Paper1976/PrimalityCertificate.lean`
  point to the certificate files in `verification/`. The five PDFs other
  than 1978 were rebuilt with their engines (page counts unchanged: 16, 18, 4, 24, 14; the satellite 208).
  In 1978 the same day, all fifteen unmarked clarifications were marked
  with editorial notes and the printed "absolute epistemological upper
  bound" sentence was restored (78-R4-09 to 78-R4-27); its PDF grew from
  18 to 19 pages.

### Number diff against the scans

For each article, every number of two or more digits was extracted from the
Mathpix OCR of the scan and from the current source (after stripping
comments, commands and link targets) and the two multisets were compared,
with context printed for every difference. Apart from edition metadata
(DOIs, dates, page headers) the differences are exactly: the documented
corrections in 1974 (two reference page ranges, the rounded quotient 0.472
of 1974-63), the 1980 OCR defect b⁵⁶⁰ → b^(5⁶⁰) (1980-09), the Melzak page
range 279–293 in 1984 (1984-48, correct), the added pages 433–434 of
Jones's *Canadian Math. Bull.* note in 1976 (correct), and the two items
acted on in this log (74-R4-01, 76-R4-02).

### The 354–357 / 354–358 question, resolved

The six originals disagree about the last page of the English translation
of Matiyasevich's 1970 note: 1974, 1982 and 1984 print 354–357; 1976, 1978
and 1980 print 354–358. The editions of 1978 and 1980 had been emended to
357 (citing the author's publication list and Jones 1982) while 1976 was
left at 358, and the inconsistency had been recorded as unresolved. The *Journal of Symbolic Logic*
Reviews entry for the paper (Cambridge Core) records the translation as
"Soviet mathematics, vol. 11 no. 2 (1970), pp. 354–357", with errata in
vol. 11 no. 6, p. vi. This is a bibliographic record of the translation
itself, so 354–357 is adopted throughout; 1976 is changed accordingly
(76-R4-02). The bibliography document (not included here) already uses
354–357.

### Spelling and build hygiene

- All prose words of the six sources (mathematics, references and commands
  stripped; 1802 distinct words of four or more letters) were checked
  against the Wolfram Language dictionary. The 43 words not found are all
  names (Daihachiro, Hideo, Wiens, Cassels, Steklov, Reiner, Kioicho,
  Krisnis, Kosovski…), LaTeX option names, or standard technical terms
  (hyperimmune, retraceable, singlefold-type words, nonrecursive,
  calculability). No misspelling was found.
- The pass-2 LaTeX logs of every rebuild recorded above (1974, 1976, and
  the 1978/1982 test builds) contain no undefined references or citations,
  no multiply defined labels, and no overfull boxes.

### Findings from the Lean formalization (`../Lean/`)

- **1976, Corollary 2.6 and Theorem 2.12.** The article's equations are
  polynomial identities over the integers with unknowns ranging over the
  nonnegative integers; the Lean statements (`Cor26System`,
  `Thm212System`, `primePoly`) therefore cast the ℕ unknowns to ℤ. The point
  matters: if `u²(u²−a)` in (III) of Corollary 2.6 (equation (8) of Theorem
  2.12) were read with truncated subtraction in ℕ, the case `r = 0`, `u = 1`
  would make `u²−a` vanish and the system would admit spurious solutions,
  for example `a = 2, n = 1, y = 4` with `x = 7`, `c = 355`, `d = 13`. The
  text needs no change, but the convention "all variables are nonnegative
  integers" (§2) must be understood as "the equations hold in ℤ". Recorded
  as CLAR-level context, no edit.
- The complete chain Lemma 2.3 → Corollary 2.6 → Lemmas 2.7–2.11 → Theorem
  2.12 → Theorem 1 of the 1976 article has been machine-checked in Lean 4
  against Mathlib (`Lean/STATUS.md`); no gap in the printed arguments was
  found. The only external inputs are Mathlib's Pell/Matiyasevič
  characterization, the general Pell existence theorem, Bernoulli's
  inequality and Wilson's theorem.

- **1984, §3 (the register-machine encoding).** The equivalence "the
  machine accepts `x` iff conditions (24)–(39) are solvable" has been
  machine-checked in Lean 4 for the paper's command set (15)–(19) with the
  constants 0/1 as comparison operands and with the parallel `±1` updates of
  Example 1 (`Lean/Diophantine/Paper1984/Theorem.lean`, `RM.accepts_iff`).
  Three points that the printed proof leaves implicit had to be supplied:
  1. *Carries in (35)–(37).* The number `L_n + QI + 2U − 2V` is not written
     to the base `Q` with proper digits: block `t` has value
     `l_{n,t} + Q + 2u_t − 2v_t`, which lies between `2` and `2Q − 1`, so
     carries propagate. The intended reading (bit 0 of block `t+1` equals
     `l_{n,t+1} XOR [u_t ≥ v_t]`) holds only because (a) the carries are all
     `0` or `1`, which needs the block values to be at most `2Q − 2` at the
     times `1 ≤ t < s`, and (b) at a time when line `i` is executed the line
     `n ≠ i` is not, so no `+1` from `L_n` enters the block that produces the
     carry. Point (a) follows from `r_{j,t} ≤ x + t` (not just from (24)),
     and for the constant operand `1` it needs `Q ≥ 8`, which (24) supplies
     whenever `s ≥ 2`. This is exactly where the edition's normalisation
     `k ∉ {i, i+1}` is used (`Compare.lean`, `compare_cond`).
  2. *The zero-register convention.* The paper assumes that subtraction from
     a zero register "never occurs". In the formalization such a step has no
     successor, and the register equations (38)/(39) indeed have no solution
     for a run that attempts it, so the convention costs nothing.
  3. *(25) is used for (30).* The condition `l + 1 < Q` is what makes the
     column sums `Σ_i l_{i,t} ≤ l + 1` proper base-`Q` digits, so that (30)
     can be read column by column; the paper says only "since `l + 1 < Q`".
  No error in the printed conditions was found. The translation of (24)–(39)
  into a single exponential Diophantine equation by the identities of §2, and
  the trampoline normalisation of self-targeting conditional jumps, are not
  yet formalized (`Lean/STATUS.md`).
- **1976, §3 (Theorem 3.9, the ratio method).** Theorem 3.9 has been
  machine-checked in both directions (`Lean/Diophantine/Paper1976/Theorem39*.lean`,
  `JSWW1976.theorem_3_9`), together with Lemma 3.8 of Matijasevič–Robinson,
  which the article cites without proof and which is now proved in full
  (`MR.lean`; the converse direction needs the residues of `ψ_A` modulo
  `χ_A(n)`, `Common/PellMod.lean`). Points worth recording:
  1. The chain (17), `R/C < (2Mx)^{k+1}/(2Mx)^n ≤ 1/(2Mx)²`, needs
     `n − k − 1 ≥ 2`, i.e. `n ≥ k + 3`; this follows from (2) since
     `(2k)^{2k} ≥ 4k ≥ k + 3`, but the text does not say so.
  2. The estimate (11) is proved with `≤` on the right (`|σ − a| ≤ (n/M)a`,
     Lemma 3.1 gives only `≤`); the strict inequalities used afterwards
     (`ε₁ < 1/8`) still follow because `a < 2σ` is strict.
  3. The parenthetical "the rational expression in (XIV) must be defined" is
     formalized as the explicit side conditions `K, L, C ≠ 0`,
     `σ − (w+1)x ≠ 0`, `R ≠ C`; without them the ratio method has spurious
     solutions (a vanishing denominator would make (XIV) read `(S+1)² < 1/4`
     in the Lean convention `x/0 = 0`).
  4. In the sufficiency proof the case `σ − (w+1)x < 0` is not mentioned; it
     is excluded because then `β ≤ 0`, whereas (XIV) forces `β > S + 1/2`.
     The same observation replaces the paper's `σ < 1/2 ⇒ β < 0` in the
     argument that `p' = l' = 0`.
  5. The paper's square-root estimate for `r' > 0`
     (`R/(R/C − 1)² < 1/4` from `C < R^{1/2}/3`) is replaced by the
     equivalent polynomial inequality `4RC² < (R − C)²`, valid for
     `R > C³` and `C ≥ 5`.
  6. In (20) the bound `(1 − (2Mx)^{-2})^{-2} ≤ 1 + 1/(Mx)` is used with
     `(1+2t)² ≤ 1 + 8t` and `8/(2Mx)² ≤ 1/(Mx)`, i.e. `Mx ≥ 2`; in (21) the
     factor `(1 + ε/C(n,k))^{-1}` is bounded below by `1 − 1/(4C(n,k))`
     directly from `s ≤ C(n,k) + 1/4`, which is simpler than the paper's
     condition (ii').
  No error in the printed statements was found. At this stage Theorem 2
  (twelve variables) additionally needed the relation-combining theorem
  of [11]. The later relation-combining and refined-degree milestones
  below record the subsequent construction and its validation boundary.

- **1974 (the Turing machine exposition).** Theorems 1 and 2, Corollary 1,
  the non-computability of `Σ`, `SC` and `SH`, the bound (2) on `H(n)`, and
  Example 2 have been machine-checked (`Lean/Diophantine/Paper1974/`,
  `Jones1974.theorem_1`, `corollary_1`, `winningII_iff`, `H_lt`,
  `doubler_computes`). Points worth recording:
  1. *The printer `M^(x)` needs `x ≥ 1`.* The card of the last state writes a
     one on a zero and moves right in the same state, and on a one halts; for
     `x = 0` the machine starts in that state on the blank tape and never
     meets a one, so it never halts. The proof of Theorem 1 only uses `x ≥ 1`
     (`n ≥ 12 + 2c` gives `x ≥ 3`), so the text is correct as printed.
  2. *Corollary 1 without Kleene.* The article passes from Theorem 1 to
     Corollary 1 through `f̂(n) = n + Σ_{i≤n} f(i)`, whose computability is
     taken from Kleene's closure theorems. The formalization avoids this: the
     odd arguments `2x + 1` are reached by appending a 3-state successor
     machine to the doubler, which gives `f(2x+1) + 1 ≤ Σ(x + 9 + c)`, and
     together with the even case `f(2x) + 1 ≤ Σ(x + 6 + c)` and the
     monotonicity of `Σ` this yields `f(n) < Σ(n)` for all `n ≥ 17 + 2c`
     directly for an arbitrary computable `f` (the monotonicity of `f` is
     needed only for the paper's sharper bound `12 + 2c`).
  3. *`Σ(n) < Σ(n+1)`.* The remark that a new card "may be instructed to move
     right across ones to overprint with 1 the first 0 encountered, and halt"
     is verified for `n ≥ 1`; it requires the tape at the halting time to
     contain finitely many ones, which holds because a run of `t` steps
     never leaves `[-t, t]`.
  4. *The game.* Theorem 2 is formalized as: player II's function `f` wins
     iff `SH(n) ≤ f(n)` for every `n` (the "iff" is the paper's definition of
     winning, made explicit), `SH` itself wins, and no Turing computable `f`
     wins since `Σ(n) ≤ SH(n)`. For player I, no strategy `g` with
     `g(m) ≥ 1` can win against every II, because II may answer with `SH`.
  5. *The non-computability of `H`.* The article's argument (dovetail all
     `n`-state machines until `H(n)` of them have halted) is informal and is
     not formalized; only the count `H(n) < (4n+4)^{2n}` of (2) is proved
     (the machine whose every card moves right into state 1 never halts).
  No error in the printed statements was found.

- **1978 (three universal representations).** Theorems 1, 2 and 3 and
  Lemmas 2.1–2.10, 3.1, 3.2, 3.4, 3.5 have been machine-checked
  (`Lean/Diophantine/Paper1978/`, `Jones1978.theorem_1`, `theorem_2`,
  `theorem_3`), for the enumeration `Wₙ` of the Diophantine sets of positive
  integers; that the list also contains every recursively enumerable set is
  the theorem of Davis–Putnam–Robinson–Matijasevič cited by the article and
  is neither used nor assumed. Points worth recording:
  1. *Lemma 2.8 and its variant.* The partial-binomial lemma is cited from
     [20] without proof, and the variant used in (1.3) (`5(C − KLY)² ≤ K²L²`
     with `M = 9NXY`, for `1 < Y` and `8N^Z < X`) is stated with "we may
     replace". Both are proved by the ratio method; the only properties of
     `M` needed are `8N ≤ M`, `4(X+1) ≤ M`, `N/(2M) ≤ 1/32` and
     `2Y·N/(2M) ≤ 1/8`, under which `|C − KLY| ≤ (25/64)KL` when
     `Y = ⌊(X+1)^N/X^Z⌋`.
  2. *Lemma 2.10 and equation (1.3.36) must be read over the integers.* In
     Q4 the factor `F² − A` is negative when `i = 0` (then `F = 1`), and the
     integer reading is exactly what excludes `i = 0`. With natural-number
     (truncated) subtraction the system Q1–Q4 has spurious solutions, for
     example `A = 2, B = 1, C = 4, D = 7, F = 1, i = 0, j = 26, τ = 355`
     (then `C ≠ ψ_A(B) = 1`). The same applies to (1.3.04), (1.3.09),
     (1.3.19), (1.3.20), (1.3.30) and (1.3.36), whose subtractions are
     integer subtractions; in every solution of the whole system the
     differences `η − r`, `η − z`, `μ − 1`, `μχ − 1` are nonnegative anyway.
     The convention "all variables are nonnegative integers" of §2 must
     therefore be understood as "the equations hold in ℤ", as for the 1976
     article. Recorded as CLAR-level context, no edit.
  3. *Lemma 3.5, the case `R = 0`.* The text says "U2, U3 and U4 imply
     `2 ≤ β` and `3 ≤ R`"; this needs `x > 0` (the standing hypothesis of the
     lemma): for `θ = 0` one has `R = 0`, and then U3, U4 are contradictory
     only because `0 < x < β < M(u)` excludes `M(u) ∣ x` (case `h = 0`) and
     `hM(v) ≥ 1 + β` excludes U4 (case `h ≥ 1`).
  4. *Lemma 3.5, the estimate.* The "rather tedious estimation"
     `|A(y)B(y)C(y)| < Z^90` is verified (a crude bound of the form
     `c·Z^49·R^28` with `c < 30^14` and `R^28 ≤ Z^10` suffices, using
     `β < R` and `R³ ≤ Z`), and so is the inequality
     `(2ZZ!Z^90)^(Z^5) + Z ≤ Z^6 − 1 + (Z^6)^(Z^6−2)` for `Z ≥ 30`.
  5. *Lemma 3.5, necessity.* "By choosing the residue code `R` sufficiently
     large, these witnesses can be chosen smaller than `T₁ + R³`" requires
     `β` to be chosen first (from the coded values) and then
     `R ≥ V² + 10β + 1`, where `V` bounds the coded values: the Lemma 2.2
     witness `g` satisfies `g + 1 ≤ (1 + (R − T − P)²)(β − T² − P²)`, which
     is below `R³` only when `10β < R`. The article's "the Chinese-remainder
     representative for `g` may be increased by a multiple of `Z!q` until
     `g ≥ r`" is implemented by shifting all five witnesses above `r`.
  6. *Lemma 3.4.* The residue facts (`T = S(R,β,s)` from `T² < β`, and
     `S(R,β,3i) = T + P` from `(T+P)² < 2β`) hold for every `β ≥ 1` in the
     sufficiency direction; "provided `β` is sufficiently large" concerns
     only the converse. The case `u = 0` of `S(u) = S(v) + x` needs a
     separate argument (only `|x + S(v)| < M(0)` is available there).
  7. *Lemma 2.3 (BQT).* Formalized for any function of the arguments that
     respects congruences (the only property of polynomials used), with the
     unknowns indexed by `Fin (m+1)` and `z₁` the first one.
  No error in the printed statements was found.

- **1982, Theorem 1 and §4 (2026-09-14).** The exponential-binomial system
  has been checked against the displayed equations of Theorem 1 and (4.12).
  The Lean statement `Jones1982.theorem_1` uses all twelve witnesses as
  strictly positive natural numbers, with subtraction evaluated in `ℤ`.
  The following are CLAR-level proof details, with no article-source edit:
  1. *Admissible indices exist.* `exists_index_above` constructs (4.1) for
     every integer polynomial by choosing a power of two above the finite
     coefficient bounds and evaluating `lpoly` and `epoly` at `2z`. The
     first coordinate can exceed any prescribed bound; `exists_index`
     proves positivity of all three coordinates when `ν ≥ 1`.
  2. *Binomial domains.* The common equations imply `b ≤ q`, `l < q²`,
     `(b−1)l + 2 ≤ q³`, and `S₃ ≥ 0`. Thus the signed upper arguments are
     exactly `g + (q³−1−(b−1)l)` and `(b⁵−2)q + S₃`; the `Int.toNat`
     conversions in the Lean system preserve their integer values. No
     extra domain assumptions are appended to the theorem.
  3. *Positivity of `η`.* Oddness alone gives `η ≥ 0` in a product of the
     form `2η+1`. Here `g > 0` and the positive first mask make the first
     binomial coefficient at least two, while the other two odd factors
     are positive. Hence the odd product is at least three and `η > 0`,
     as required by the edition's positive-witness convention.
  4. *The sign of `D₀`.* The chain following (U17) uses `D₀ > 0`; this was
     already established in the paragraph preceding (4.9), from
     `e < q² < q³ < λ < zλ`. This is not an error in the article. The Lean
     lemma `UEqs.S3_nonneg` also supplies a direct sign-safe proof from
     the common equations, using `1+xB+g ≤ 2q` and `32z ≤ B`.
  5. *Scope.* The proof is uniform in `ν ≥ 1`, with exponent `5^(ν+2)`.
     `ν = 58` gives the printed exponent `5^60`. Neither the universality
     of `(58,4)` nor a representation of every recursively enumerable set
     is assumed by these Lean theorems. Those require further work in §5.
  No new typo or mathematical error was found in the checked passages.

- **1982, §4 packing and Lemmas 2.26–2.27 (2026-09-14).** Further
  formalization notes; compilation and axiom-audit results are tracked in
  `Lean/STATUS.md`. No new displayed-equation correction was identified.
  1. *The weaker inequality (U6').* The sentence after (U22) cites
     (U1)–(U17), while the displayed Theorem 2 uses (U6') in place of
     (U1) and (U6). The six block bounds also follow from this weaker
     system: `e,l < q²`, `g < q`, and the geometric sum for `λ` give
     `S₁,T₁ < q³`, `S₂,T₂ < q⁴`, and `S₃,T₃ < q⁹`. In particular,
     `q² ≤ λ`, so `e ≤ zλ`; hence the signed summand in `S₃` is
     nonpositive, and `S₃ ≤ 4q⁸ < q⁹` because `q ≥ 32`. These bounds
     require no carry condition. This completes the proof-reference
     detail needed to read the packed test in the sufficiency direction;
     it does not require strengthening Theorem 2's equations.
  2. *The expanded equation for `r`.* Expanding (U21)–(U24) gives exactly
     the corrected formula in Theorems 2 and 3, over `ℤ`. The third left
     block has multiplier `q⁷`, the third right block contributes `q⁸`,
     and the `+1` in `T+1` cancels the mask's `−1`. These are checks of
     the existing corrections, not new changes to the printed systems.
  3. *Positive new witnesses in Theorem 2.* The code
     `r=S(n²−n)+(T+1)(n²−1)` satisfies `r ≥ n²−1 ≥ n` for `n ≥ 2`.
     With `n=q¹⁶`, this also supplies `r,n ≥ 8` and `b ≤ n ≤ r` for
     the subsequent use of Lemma 2.25. Positivity of the central
     binomial coefficient makes its quotient by `n²` strictly positive.
  4. *Lemma 2.26.* Both groups (C1)–(C3) and (C1')–(C3') and both
     replacements for (B8) are retained. The bound needed in (13) follows
     directly from `B^(3B₁) ≤ U^(3B₁) ≤ U^R < A` and
     `Q³ ≤ U³ ≤ U^R < A`. The gap in (14) gives a strictly positive
     remainder `φ`, even with the extra `W` in (B8); `B₁ < ψ_A(B₁)`
     similarly gives `Δ > 0`. The primed group changes the newly
     adjoined congruence, leaving the inherited (B13) unchanged, exactly
     as in the statement of Lemma 2.26.
  5. *Lemma 2.27.* The product-square condition is split using the
     coprimality of `D,F,I`. The new formula for `G` gives `G ≡ 1 mod D`
     and `G ≡ A mod F`; the congruence `H ≡ C mod F` then gives
     `I ≡ D mod F`. Working modulo `C`, rather than `2C`, introduces
     the possibility `B+t₀=C`. Odd `B` excludes it, while `2B ≤ C`
     forces the harmless boundary case `A=B=t₀=2`, `C=4`, which
     still gives the required index `B=t₀`. The auxiliary `J` remains
     any fixed positive integer. Polynomial subtractions and `F ∣ H−C` are interpreted
     as integer identities and divisibility, respectively.
  6. *The positive `γ` in Theorem 3.* A congruence by itself gives an
     integer quotient. For the intended Pell witnesses, the stronger
     bound `2^k < ψ_A(k)`, valid for `A ≥ 3` and `k ≥ 2`, together
     with `χ_A(k) > (A−1)ψ_A(k)`, makes the numerator
     `χ_A(k)−2^k−(A−2)ψ_A(k)` strictly positive. Its divisor `4A−5`
     is positive, so `γ > 0`. This covers the required index
     `k=2r+1 ≥ 17` without adding a new condition to the article.

- **1982, Theorem 3 (2026-09-14).** The full polynomial system has been
  checked against the eighteen displayed equations and the list of
  twenty-eight positive witnesses. No new article-source correction was
  needed. The following CLAR-level details are retained for the proof:
  1. *Two reused names.* Theorem 2's exponent in `b=2^w` is eliminated.
     Theorem 3's `w` is the ratio multiplier in `U=n²w`. Similarly,
     Theorem 3's `η` is `k²−4(c−ksn²)²`, rather than Theorem 2's
     central-binomial quotient. The formalization keeps these witnesses
     separate when converting between the systems.
  2. *Sizes in the converse.* The first equation and `α > 0` already
     imply `xy < b`. For positive `x,y`, this gives `b ≥ 2` before
     recovering that `b` is a power of two. The common coding equations
     and the polynomial for `r` then give `r,n ≥ 8` and `b ≤ n ≤ r`,
     allowing Lemma 2.25 to be applied without a circular size argument.
  3. *Positive auxiliary witnesses.* Lemma 2.25 gives a strictly positive
     approximation slack. Its Pell square has a positive square root
     because its constant term is one. Corollary 2.29 supplies positive
     `d,f,i,j,o`; uniqueness of the Pell pair identifies `d` with
     `χ_a(2r+1)`, so the positive quotient proved above supplies the
     required `γ`. Every one of the twenty-eight unknowns is positive.
  4. *Signed equations.* The equations for `k,d`, the approximation
     square, and all three Pell equations are interpreted in `ℤ`,
     including the inner `d²−a` in the last equation. Conversion to the
     natural-number Pell lemmas is made only after establishing the
     nonnegativity of the relevant subtractions.
  5. *The next system uses the alternate Pell formula.* In §5, (D35)
     deliberately uses `G=A+F²(F²−A)`, whereas Theorem 3 uses `D²−A`.
     The remark after Lemma 2.28 explicitly permits the `F²` version;
     this is not a typo. It is also the version that permits the single
     `F²` auxiliary in §5's reported quadratization. The shorter-mask
     proof and the 58-variable, degree-four construction still require
     separate formalization.
  6. *The positive quotient in §5 (D3).* The analogous quotient for a
     general base also is positive: if `2 ≤ B < A` and `L ≥ 2`, then
     `B^L < (B−1)(2B+1)^(L−1) ≤ (B−1)ψ_A(L)`. Combined with
     `χ_A(L) > (A−1)ψ_A(L)`, this makes
     `χ_A(L)−B^L−(A−B)ψ_A(L)` strictly positive. Divisibility by
     `2AB−B²−1` therefore supplies the required positive `α` once
     `Q=B^L` and `C₁=ψ_A(L)` are known in the necessity construction.
     This proves the quotient detail; it does not replace the other
     size and Pell conditions required to eliminate `Q=B^L`.

- **1982, §5 shorter coding and packing (2026-09-14).** The coding stage
  and (D11)–(D18) are now formalized in both directions. These CLAR-level
  notes explain proof details; no new typo or mathematical error was found
  in the checked passages, and no article-source correction is needed.
  1. *The shorter coefficient argument.* With `L=5^(ν+1)`, let
     `D₀(X)=z∑_{i=0}^L X^i−epoly(X)`. The coefficient of `X^L` in
     `−cpoly(X)^4 D₀(X)` is `4!P(zs)`. Its degree is strictly below
     `2L`, and each coefficient has absolute value at most
     `z(1+∑zs)^4`. The index bound and `zs_i<b` make this strictly
     smaller than `B/2` for `B=2b⁴(2z)^(L+1)`. This justifies the
     third carry test with the shorter geometric sum.
  2. *Existence for (D8).* The margin
     `2zB^L−e(B)−2zB l(B)−2zB c(B)^4` has degree at most `L`
     and a strictly positive coefficient at `L`. An explicit cutoff,
     obtained from the sum of the absolute lower coefficients, makes it
     positive for every sufficiently large base. Since `b<B`, this
     implies the printed (D8) with `2zbl`. Arbitrarily large powers of
     two supply `b`, while preserving all digit bounds. The strict degree
     inequality here uses `ν≥1`.
  3. *The top digit in the transfer of `e`.* The polynomial for `e` may
     have a nonzero coefficient at `L`; the valid bound is `e<2zQ`,
     rather than `e<Q`. Applying Lemma 2.9 with `n=m=k=L`, then
     combining the `l` and `e` blocks, proves the second carry
     equivalence with exactly the displayed mask.
  4. *Strictly positive witnesses.* Normalization forces every solution
     tuple to have a positive tail coordinate, giving `g>0`. Both
     transfer polynomials have nonnegative coefficients and a positive
     coefficient at positive degree. Evaluation at `B>2z` is strictly
     larger than evaluation at `2z`; divisibility of their difference
     by `B−2z` therefore gives positive quotients `m,t`, not merely
     nonnegative ones.
  5. *Signed masks and independent packing bounds.* The base formula
     and (D1), (D6)–(D8) give all six strict block bounds before any
     carry test is assumed. The third-block estimate controls
     `|2c⁴D₀|<Q²` without assuming a
     sign for `D₀`. The signed masks consequently convert exactly to
     natural numbers, and the block sizes `Q,2zQ²,8Q²` give
     `N=16zQ⁵` and the central-binomial condition `N²∣C(2R,R)`.
  6. *Sizes before recovering the power.* Positive `λ` and (D7) already
     imply `B≤Q`. Together with the base formula and (D17)–(D18),
     this gives `3<3L≤B≤Q≤N≤R`, `N,R≥8`, and `b≤N,R`.
     This proof does not use `Q=B^L`, so the size prerequisites for
     Lemma 2.26 are available in the eventual converse without a
     circular assumption.
  7. *Scope.* `short_master` and `short_master_packed` retain `Q=B^L`
     and `b=2^w`. They concern a supplied normalized polynomial of
     degree at most four and an admissible coding index. The remaining
     Pell elimination, explicit quadratic system and variable count,
     and representation of arbitrary recursively enumerable sets are
     separate requirements for the universal pair `(58,4)`.
  8. *Correction to an earlier proof note.* The preceding Pell note
     described the branch `B+t₀=C` as excluded by either size or parity.
     Its wording is now corrected: parity excludes it, whereas the size
     condition permits only `A=B=t₀=2`, `C=4`, with the desired index
     unchanged. The existing Lean proof already handles this boundary
     case. This is an error in the explanatory note, not in the article's
     statement or in the proved theorem.

- **1982, §5 Pell elimination and the complete system (2026-09-14).**
  The following proof details accompany the formalization of (D1)–(D37).
  No new article error was identified in these equations.
  1. *The two first-coordinate congruences.* The same construction
     supplies positive quotients in both (D3) and (D30), using the
     general-base and base-two strict Pell estimates, respectively.
     The smaller Pell index is `L=5^(ν+1)`; the larger is `2R+1`.
     The multiplier `w` in `W=bw` is kept separate from the eliminated
     exponent witnessing that `b` is a power of two.
  2. *Converse without circular assumptions.* The coding equations and
     block definitions give `3<3L≤B≤Q≤N≤R` and `N,R≥8` first.
     Positivity and `A=M(U+1)` give `A>1`. Conditions (D31)–(D37),
     with the alternate `F²−A` formula, determine `C=ψ_A(2R+1)`.
     The resulting ratio system has slack `C₁+φ`; it recovers the
     central-binomial divisibility and that `b` is a power of two.
     Its size estimates then identify `C₁=ψ_A(L)` and recover
     `Q=B^L` from (D3)–(D5).
  3. *All intermediate quantities.* The full witness record has
     twenty-six scalar fields outside the twenty-seven-field Pell
     record, exactly the article's fifty-three quantities. All fifty-two
     quantities other than `D₀` are positive in the construction.
     In particular (D8) gives `bl<Q`, so
     `Q−1−(b−1)l≥l>0`, proving the strict positivity of `M₁` and
     `T₁`. The earlier block bounds already give `S₃>0` without
     assuming a sign for `D₀`.
  4. *The rational inequality.* Since `K>0`, (D21) is exactly
     `4(C−KY)²<K²`. The formalization checks this equivalence over
     the rationals and integers, so the cleared inequality adds no
     condition and loses no solution.
  5. *The substitution count.* Eliminating the seventeen named
     quantities leaves thirty-six variables. Nineteen of the twenty-two
     auxiliaries have separate defining equations; the remaining three
     replace the two inequalities and the square predicate. The resulting
     system has forty-six equations. With `z,u,y,L` fixed, all residuals
     are quadratic, including their dependence on `x`. The signed term
     in `S` is `−4z(c⁴Q³)[z(λ+Q)−e]`, explaining the auxiliary
     `c⁴Q³`. Solvability preservation through these substitutions is proved
     separately from the count and degrees; current Lean coverage is
     recorded in `Lean/STATUS.md`.
  6. *Normalization without an extra witness.* Shift every one of the
     fifty-eight witness variables by one, leaving the input unchanged.
     This preserves the quadratic and quartic degree bounds. At the zero
     shifted witness tuple, the (D9) residual is `2z−u`, independently
     of the input. For an admissible index and `ν≥1`, the first term
     in `u` gives `(2z)^5≤u`, and `2z≥4` gives `2z<u`. The sum of
     squares is therefore nonzero at that tuple for every integer input.
     This proves the normalization property without a fifty-ninth
     witness. The solvability correspondence with the original fifty-three
     quantities requires the separate constructions described next.
  7. *Positivity through the substitutions.* In the forward construction,
     the size chain and (D23)–(D24) give `B≤R≤M<A`, hence the auxiliary
     `2AB−B²−1` is positive. The two strict inequalities give positive
     integer slacks `ξ` and `η`; the square in (D20) is at least one,
     so the absolute value of its integer square root gives positive `τ`.
     In the converse, first recover `Q=1+λ(B−1)>0` from the `λB`
     auxiliary and `B>0`. The numeric packing bounds then justify each
     conversion of an eliminated signed expression to a natural witness.
     No sign is assigned to `D₀`, and no Pell power or carry condition is
     assumed while reconstructing those bounds.
  8. *Ordinary nonnegative polynomial witnesses.* The shift is a bijection
     between natural witnesses `v` and positive natural witnesses `v+1`;
     the inverse is `v−1`, justified by positivity. Renaming the input
     and witness coordinates as `Fin 59` preserves input coordinate zero.
     Combining these facts with the two substitutions gives the explicit
     normalized 58-witness quartic for every supplied normalized quartic
     and every positive input. This is a compression theorem; representation
     of arbitrary recursively enumerable sets is a further obligation.
  9. *Supplying the initial quartic.* The proved 1978 enumeration reduces
     any Diophantine set to some `W_n` on positive inputs. Retaining the
     first `3(n+1)` integer evaluation nodes yields finite addition and
     multiplication equations. The extra final group handles `n=0`
     uniformly. Split each node into a difference of two natural witnesses
     and add one guard witness constrained to equal one. The squared
     residual sum has degree at most four and `6n+7` natural witnesses;
     its guard residual is `−1` at the zero witness tuple. Applying the
     §5 compression therefore covers any Diophantine set, with no initial
     degree or variable bound. The claim that every recursively enumerable
     set is Diophantine remains a separate theorem, not an assumption.

### Formalization adapter notes — 2026-09-14

- **Axiom policy clarification.** The project owner permits obvious elementary
  facts that a paper would leave entirely unargued to be explicit axioms,
  in addition to the previously permitted well-known pre-1950 external
  theorems. Positivity and integrality of a central binomial coefficient
  are the stated example. Any such dependency will be recorded in the
  formalization status. The current adapter batch introduces no project
  mathematical axiom.
- **Polynomial representation boundary.** Mathlib's `Dioph` definition uses
  integer-valued polynomial functions on natural tuples, with a witness
  index type that need not be finite. Conversion to the articles' finite
  polynomial convention must first restrict to the finitely many witness
  coordinates occurring in the polynomial. Input coordinates are retained;
  unused witnesses can be extended by zero. For a single input, the final
  renaming puts it at coordinate zero. This adapter concerns two definitions
  of Diophantine representation; it does not supply the separate theorem
  that recursively enumerable sets are Diophantine. Compilation and proof
  dependency receipts are recorded in `Lean/STATUS.md`.
- **Proof-comment correction.** In `Paper1978/Godel.lean`, the docstring for
  `S_eq_P` said `k ≤ 3n+1`, while the actual theorem and proof use
  `k ≤ 3n−1`. The comment now matches that bound. Recursions are supplied
  only for `i<n`, so the next addition and multiplication nodes, `3n` and
  `3n+1`, are not generally covered. This corrects a Lean explanation,
  without changing the theorem or an article equation.

### Recursively enumerable representation and uniformity — 2026-09-14

- **Proved computability input.** The finite-support adapter above is now
  complemented by a proof that every Mathlib `REPred` on natural numbers
  is Diophantine. Primitive recursion is represented by an exact finite
  trace whose state contains the fixed parameter, counter, and current
  value. A fixed semidecider code and its primitive-recursive bounded
  evaluator then reduce successful execution to one existential bound.
  This proves the representation theorem, including input zero; it does
  not introduce a DPRM axiom. The sparse-cipher trace proofs are vendored
  from a pinned ProveIt revision with their license, source hashes, and
  mathematical provenance retained.
- **One universal polynomial.** A polynomial chosen separately for each
  recursively enumerable set does not by itself express the universal
  equation defined near the start of the 1982 article. Apply the §5
  compression again to the resulting 58-witness quartic. The second
  application has the globally fixed exponent `L4 58 = 5^59`, so only the
  three index parameters vary with the represented set. The formalization
  proves that all 46 residuals depend polynomially on those parameters,
  constructs one joint integer polynomial, and proves literal equality
  between its parameter specializations and the explicit quartic family.
  The resulting theorem chooses this polynomial before choosing the set.
- **Degree and domains.** As expressly stated in §5, the quartic degree
  counts the input and the 58 witnesses after the three index parameters
  have been fixed. No degree-four bound is asserted for all 62 joint
  indeterminates. The witness shift yields natural witnesses; the three
  selected parameters are positive. Membership equivalence is restricted
  to positive inputs, while normalization also holds at zero. The printed
  Theorems 1–3 use their different exponent `5^60` and exactly 12, 14, and
  28 positive witnesses. One coding triple works for all three systems
  and every positive input of the represented set.
- **Editorial classification.** These are explicit proof and statement
  boundary clarifications. No additional error in the article equations
  was found in this batch, and no article TeX or PDF was changed. The
  compilation and transitive axiom receipts are recorded in
  `Lean/STATUS.md`; the other unfinished article arguments remain separate.

### Relation combining and the twelve-variable prime polynomial — 2026-09-14

This entry records the initial common-weight milestone. Its then-open
refinements are addressed in the later entry below; its validation receipt
remains historical.

- **Updated axiom policy.** The project owner expanded the cutoff from
  1950 to 1980: well-known theorems proved before 1980 may now be explicit,
  cited axioms, alongside the already permitted obvious elementary facts.
  This supersedes the earlier cutoff recorded in the adapter notes.
  Completed proofs are retained. The present relation-combining and
  twelve-variable construction introduces no mathematical axiom.
- **The cited theorem is proved.** The shared formalization constructs the
  Matijasevič–Robinson polynomial as the product over all independent sign
  choices, using `W = 1 + Σ Aᵢ²`. Sign changes permute the factors, so all
  radical exponents are even. Explicitly halving those exponents gives an
  ordinary polynomial with integer coefficients. The evaluation and
  substitution identities are proved separately from its arithmetic
  meaning. The theorem permits signed integer radicands, dividend, and
  positivity parameter; only the divisor is required to be nonzero.
- **Repeated square classes and zero roots.** The necessity argument uses
  rational automorphisms of the algebraic closure of the rationals.
  Each root is mapped to itself or its negative. If the weighted sum is
  rational, the changed roots have weighted sum zero; norm separation
  forces each changed root to vanish. Consequently every root is fixed
  and rational, and a rational square root of an integer is integral.
  This does not assume independent square classes. Complex norms cover
  negative radicands, and zero roots are handled explicitly. The empty
  family has one sign assignment and reduces to the arithmetic theorem
  with positive offset 1.
- **The rational inequality keeps its domain.** Eliminating the capital
  letters of 1976 Theorem 3.9 leaves the ten natural witnesses
  `n,x,w,m,i,j,p,l,r,z`. Set
  `d = (C−(w+1)xKL)(C−R)²` and `a = RKC²`. Under the other system
  hypotheses, the defined rational inequality (XIV) is equivalent to
  `d²−4(a−(S+1)d)² > 0`. Strict positivity forces `d ≠ 0`, so clearing
  the denominator does not admit either undefined case. Every eliminated
  expression uses integer subtraction. The divisor `F` is positive on
  every natural assignment, before imposing the square conditions.
- **Existence and the sharper degree are distinct.** Applying the proved
  six-square combining theorem and the device `(k+2)(1−M²)` constructs an
  actual `MvPolynomial (Fin 12) ℤ`. Its positive values on natural
  assignments are exactly the primes. The reduced criterion is used at
  parameter `k+1`, including prime 2 when `k=0`. This establishes the
  twelve-variable assertion, but not the printed degree 13697. The
  refined individual weights and the five-square growth replacement (24)
  remain separate formal obligations. In particular, that replacement
  supplies the growth bounds used by the proof and is not itself the
  second original `U` square test. The source-derived degree bookkeeping
  and required interface changes are retained in
  `Lean/RELATION_COMBINING_FRONTIER.md`, explicitly distinguished from
  Lean degree certificates.
- **Editorial classification.** No new error in the six article equations
  was found in this batch. These notes make the proof, domain, and degree
  boundaries explicit. No article TeX or PDF was edited by this
  formalization batch; upstream 1980 article updates remain a separate
  contribution. The build and axiom-audit receipts are in `Lean/STATUS.md`.

### Refined relation combining, exact-degree primes, and Theorem 3 — 2026-09-14

The refined degree and application proofs pass the consolidated Lean
build and transitive axiom audits. The completed receipt is in
`Lean/STATUS.md`; it supersedes the focused checks for this milestone.
The earlier common-weight receipt remains evidence for its own source state.

- **Individual polynomial weights.** The refined signed product uses
  prefix products of independent weights and the unsquared divisibility
  parameters. Its arithmetic theorem requires a positive divisor and a
  nonnegative dividend, which hold for `F` and `H-C` on every natural
  assignment. The root bounds also hold on every natural assignment,
  including those where the capital expressions `K,L,R,G` are negative.
  Polynomial majorants replace absolute values without adding unknowns.
  Signed and repeated radicands, zero roots, and the empty family remain
  covered by the automorphism and norm-separation argument.
- **The five-square replacement.** Equation (24) has coprime factors and
  supplies the two growth bounds used by Theorem 3.9. Conversely, the
  second Pell equation supplies arbitrarily large admissible `x` for each
  admissible `n`. The refactored necessity theorem constructs the remaining
  witnesses for supplied `n,x` satisfying the growth bounds. The replacement
  is not identified with the old second square condition. The criterion
  retains ten natural witnesses; relation combining adds one witness, and
  the prime parameter gives twelve natural coordinates. The shift of the
  article parameter includes prime 2 at outer coordinate zero.
- **Bounds for the unpadded polynomials.** The generic degree calculus
  counts polynomial coefficient degrees as well as weighted radical
  exponents, then transports the bound through exponent halving. The
  concrete six-square combined and prime-polynomial bounds are 13376 and
  26753; the five-square bounds are 6848 and 13697. These are upper bounds
  for the stated unpadded constructions. The older common-weight estimates
  148864 and 297729 remain source-derived calculations in
  `Lean/RELATION_COMBINING_FRONTIER.md`.
- **Literal exact-degree existence.** For the five-square combined
  polynomial `M`, set `e=6848-M.totalDegree` and multiply `M` by
  `(X 11+1)^e`. This factor is positive on every natural assignment, so it
  preserves the natural zero set. The combined polynomial is nonzero,
  since otherwise its prime-value theorem would make 4 prime. Exact degree
  of nonzero products gives degree 6848 after padding and degree 13697 for
  the resulting prime polynomial. This supplies a separately defined
  construction for the article's existence assertion, with the same
  positive prime values and no new coordinate. Equality for the unpadded
  `M` is not asserted, and the padding may have exponent zero.
- **Theorem 3's discrete zero test.** Squaring the five-square combining
  polynomial gives an exponent nonnegative on every natural assignment.
  The formula `2 + k * 0^M` therefore has an ordinary natural exponent:
  `0^0=1` returns `k+2` on successful tests, while positive exponents
  return 2. The parameter-zero case also returns 2 for arbitrary
  witnesses. `PrimeZeroTest.lean` packages the exact prime range with
  eleven auxiliary natural variables; it passes the same build and
  transitive axiom audit.
- **Editorial and validation boundary.** No new error in the article
  equations was found by this source review. These additions record the
  growth interface, unconditional bounds, and exact-degree construction.
  This milestone edits no article TeX or PDF and claims no PDF rebuild.
  The parallel 1980 formalization and certificate work remain separate.
  The build passed 3579 jobs; all 87 audited declarations use only
  Lean's standard logical axioms. Detailed results are in `Lean/STATUS.md`.

### MRDP and further 1976 proofs — 2026-09-14

- The public Lean theorem `Diophantine.mrdp` now states MRDP as existence
  of one integer polynomial with finitely many natural witnesses. Both
  the polynomial and the witness dimension are chosen before the input;
  membership at zero is included. The difficult direction was already
  proved by the finite-trace and bounded-evaluator development. The
  finite-support adapter gives the explicit polynomial, and a new
  primitive-recursive witness search proves the converse. The full
  equivalence is `Diophantine.mrdp_iff`. See the
  [proof guide](../Lean/MRDP.md) and the dated
  [validation register](../Lean/STATUS.md). No new axiom is introduced.
- The 1976 Theorem 4 now follows from a proved Diophantine graph of the
  nth prime and the proved Putnam construction. The one-based source
  indexing is `Nat.nth Nat.Prime (n - 1)`, and the theorem applies at
  positive input indices. The additional fourteen-witness refinement
  is a separate remaining obligation.
- Theorem 4.1 retains its full complex coefficient field. The Lean proof
  supplies the rational-coefficient descent and clears a positive common
  denominator `l`. It uses the prime `p` at the origin and congruence
  modulo `l*p`, cancelling `l` in the integers before invoking primality.
  This avoids assuming that `l` and `p` are coprime. Using the origin in
  place of the article's all-ones assignment changes only the proof's
  base point. No article error or source correction was required.
- The 1976 Theorem 5 is proved using the certificate of
  `verification/jones1976_primality87.json`: an acyclic
  schedule with 30 addition, 10 subtraction, and 47 multiplication
  assignments is verified by 40 additions and 47 multiplications.
  Each subtraction is checked by addition in the reverse direction.
  Lean proves the final comparisons equivalent to Theorem 2.12 and
  primality equivalent to existence of a valid certificate, including
  the prime 2. Equality/domain checks, fixed numerals, and certificate
  reading remain uncharged, as in the existing editorial convention.
  All 87 schedule instructions and fourteen system comparisons match
  the JSON source. The article statement needs no further correction.
- These additions do not alter the agreed 1980 scope: Theorem 5 remains
  intentionally excluded, and Theorem 4 remains abridged to `(58,4)`.
  No article TeX or PDF is changed by this milestone.

### Environment notes for reproducing these results

- **1980 satellite, certificate optimization (2026-09-14).** The original
  129-instruction schedule remains reproducible. Sharing `UM`, with
  `U=wn²` and `M=rsn²`, between `a=UM+M` and `p=2(UM)M` saves one
  multiplication. The new 128-instruction schedule has 74 multiplications,
  54 additions (including reversed subtractions), and 20 equality tests.
  The checker verifies every residual as an exact polynomial identity.
  The satellite's unsupported suggestion that rewriting could not close
  the gap to 100 has been replaced by an explicit upper-bound statement.
  A second milestone checks 127 instructions for the original system,
  126 after a positive-slack reparameterization justified by Pell spacing,
  and 123 after recoding the radix and splitting the original inequality.
  The optimized checker records the exact triangular E7 residual identity,
  both slack substitutions, and complete lists of primitive addition and
  multiplication checks. The recoding proof explicitly establishes the
  bounds for exponent elimination without assuming its conclusion.
  The final packed recoding reduces this further to **120 instructions**:
  68 multiplications and 52 additions, including 18 reversed subtractions.
  It replaces the bound by `e l C²<q²`, sharing `C²` with the fourth power
  already used in E7, and replaces the two coefficient congruences by
  `e+lq²=V+tθ`, where `V=y+uZ^(2L)` belongs to a fixed admissible index.
  The strengthened bound supplies `q>C>B` before applying the Pell lemmas;
  Lemma 2.9 and the unique quotient/remainder split recover both original
  coefficient codes. There are again 32 positive witnesses, 20 equations,
  and three fixed index parameters besides the input. The article includes
  the full proof and a generated 120-instruction appendix. All primitive
  statements and all residual identities are checked symbolically;
  positive-domain and decoding arguments are mathematical proofs, not
  claims of Lean formalization. The literal-numeral variant takes 131
  instructions when only `2,4,5,5^59` must be constructed from 1 and the
  admissible index remains supplied. The earlier claim that choosing Pell
  base `b` saves an operation over an already computed `b^5` was corrected:
  both have the same basic cost with the shared modulus identity.
  The next verified milestone is **119 instructions** (68 multiplications,
  51 additions). The alternate Pell parameter allowed after Lemma 2.28,
  `G=a+f²(f²-a)`, factors as `G-1=(f²-1)(f²-a+1)` and reuses E16 and
  E20 intermediates. Its checker records the exact additional triangular
  E17 residual identity. The proof explicitly constructs positive
  `I=χ_G(2r+1)` and `H=ψ_G(2r+1)`, so that the congruence quotients
  `o` and `j` are positive; it does not assume positivity of the source's
  unspecified integer `I` or silently change a positive domain to signed.
  The composed successor reaches **114 instructions**: 63 multiplications
  and 51 additions, with 33 positive unknowns and 21 equality tests. The
  normalization `R=24S+z(sigma-1)` makes the leading coefficient digit zero
  without changing the represented set; `z` is a power of two, so the
  alternative `24S=z` is impossible modulo 3. The new bound `e+lC^4<q`
  permits packing by `q` and `n=q^8`, saving two instructions. The signed
  parameter `G=1+(a+1)(f^2-1)` with `(of-d)^2` saves two more. Finally,
  `c=ksn^2+eta`, `k=eta+zeta` saves two and adds one positive unknown
  and one equation. Its proof establishes both exponential relations
  before parity rounding, then uses the positive binomial tail to prove
  that `eta` and `zeta` are strictly positive. The final exponent
  `L=5^64` satisfies all mask bounds and requires nine literal-construction
  instructions for `2,4,5,L`, giving 123 with that additional requirement.
  `round5_1980_certificate.py` verifies all primitive checks and all 21
  residuals, including the triangular E7 and E17 corrections. Its full
  JSON receipt and generated 114-instruction appendix preserve the exact
  arithmetic evidence; the new mathematical equivalence proofs are not
  claimed to be Lean formalizations or optimality results.
  The next two independent reductions compose to **112 instructions**:
  62 multiplications and 50 additions, with 32 positive unknowns and
  20 equality tests. Directly testing the quadratic residuals allows
  `B=Hb^2` and a code square instead of a fourth power. The same sparse
  mask selects true witness digits and separated equation targets;
  support inequalities prove that arbitrary extra code coordinates do
  not contaminate the target coefficients. Explicit quadratic Sidon
  weights distinguish all 1830 monomials and permit `L=5^16`. This gives
  an independent 113-operation scheme and seven numeral instructions.
  Separately, use the mathematical Pell parameter `P=1+2UM^2` and compute
  its coefficient as `X(X+2)`, where `X=2UM^2` is already available.
  The old `p-1` subtraction, `p` witness, and defining equality disappear.
  The perturbed ratio error is bounded before using parity, and the
  positive binomial tail proves both interval slacks remain positive.
  `round6_1980_certificate.py` verifies their composition, all 112
  primitives, 20 residuals, both triangular identities, and fixed support
  inequalities. The optional seven numeral instructions give 119. The
  satellite contains both complete arguments and the generated final
  112-instruction appendix, with all earlier milestones preserved.
  Reversing the packed code to `Y=l+eq` and shortening the dense baseline
  gives **111 instructions**: 61 multiplications and 50 additions, with
  33 positive unknowns and 21 equality tests. The size bound becomes
  `Y+C^2+alpha=q^2`, removing one multiplication. The packing widths are
  two, two, and four powers of `q`; a positive unknown `sigma=S3` enforces
  the third block's sign through a free equality. A possible first-block
  borrow is removed before decoding. The remaining ambiguity
  `l=l0+mq`, `e=e0-m` is eliminated by the high mask: its digit polynomial
  evaluated at 2 is divisible by `B-2` and smaller than `B-2`, so `m=0`.
  The enlarged fixed index is independent of the input. The complete
  mathematical proof is `1980/REVERSED_PACKING_PROOF.md`; the exact
  `round7_1980_certificate.py` checker verifies all 111 primitive checks
  and 21 source residuals, including the changed E7 triangular correction.
  An independent implementation, `affine_reverse_pack_check.py`, agrees.
  Seven numeral instructions give 118 with that additional requirement.
  The satellite now includes the complete argument and generated
  111-instruction appendix. The deterministic carry regression
  `round7_1980_reversed_checks.py` checks 158,834 high digits across
  31,898 quotient trials and rejects all 31,571 tested nonzero quotients
  under its hypotheses. A negative control exhibits a surviving quotient
  when the exponential scale hypothesis is omitted. These finite checks
  supplement the general mathematical proof. This extends the mathematical
  and arithmetic evidence, not the Lean formalization.
  The next verified reduction reaches **110 instructions**: 61
  multiplications and 49 additions, with the same 33 positive unknowns
  and 21 equality tests. Homogenize the encoded quadratics with a digit
  `delta`, add an encoded guard `u*delta-x^2=0`, and add a special target
  `delta^2`. Changing the third mask to `(B-4)l` permits target values
  zero and one; ordinary targets are even, so they must be zero. The
  special target and positive input force `delta=1`, removing the
  explicit addition of 1 from `C=xB+g`. The high quotient test now
  evaluates its digit polynomial at 4, with a stronger fixed scale.
  The complete proof is `1980/UNIT_DIGIT_PROOF.md`; the exact
  `round8_1980_certificate.py` checker verifies all 110 primitives,
  21 residuals, and the expanded Sidon layout. Seven numeral operations
  give 117. The new code coordinates remain inside the fixed encoding,
  and do not add polynomial-system unknowns. Article integration is
  in progress; the previous 111-operation article and table are preserved.
  Moving the input to weight zero and the decoded unit to weight one
  then gives **109 instructions**: 60 multiplications and 49 additions.
  The code is `C=x+g`, removing its multiplication by `B`; all 33
  positive unknowns and 21 equality tests are retained. The earlier
  preliminary inequality `B<q` is replaced by the geometric consequence
  `B<=q^2<=n`. The full Pell dependency audit proves this is sufficient:
  `B^(3L)<=B^B<=n^n` supplies the same exponent bound, and `q=B^L`
  is recovered before the digit arguments need `B<q`. The remapped
  special target is at `t_special-2`, and the input is exactly the
  unit digit because the first mask forces the unit digit of `g` to zero.
  The complete proof and audit are `1980/INPUT_UNIT_PROOF.md` and
  `1980/PELL_RELAXED_RADIX_PROOF.md`; `round9_1980_certificate.py`
  verifies every primitive, residual, and support bound. The optional
  numeral construction gives 116. Article integration follows separately.
  Positivity of an existing computed coefficient gives **108 instructions**:
  60 multiplications and 48 additions. Introduce the positive witness
  `Omega=Z*lambda-2e` through a free equality, reverse that subtraction,
  and write `S3=B*lambda*(1+q)-Omega*C^2`. The positive `sigma=S3`
  first implies `C<q^2`, enough for the wider first packing block.
  After the unchanged Pell step gives `q=B^L`, it implies `C<q` before
  decoding. Thus `Y+C^2+alpha=q^2` can become `Y+alpha=q^2`, removing
  one addition. There are now 34 positive unknowns and 22 equations.
  `1980/POSITIVE_COEFFICIENT_BOUND_PROOF.md` proves both directions;
  `round10_1980_certificate.py` checks the full arithmetic and residuals.
  Seven numeral instructions give 115. Independent reviews checked the
  weaker preliminary bound and the later recovery of the stronger one.
  An independent **108-instruction** variant uses 59 multiplications
  and 49 additions, retaining the 109-stage 33 positive unknowns and
  21 equations. Write `Q=UM^2`, already computed, and replace the odd
  Pell root by `tau_old=2*tau+1`. The norm becomes
  `tau*(tau+1)=Q*(Q+1)*k^2`; weaken the index equation to
  `k=r+1+h*Q`. A growth argument still forces the exact index `r+1`,
  which proves `h` even and restores the old positive witnesses.
  The computation of `2Q` disappears. The proof is
  `1980/PELL_ODD_ROOT_PROOF.md`; the complete checker and receipt are
  `round11_1980_pell_certificate.py` and its adjacent JSON. Both exact
  polynomial witness maps are checked, while the positive inverse and
  its evenness follow from the independent mathematical index proof.
  These independent reductions compose to **107 instructions**:
  59 multiplications and 48 additions, with 34 positive unknowns and
  22 equality tests. The positive-coefficient bootstrap first supplies
  `r>=n>=8`; the odd-root argument then restores the old positive Pell
  witnesses, after which the coefficient proof completes decoding.
  The necessity maps act on disjoint witnesses and commute. The complete
  composition argument is `1980/COMPOSED_107_PROOF.md`, and
  `round12_1980_certificate.py` directly checks all 107 primitives,
  22 source residuals, triangular corrections, and polynomial witness maps.
  Seven numeral operations give 114. All earlier certificates remain
  reproducible. The satellite now integrates the 110-, 109-, and two
  independent 108-operation arguments, the 107-operation composition,
  and complete generated tables for 110, 109, and 107. Its final
  Theorem 5 statement includes the 107-operation certificate form.
  A further encoding improvement keeps the core count at 107 and reduces
  the count with all literal numerals generated from 1 to **113**. Use
  `v_i=1+3(122i+(i^2 mod 61))`, whose pair sums are unique by recovering
  their sum and product over the field of 61 elements. The new support
  has `K=316719071`, so `L=2^32>3K+2` suffices. Sharing the existing
  `a-1` register in `4(a-1)-1` eliminates literal 5 without changing the
  core cost; one doubling and five squarings construct the remaining
  numerals. The proof is `1980/MODULAR_SIDON_PROOF.md`, and
  `round13_1980_certificate.py` checks both the 107-step core and the
  complete 113-step certificate, including all 1891 monomial weights,
  all support margins, and every primitive and residual identity.
  The six-operation numeral variant has not yet been integrated into
  the rendered satellite article.
  A further main-Pell change gives **106 core operations**, comprising
  59 multiplications and 47 additions, with the same 34 positive unknowns
  and 22 equality tests. Supply `a0=RY(U+1)`, use mathematical parameter
  `A=a0+4`, and impose the base-four exponent congruence for
  `bw=4^(2r+1)`. Then `A-4=a0` needs no subtraction, while
  `A-B=a0-(B-4)` shares the existing mask factor. The new Pell ratio lies
  above the binomial expression; the proof establishes `a0>R U^R`
  before either exponent test and recovers the integer part directly.
  Necessity rechooses `w=4^(2r+1)/b` and every dependent Pell witness.
  The proof is `1980/MAIN_PELL_BASE_FOUR_PROOF.md`, and the complete
  checker `round14_1980_base_four_certificate.py` verifies all shifted
  source residuals, triangular corrections, and primitive identities.
  Its initial numeral-generating certificate has 115 operations; the
  separate 107-core/113-total variant remains the better strict bound.
  The 106-operation article integration is in progress.
  An equivalent arrangement reduces that variant's numeral cost by one:
  compute `A+1=a0+5`, then `A-1=(A+1)-2`, and express its modulus as
  `8(A+1)-25`. With the same modular support and the larger admissible
  exponent `L=5^16`, eight operations construct every required numeral,
  yielding 106 core and 114 total operations. The exact proof and complete
  checker are `1980/BASE_FOUR_NUMERAL_VARIANT_PROOF.md` and
  `round15_1980_certificate.py`. This does not supersede the separate
  113-total certificate.
  The optimization measure has now been explicitly fixed to give
  **numerals no cost**. Earlier numeral-construction experiments remain
  reproducible historical artifacts, but are not further optimization
  targets. The next core reduction gives **105 arithmetic operations**:
  59 multiplications and 46 additions. Set `M=(R+1)Y`, so the first
  Pell parameter satisfies `P-1=2U(R+1)^2Y^2`, and replace
  `K=R+1+hQ` by `K=h(R+1)`. The index is a positive multiple of `R+1`;
  growth and the positive interval exclude every multiple after the first.
  The larger scale preserves the ratio bounds, and necessity supplies
  `h=psi_P(R+1)/(R+1)` as a positive integer. Moving the existing `r+1`
  register removes exactly one addition. The proof is
  `1980/PELL_INDEX_MULTIPLE_PROOF.md`; the complete checker is
  `round16_1980_index_multiple_certificate.py`. It verifies all 105
  primitives, the three changed source equations E9/E11/E12, every other
  unchanged source residual, and both triangular corrections. There are
  still 34 positive unknowns and 22 equality tests. The proof has passed
  independent mathematical review. The 77-page satellite now integrates
  the smaller modular support, the 106-operation shifted main parameter,
  and the 105-operation index-multiple proof, with complete generated
  tables for both recent core reductions. It was rebuilt with two serial
  pdfLaTeX passes; the final pass has no reference or layout warnings.
  All 77 rendered pages were reviewed in contact sheets, and the new
  mathematical sections, final theorem, and 105-step table were inspected
  at full size. Fixed numerals are explicitly free in the new statements.
  An independent scale choice `M=Y` removes one multiplication from the
  base-four 106-operation construction, giving 105 operations with
  58 multiplications and 47 additions. Its proof uses the previously
  unused packing upper bound `R<2N^3` before identifying the Pell indices.
  It establishes `A>U^(R+1)` before exponent decoding and only invokes
  the small ratio error after deriving `bw=4^(2R+1)`. The proof and
  checker are `1980/PELL_UNIT_SCALE_PROOF.md` and
  `round18_1980_unit_scale_certificate.py`.
  This exposes a further shared product, giving **104 operations**:
  57 multiplications and 47 additions. For `Q=UY^2`, rewrite the first
  norm as `Q(Q+1)k^2=((UY)^2+U)(Yk)^2`; both `UY` and `Yk` are already
  required. Replace its index modulus `Q` by `UY`. Since `UY>=N^4>R+1`,
  the exact-index argument remains valid and recovers positive inverse
  witnesses. The separate `Q` register disappears from the whole
  schedule. Only E11 changes as a source polynomial. The proof and
  complete checker are `1980/PELL_SHARED_RATIO_PRODUCT_PROOF.md` and
  `round19_1980_shared_ratio_product_certificate.py`. Mathematical
  reviews and all exact primitive, residual, and witness-map checks pass.
  The system retains 34 positive unknowns and 22 equality tests.
  The 85-page milestone included the complete unit-scale and shared
  product proofs in Section 18, the 104-operation case of Theorem 5,
  and its complete generated instruction table in Appendix K. The
  generator `round19_1980_schedule_table.py` reruns the exact checker
  before emitting all 104 instructions and 22 equality tests. Two serial
  PDF builds pass without warnings; all 85 pages were rendered and
  reviewed in contact sheets, with pages 44--50 and 83--85 inspected
  at full size. Fixed numerals have no cost.

  A new coefficient encoding removes the low `B*lambda` offset from
  `S3`, yielding **103 operations: 57 multiplications and 46 additions**.
  Replace ordinary targets by `4F_i^h+delta^2` and retain the special
  `delta^2` target. The incoming normalization carry is -1 or 0, so
  valid target digits are 1 or 2; the same four-value mask forces the
  decoded unit and every quadratic equation. The new high-digit proof
  eliminates the quotient alias with the existing H margin. The proof
  is `1980/SINGLE_OFFSET_ENCODING_PROOF.md`, independently supplemented
  by `1980/HIGH_MASK_SINGLE_OFFSET_PROOF.md`. The complete
  `round20_1980_borrow_mask_certificate.py` checks all 103 primitives,
  all 22 source residuals and both triangular corrections; only E7
  and the positive S3 equation change. The support and 34-positive-
  unknown count remain unchanged; the fixed coefficient index is rebuilt.
  A separate deterministic regression checks 144 integer examples,
  648 high digits and 576 rejected nonzero aliases, without replacing
  the universal mathematical proof. Article integration is in progress.

  Independently, share the exponential witness and binomial scale as
  `U=W=Bw`, and use the already computed norm coefficient `U(Q+1)`
  as the first index modulus. This gives **103 operations**, now with
  56 multiplications and 47 additions. The coding equations imply that
  R is even before exponent decoding; this makes R+1 odd and supplies
  both congruences needed for the positive CRT quotient h. The proof
  recovers the exact index using the signed congruence modulo Q+1,
  delays the ratio error estimate until U=4^(2R+1), and restores
  `N^2|U` only after the two exponent relations. Full proof and checker:
  `1980/PELL_SHARED_EXPONENT_PROOF.md` and
  `round21_1980_shared_exponent_certificate.py`. Independent reviews
  and the exact checker pass; only E9, E11, E12 and E14 change.

  A simpler way to share the exponent target keeps `U=wN^2` and the
  existing index modulus UY, and changes only E14 to use W=U. The
  recovered relation `U=4^(2R+1)` makes N and q powers of two; after
  `q=B^L`, B and b are powers of two as well. Necessity uses the
  positive integer `w=4^(2R+1)/N^2`. This needs neither the parity nor
  the CRT argument of the independent alternative above. Its proof is
  `1980/PELL_COMMON_WITNESS_PROOF.md`.
  Combined with the borrow-tolerant coefficient targets it gives
  **102 operations: 56 multiplications and 46 additions**. The complete
  positive-domain composition proof is `1980/COMPOSED_102_PROOF.md`.
  The checker `round22_1980_composed_certificate.py` verifies all 102
  primitives, 22 residuals and both triangular corrections, and proves
  that both orders of the arithmetic and source-equation changes agree.
  Three independent reviews and the exact checker pass. The system
  retains 34 positive unknowns and three fixed index parameters besides
  x. The 98-page satellite now integrates the full borrow-tolerant
  coefficient proof and common-witness Pell proof in Sections 19 and 20,
  adds both cases to Theorem 5, and includes the complete 103- and
  102-instruction tables in Appendices L and M. Both table generators
  rerun their exact checkers. Two serial final PDF builds pass without
  warnings; all 98 pages were rendered and inspected in contact sheets,
  with pages 49--57 and 93--98 inspected at full size. Fixed numerals
  remain free.

  Compiling arbitrary coefficient equations into finite primitive circuit
  rows permits the targets `2F+delta^2`, whose divided coefficients lie
  in `{-2,-1,0,1}`. Centering at two gives canonical digits 0 through 3,
  so the digit parameter can be fixed at `Z=4`. A dynamic ternary
  support layout and a set-dependent power-of-two length L accommodate
  every finite circuit. The index is still three integers, now `(V,H,L)`;
  the circuit coordinates are digits of the existing code. The existing
  `theta=B-4` replaces the separately computed mask/exponent shift,
  giving **101 operations: 56 multiplications and 45 additions**, with
  34 positive unknowns and 22 equality tests. The full proof is
  `1980/FIXED_FOUR_ENCODING_PROOF.md`; three independent mathematical
  reviews pass. The standalone checker
  `round23_1980_fixed_four_certificate.py` verifies all 101 primitives,
  all 22 residuals, and the three triangular corrections induced by the
  reused theta and the shared norm expression. Its finite support,
  normal-form and carry regressions supplement the general proof.
  The 105-page article integrates the full fixed-four proof in Section 21,
  its additional case of Theorem 5, and all 101 instructions and 22 free
  equality tests in Appendix N. The generator reruns the standalone
  checker. Two serial final PDF builds pass without warnings. All 105
  pages were rendered and reviewed in contact sheets; the title/abstract,
  pages 56--59 and 61, and all three new table pages 103--105 were also
  inspected at full size. Fixed numerals remain free.

  Two independent refinements give **100 operations**. The doubled-index
  Pell construction uses `v=of-d^2`, `K=(A^2-1)(f^2-1)` and the norm
  `v(v+1)=K(K-1)(2r+1+jc)^2`. Replacing the fixed length parameter by
  `T_L=psi_4(L)` permits the index equation `kappa=T_L+Delta*a`.
  Together these remove the last uses of `A-1,A+1`, so the norm coefficient
  can be calculated as `a^2+(8a+15)` with its existing exponent modulus.
  The result is 56 multiplications and 44 additions. Full proof and exact
  checker: `1980/PELL_DOUBLED_INDEX_PROOF.md` and
  `round24_1980_doubled_pell_certificate.py`.

  Independently, replace the positive coefficient by `2lambda-e` and the
  third-block offset by `theta*lambda*q`. Paired primitive rows, two unit
  constraints and a first special target preserve exact circuit decoding
  with the halved raw coefficients. The modified high-window proof still
  excludes every quotient alias under the same index bound. Sharing the
  geometric factor replaces eight instructions by seven, giving 55
  multiplications and 45 additions. Full proof and exact checker:
  `1980/HALF_CENTER_ENCODING_PROOF.md` and
  `round25_1980_half_center_certificate.py`. Both constructions retain
  34 positive unknowns, 22 equations and three fixed index parameters;
  independent full mathematical and arithmetic reviews pass.

  The two refinements compose to **99 operations: 55 multiplications and
  44 additions**, with the same 34 positive unknowns and 22 equations.
  Construct V,H using the paired, special-first circuit encoding and
  supply `Tindex=psi_4(L)` as the third fixed index component. The complete
  proof `1980/COMPOSED_99_PROOF.md` verifies the combined bootstrap,
  exact indices, radix recovery, revised high-window decoding and all
  positive witnesses in a noncircular order. The standalone checker
  `round26_1980_composed_certificate.py` verifies all 99 primitives,
  all 22 residuals and three acyclic corrections, and checks that both
  full schedule and source transformations commute. Independent full
  mathematical and arithmetic audits pass. This is an upper bound under
  the free-numeral measure, with no optimality claim.

  The 124-page article integrates both 100-operation proofs and their
  99-operation composition in Sections 22--24, with the three complete
  instruction tables and all equality tests in Appendices O--Q. The
  generator reruns all three exact checkers. Two serial final PDF builds
  pass without warnings. All 124 pages were rendered and reviewed in
  contact sheets; the title, pages 59--71, and all nine new table pages
  116--124 were also inspected at full size. No clipping, overlapping
  rows or footer intrusions were found. Fixed numerals remain free.

  Two independently audited refinements each give **98 operations**.
  The unit-centered coefficient code has digits in `{0,1,2}` and replaces
  `Omega=2lambda-e` by `Omega=lambda-e`. Copied unit coordinates remove
  the negative square coefficient in the Boolean unit test; the direct
  guard `2u*delta-x^2+delta^2` excludes `delta=0` before copies are used.
  Its necessity witness is `u=ceil(x^2/2)`. The full rebuilt-index,
  preliminary-bound, canonical-code and positive-witness proof is
  `1980/UNIT_CENTER_ENCODING_PROOF.md`. Its standalone checker
  `round27_1980_unit_center_certificate.py` verifies all 98 instructions
  and 22 residuals: **55 multiplications and 43 additions**.

  Independently, replace the auxiliary Pell equation by
  `(i*c^2)^2=D*(f^2-1)`, where `D=(a+4)^2-1`. The square on the left
  supplies the later norm parameter directly. The existing interval and
  first-index equations establish a large main index before this norm
  is used. Strong divisibility and Pell growth then recover an integral
  auxiliary Pell solution and the required multiple of the main
  coordinate. Necessity rescales only the auxiliary witness `i` by D.
  The complete proof is `1980/PELL_RELAXED_AUXILIARY_PROOF.md`, and
  `round28_1980_relaxed_auxiliary_certificate.py` verifies
  **54 multiplications and 44 additions**, including the changed sign
  in the exact signed-norm residual correction. Both variants retain
  34 positive unknowns, 22 equations and three fixed index parameters.
  Full independent mathematical and arithmetic audits pass.

  The two changes compose to **97 operations:
  54 multiplications and 43 additions**, still with 34 positive unknowns
  and 22 equations. The unit-centered code supplies the bounds needed
  to recover Pell integrality before the auxiliary signed norm is used.
  The subsequent exponent and code decoding proofs keep their original
  order. Necessity constructs the new canonical code and every Pell
  witness, then rescales only `i` by D. The complete composition proof
  is `1980/COMPOSED_97_PROOF.md`; the standalone checker
  `round29_1980_composed_certificate.py` verifies both complete schedule
  orders, all 22 source residuals, every one of the 97 primitives, and
  all three acyclic residual corrections. Independent full mathematical
  and arithmetic reviews pass. Fixed numerals and equality tests are
  free; this remains an upper bound with no optimality assertion.

  The completed 144-page article integrates both 98-operation proofs and
  their 97-operation composition in Sections 25--27. Appendices R--T
  contain every instruction and all equality tests; their generator
  reruns the three standalone exact checkers. The title, abstract and
  precise Theorem 5 statement include the new best bound. Two serial
  final PDF builds pass without warnings. All pages were rendered and
  inspected in contact sheets, with the title, all new proof pages
  70--81, Theorem 5 pages 82--83, and all nine new table pages 136--144
  additionally reviewed at full size. The visual pass caught and fixed
  a missing TeX escape on a Pell psi symbol; its page was rendered and
  inspected again after the final rebuild. The mathematical proofs are
  separate from the symbolic checks and have not been formalized in Lean.

  A linear-radix construction gives **96 operations:
  52 multiplications and 44 additions**, with 35 positive unknowns and
  23 equations. The new positive bound `ell+alpha2=q` removes the code
  quotient alias. The third block factors as `(lambda-e)*(q-C^2)`, and
  `B=H*b` replaces the former quadratic scale. The smaller radix requires
  a new coefficient construction: paired zero-centered equations have
  two-digit masks, positive reset padding removes incoming carries, and
  two unit tests with a final `5*x^2` padding force the homogeneous unit
  to one. That last padding uses three distinct coefficient-one entries,
  preserving the code alphabet `{0,1,2}`. The complete proof
  `1980/LINEAR_RADIX_96_PROOF.md` establishes the support, carry bounds,
  canonical decoding, retained Pell hypotheses and all positive witnesses.
  The standalone `round30_1980_linear_radix_certificate.py` checks all
  96 instructions, all 23 source residuals and their acyclic corrections.
  Independent complete mathematical and arithmetic reviews pass.
  The completed 154-page article includes the full proof in Section 28
  (pages 81--87), its precise Theorem 5 consequence on pages 88--89,
  and all 96 instructions and 23 equality tests in Appendix U
  (pages 152--154). The table is generated directly from the checked
  schedule by `round30_1980_schedule_table.py`. Two serial pdfLaTeX
  passes completed; the final log has no overfull/underfull boxes,
  undefined references or other warnings. All 154 pages were rendered
  and visually inspected in contact sheets. The title and precise
  theorem pages were additionally inspected at full size, and an
  independent full-size review of all ten new proof/table pages passed.
  The sparse encoding regression also passes, checking exact target
  coefficients, reset and final-padding identities, complete sample
  codes, and oversized-unit rejection separately from the general proof.
  Fixed numerals and equality tests remain free, and no optimality or
  Lean-formalization claim is made for the new construction.

  The subsequent combined-bound refinement keeps **96 operations:
  52 multiplications and 44 additions**, with **34 positive unknowns
  and 22 equations**. The single bound `ell+e+alpha=q` replaces the
  two old code bounds at the same two-addition cost. The explicit
  positive witness map restores the old gaps as
  `ell*(q-1)+alpha*q` and `e+alpha`; its two residual identities are
  checked symbolically. Conversely, canonical code digits prove
  `ell+e<q`, so the new gap is positive for every old solution.
  `1980/COMBINED_BOUND_96_PROOF.md` gives both maps in full, and
  `round31_1980_combined_bound_certificate.py` checks all 96 instructions
  and all 22 residuals. Independent mathematical and arithmetic reviews
  pass. Section 29 of the completed 169-page article includes this
  same-count refinement and its witness maps, following the 35-unknown
  construction in Section 28.

  The affine-radix construction gives **95 operations:
  51 multiplications and 44 additions**, with **34 positive unknowns
  and 22 equations**. It replaces `B=H*b` by `B=H+b`, with the fixed
  parameter `H=H0+1` and `H0` a sufficiently large power of two.
  The first mask uses `b` instead of `b-1`, saving one subtraction;
  its digits now forbid exactly the `H0` bit. Every logical coordinate
  except the homogeneous unit is represented by three physical
  coordinates with this bit clear. Three-digit target windows and
  reset padding make both signs of each zero equation exact. Three
  unit tests, with independent `5*x^2` and `7*x^2` preceding carries,
  remove the possible carry wraparound and force the unit to one.
  `1980/AFFINE_RADIX_95_PROOF.md` proves all support, carry, canonical
  decoding, Pell-bootstrap and positive-witness claims. The complete
  `round32_1980_affine_radix_certificate.py` verifies every instruction,
  all 22 source residuals and their three acyclic corrections.
  Independent full mathematical and arithmetic reviews pass, including
  a separate algebraic transformation of the preceding source list.
  A focused unit regression checked 32,272 cases, including 12 cases
  where the five-padding test alone admits a nonunit value and the
  seven-padding test rejects it. The broader sparse coefficient/carry
  regression `round32_1980_affine_radix_encoding.py` also passes:
  it checks the expanded physical circuit, all target coefficients,
  exact resets and both padding patterns, and dummy exclusion. It tests
  20 complete valid codes, eight codes with wide signed coefficients,
  eight complete nonunit rejection examples, 65,724 bit decompositions,
  9,341 paired three-digit windows and 73,299 reset cases, besides the
  32,272 unit pairs. These are finite regressions with explicit toy
  index bounds, distinct from the general proof and a full Pell-witness
  instantiation. The completed article includes the full proof in
  Section 29 and all 95 instructions in Appendix V. Fixed numerals and
  equality tests remain free; no optimality or Lean proof is claimed.

  Translating the fixed affine parameter gives
  **94 operations: 51 multiplications and 43 additions**, with the same
  **34 positive unknowns and 22 equations**. Replace the old fixed
  `H_old=H0+1` by `H=H0-3`. The actual radix `H+b+4` is unchanged,
  but the certificate can compare `theta` directly with `H+b` and
  delete its addition `theta+4`. No other instruction consumes either
  old radix register. `1980/SHIFTED_AFFINE_94_PROOF.md` proves an exact
  bijection that leaves every positive witness unchanged, and the
  complete `round33_1980_shifted_affine_certificate.py` checks all
  94 primitives, 22 source residuals and the parameter substitution.
  Independent mathematical and arithmetic audits pass. The 95-operation
  support and carry regression applies unchanged because the actual
  radix, codes and witness tuples have identical values. Section 30
  proves the translation, and Appendix W lists all 94 instructions and
  22 equality tests. Both new tables are generated directly from the
  complete certificate checkers. The title, abstract and precise
  Theorem 5 statement now include the 94-operation result.
  Two serial final PDF builds produced a 169-page article without
  warnings, unresolved references or overfull/underfull boxes. All
  169 pages were rendered and reviewed in contact sheets. The title
  and precise Theorem 5 pages were also reviewed individually; an
  independent full-size visual audit of pages 88--96 and 164--169
  checked both new proofs and both complete instruction/equality tables
  with no presentation findings. The reviewed PDF has 1,334,229 bytes
  and SHA256 `1d43997cd9d846552b46ec6d3590d6895783b75e948831c8dcc479561b77e8f4`.
  No numeral construction is charged, and no lower bound or Lean proof
  of this certificate is claimed.

  Factoring the packed mask gives **93 operations:
  50 multiplications and 43 additions**. The system, all 34 positive
  unknowns, all 22 equations and all supplied fixed parameters are
  unchanged. Replace `q^2*Tcoef-ell*b+theta*ell*q^4` by
  `q^2*Tcoef+ell*(theta*q^4-b)`. The four deleted temporaries have no
  consumers outside the replaced block, and the identity saves exactly
  one multiplication. `1980/FACTORED_MASK_93_PROOF.md` proves the
  identical accepted assignments and positive-witness map.
  `round34_1980_factored_mask_certificate.py` checks all 93 primitives,
  all 22 source residuals and their inherited acyclic corrections,
  equality of every retained register, and the unchanged literal
  numeral set `{1,3,8,15}`. An independent audit of the live predecessor
  schedule verifies the complete transformation and all residuals.
  Section 31 gives the full proof; Appendix X lists every instruction
  and all 22 equality tests, generated directly from the checker.
  The title, abstract, precise Theorem 5 statement and proof now include
  the 93-operation result. Its new equivalence clause is labeled (aa).
  Two serial final builds produced a 173-page PDF without warnings,
  unresolved references or overfull/underfull boxes. All 173 pages
  were rendered and inspected in contact sheets. An independent
  full-size visual audit checked pages 1, 95--100 and 171--173,
  including the complete new proof, the precise theorem, all 93
  instructions and all 22 equality tests, with no findings.
  The reviewed PDF has 1,351,068 bytes and SHA256
  `84da0ce657fc01ccbf491abe96a391aac86f60ed981aa1c5a474f347b3041933`.

  The smaller auxiliary Pell parameter gives
  **92 operations: 49 multiplications and 43 additions**, with
  **35 positive unknowns and 23 equations**. Retain
  `R=i*c^2`, `K=R^2=D*(f^2-1)` and all coding equations. Replace
  the old signed norm by `u=c+o*f` and
  `K*(u^2-y_aux^2)=1-y_aux^2`, where `u=2*r+1+j*c` is computed.
  The new block uses nine operations instead of ten. The new
  `y_aux` is positive; its square-gap intermediates are negative
  integers and use the same reversed-addition convention as before.
  `1980/HALF_PARAMETER_PELL_92_PROOF.md` proves the odd polynomial
  identity, both modular reductions, exact main-index recovery,
  unchanged sufficiency after that recovery, and positive necessity.
  The proof explicitly derives canonical `r` even and `J=1 mod 4`
  before constructing the new auxiliary quotients. No identity map
  on the changed auxiliary witnesses is asserted.
  The complete `round35_1980_half_parameter_pell_certificate.py`
  checks all 92 primitives and 23 source residuals. Its new auxiliary
  correction is `F16*(u^2-y_aux^2)`, using the independently exact
  retained norm. Independent full mathematical and arithmetic audits
  pass. The focused `round35_1980_half_parameter_pell_regression.py`
  checks 99 polynomial identities, 527 odd-divisibility cases,
  496 even-index exclusions, 1,581 normalized-root congruences,
  four complete positive auxiliary constructions and four parity
  controls. These finite examples corroborate the proof and do not
  instantiate the full universal system. The fixed index and literal
  numeral set `{1,3,8,15}` are unchanged. Section 32 now contains the
  complete proof, and Appendix Y gives all 92 instructions and 23
  equality tests. The title, abstract and precise Theorem 5 include
  the new result, with equivalence clause (ab). Two serial builds
  produced a 183-page PDF without warnings, unresolved references,
  or overfull/underfull boxes. All 183 pages were rendered and inspected
  in contact sheets. Independent full-size visual review checked
  pages 1, 99--106 and 181--183: the complete new proof, precise
  theorem and clause (ab), and every new instruction and equality.
  No visual findings remain. The reviewed PDF has 1,399,356 bytes and
  SHA256 `4d72b5ea6cbe968e65944d995c7ca97ca45a103e80f4150c73ec37585b4006e1`.

  The product-bound helper compiler gives
  **91 operations: 49 multiplications and 42 additions**, with
  **34 positive unknowns and 22 equations**. Its new equations are
  `sigma=(e-ell)*C^2` and `ell+sigma+alpha=q`. The first implies
  `e-ell>0`, so the supplied `Omega` and its free equality are removed.
  Before decoding, the two equations give `C^2<=sigma<q` and
  `ell<e<=ell+sigma<q`. The canonical coefficient code now satisfies
  `e0=ell0+D`. Two copied inputs supply positive compensating terms
  at every negative coefficient position. Seed and reverse rows
  establish both helpers equal to the input before the ordinary
  circuit equations and the unit tests use them. A stride-eight
  support and positive resets control all new signed carries.
  `1980/PRODUCT_BOUND_91_PROOF.md` supplies the full fixed-index
  construction, coefficient isolation, extra indicator tests,
  canonical decoding, and positive witnesses in both directions.
  It verifies `B|g,ell` and even `r` for the retained half-parameter
  Pell necessity. The complete checker
  `round36_1980_product_bound_certificate.py` checks all 91 primitives,
  all 22 fresh source residuals, the exact predecessor differences,
  and all three inherited acyclic corrections. Independent complete
  mathematical and arithmetic audits pass. The supplementary
  `round36_1980_product_bound_encoding.py` checks a sample with
  35 coordinate positions, 25 main rows, 128 tested starts, 418
  indicator digits and 976 nonzero coefficient terms. All symbolic
  targets, reset and padding coefficients, six canonical assignments
  and four wide signed-carry examples pass. These finite examples
  corroborate the general proof and are not an exhaustive search.
  Literal numerals remain `{1,3,8,15}`. Section 33 now gives the
  complete proof, including explicit interpolation and the full unit
  argument, and Appendix Z lists all 91 instructions and 22 equality
  tests. The precise Theorem 5 includes clause (ac). The abstract
  now states the baseline and current bound without accumulating the
  intermediate milestone descriptions. Two serial final builds give
  a 192-page PDF without warnings, unresolved references, or
  overfull/underfull boxes. All 192 pages were rendered and inspected
  in contact sheets. Independent full-size review of pages 1,
  103--112 and 190--192 covers the revised abstract, complete new
  proof and precise theorem, and every new instruction and equality.
  No visual findings remain. The reviewed PDF has 1,454,810 bytes and
  SHA256 `a96f4e4d51c3fa16754759c918bddadc50a94b18090e73ad6da1e903f8008854`.

  The binary product-bound compiler gives the current best
  **90 operations: 48 multiplications and 42 additions**, with the same
  **34 positive unknowns and 22 equations**. Replace the reverse helper
  rows by `2*delta*(x-Vi)`. Seeds and paired ordinary normalization first
  establish `Vi>=x` and `delta>0`; the reverse rows then give `Vi=x`.
  Their degree-one positive terms avoid the indicator, so both `ell0`
  and `e0=ell0+D` have only binary coefficients. Two unit tests suffice:
  an unpadded square and a square with a `2*x*X` carry. The final positive
  reset is the leading coefficient of `D`, proving `D(B)>0` for all
  `B>=2`. The binary mask permits `theta=B-2`, with supplied `H=H0-1`.
  The geometric relation is now `q^2=Tcoef+lambda`, removing the old
  multiplication `3*lambda`. Set `A=a+2`, so the first Pell modulus is
  `4*a+3`, the fixed length index is `psi_2(L)`, and interpolation is at 2.
  `1980/BINARY_PRODUCT_90_PROOF.md` proves coefficient isolation, binary
  interpolation, noncircular helper normalization, signed carries, both
  unit tests, canonical necessity and parity. `1980/BASE_TWO_PELL_90_PROOF.md`
  gives the changed bootstrap, main index recovery, `U=2^(2*r+1)`,
  `q=B^L`, the exact central-binomial rounding argument, and all positive
  Pell witnesses. Independent complete mathematical reviews pass.
  The complete `round37_1980_binary_product_certificate.py` checks all
  90 primitives, all 22 fresh source residuals, predecessor differences,
  and all acyclic corrections. The literal set is exactly `{1,3,4}`;
  fixed numerals and equality tests remain free. The separate compiler
  regression checks a sample with 35 coordinates, 24 main rows, 121
  tested starts, 397 indicator digits and 912 coefficient terms. Exact
  targets and dummy exclusion, six canonical cases, four wide carry
  cases and 1,252 local unit pairs pass. The separate exact Pell regression
  passes eight cases, including `r=64,66` with million-bit coordinates.
  These finite checks corroborate the general proofs and do not construct
  full packed-system witnesses. Root reruns and independent arithmetic
  audits pass. Section 34 now contains the complete binary compiler and
  changed Pell proof; Appendix AA lists all 90 instructions and 22 equality
  tests, generated directly from the checked certificate. Appendix labels
  extend past Z with `alphalph`; hyperref retains distinct destinations.
  The title, abstract and precise Theorem 5 include the 90-operation bound
  and new equivalence clause (ad). Two serial final builds produce a
  202-page PDF without warnings, unresolved references or overfull/underfull
  boxes. All 202 pages were rendered and inspected in contact sheets.
  Independent full-size review of exactly pages 1, 109--120 and 200--202
  checked the complete abstract, new proof, precise theorem including
  clause (ad), and all 90 instructions and 22 equality tests. No visual
  findings remain. All 27 appendix destinations are distinct; both the
  Appendix AA destination and clause (ad)'s link target page 200.
  The reviewed PDF has 1,513,522 bytes and SHA256
  `ef05c3811bd0f4332b234387d067b321e53a359cb86e76fedeb6dfa8d46bbad1`.

  Narrow binary packing reduces the complete bound to **89 operations:
  47 multiplications and 42 additions**, retaining **34 positive unknowns
  and 22 equations**, the same raw input and the same fixed index.
  This extends the satellite article's analysis of original Theorem 5;
  the historical printed system and its reported sign count are unchanged.
  Set `n=q^4`, `S=g+q*sigma+q^2*(ell+e*q)` and
  `Tplus=q^2*theta*lambda+ell*(theta*q-b)`. The packed index remains
  `r=S*(n^2-n)+Tplus*(n^2-1)`. Only these two source equations change.
  The consecutive field widths save one multiplication in the power chain,
  while the borrowed low product mask avoids an extra baseline addition.
  Before either exponent is decoded, the positive bounds give `0<S<n`,
  `0<Tplus<2n` and `n<=r<3n^3`. The revised independent Pell proof covers
  that wider range and recovers `q=B^L`, after which `Tplus<n` follows.
  Normalizing `Tplus-1` can initially spill into its binary-code field.
  Either nonzero spill forces `theta*ell<q`, contradicting the spill,
  so the original binary code is recovered before any canonicality is
  assumed. The modified product mask differs only at and below the first
  indicator, where the support of `D` forces the product digits to zero.
  Canonical witnesses retain even `r`; every Pell auxiliary is constructed
  afresh for the new packing. Both positive-domain directions are complete.
  `1980/BINARY_PRODUCT_89_PROOF.md` and `1980/BASE_TWO_PELL_89_PROOF.md`
  received complete independent mathematical reviews with no findings.
  The `round38_1980_binary_product_certificate.py` checker verifies all
  89 primitives, all 22 fresh source residuals, the exact predecessor
  differences and the inherited acyclic corrections. Literal numerals
  remain `{1,3,4}`, with numerals and equality tests free. The separate
  encoding regression retains the sample compiler's symbolic checks,
  six canonical assignments and four wide carry cases. It adds 77,114
  preliminary-bound cases (including 417 with `Tplus>=n`), 89,420 spill
  cases, 86,368 packed-popcount cases, 25,704 full-field comparisons,
  1,620 sparse mask comparisons and 12,288 borrowed-mask intersections.
  Fresh independent calls match both saved JSON receipts exactly and
  preserve their source and receipt hashes. The unchanged exact Pell
  regression also passes all eight cases. These finite checks supplement
  the general proofs and do not materialize full enormous Pell tuples.
  No new Lean formalization is asserted by this milestone; the separately
  documented `Universal90.lean` result retains its existing source system.
  Section 35 gives the new proof; Appendix AB lists all 89 instructions
  and 22 equalities, generated from the checked schedule. The title,
  abstract and precise Theorem 5 include the bound and clause (ae).
  Two serial final builds produce a 208-page PDF without warnings,
  unresolved references or overfull/underfull boxes. All 208 pages were
  rendered and visually inspected in contact sheets. Independent full-size
  review covered pages 1, 117--123 and 206--208: the new proof, precise
  theorem, every new instruction and every equality. No visual findings
  remain. All 822 named destinations are unique; all 28 appendix targets
  are distinct. Clause (ae)'s Appendix AB link resolves to page 206.
  The reviewed PDF has 1,547,870 bytes and SHA256
  `1dfa5f0892c38635ecf7445e09d01debcb9e7fbc14217cbf2a72488ea4875611`.

  The standalone direct square-scale audit refutes changing only `n=q^4`
  to `n=q^2` in89. That source has88=46M+42A, the same34 positive
  unknowns and22 equations, but accepts x=1 for a genuine fixed compiler
  index representing the empty set. Its exact sparse symbolic carry
  certificate gives `popcount(r)=(4L+1201)d-99` for all d>=4, above
  the required4Ld even at the genuine huge fixed threshold. A fresh
  constructive Pell argument supplies all remaining positive witnesses
  without reusing the missing upper bound on r. Author and independent
  full scoped proof/source reviews pass. Fresh verification exactly
  matches `explore_binary_scale_q2.json`, preserves source/receipt
  hashes, and independent division/popcount checks cover16 recorded
  normalization categories at six widths. The proof and checker are
  `1980/EXPLORATION_BINARY_SCALE_Q2.md` and
  `verification/explore_binary_scale_q2.py`. This is a research obstruction,
  not a universal improvement or a lower bound on arbitrary88 systems.
  No manuscript or PDF source changes were needed for this checkpoint.

  The general Boolean local-rule compiler in
  `1980/EXPLORATION_BOOLEAN_AFFINE_MASK.md` absorbs an arbitrary forbidden
  truth table into fixed coefficients of one affine expression and mask.
  A one-bit guard makes every Boolean cell value strictly positive and
  below its fixed power-of-two radix, even for rejected cells. This proves
  exact aligned packed composition without intercell borrowing. Placing
  a forbidden zero tuple last makes every coefficient positive and gives
  a separate range bootstrap for nonnegative planes. Author and independent
  mathematical/source reviews pass. The standalone checker and saved JSON
  verify278 relations in two clause orders,4,244 scalar assignments,
  4,164 packed cases,139 positive variants and complete Rule110/Life
  truth tables in both output conventions. A separate independent checker
  covers2,122 scalar and16,658 two-cell cases. Fresh root and independent
  default runs reproduce the receipt. The generic local upper count
  `(k+1)M+kA` and one mask multiplication exclude input-plane typing,
  alignment, mask implementation and the universal input/acceptance
  interface. This is a new encoding tool, not a lower universal bound;
  the specialized Life field remains locally cheaper. No TeX/PDF changes
  were required for this standalone research checkpoint.

  The consecutive-shift follow-up in
  `1980/EXPLORATION_BOOLEAN_CONSECUTIVE_CONVOLUTION.md` gives one exact
  local equality in10=6M+4A for every quiescent binary radius-one rule.
  A quadratic in the spatial shift combines the affine coefficients;
  its temporal shift is the fixed radix times that spatial shift.
  Uniform coefficient bounds prove a strictly positive quotient, and
  field bounds plus the congruence recover the actual word exactly.
  The associated standalone checker verifies the ten primitives and
  source residual,2,048 scalar cases,82,176 cyclic cases and821,760
  instruction-sign checks. Author and independent complete scoped
  proof/source reviews pass, and a fresh default run matches its JSON.
  The surjective lattice pullback is proved, while computational-model
  completeness requires its own consecutive-period construction.
  Geometry, Boolean typing, field bounds, masks and the raw input/halt
  interface are outside this conditional count. The complete universal
  bound remains89. No TeX/PDF changes were made for this research note.

  The complete specialized cyclic Rule110 certificate in
  `1980/EXPLORATION_RULE110_CYCLIC_CERTIFICATE.md` uses71=40M+31A,
  with23 positive existential unknowns, three positive parameters q,P,C,
  and16 equations. It characterizes exactly the indicated nonzero Boolean
  radix128 cyclic word and consecutive shifts. Geometry and bounds precede
  Pell decoding; the two packed masks recover Booleanity and the actual
  affine rule. On valid words, Rule110's output inequality forces a strictly
  positive local quotient, saving the signed adapter. The actual packed
  index is odd and the full fixed-minus Pell converse is constructed
  afresh. Author and independent complete scoped proof/source reviews pass.
  The checker verifies all71 primitives and16 residuals,90,036 cyclic
  cases with33 accepted positive outer tuples, non-power prebounds and
  arbitrary packed carry cases. Five exact odd main Pell cases through65
  and five separate auxiliary cases pass. An independent outer implementation
  checks all90,036 cases; separate immutable canonical/odd Pell receipts
  also match. These regressions do not materialize a full huge packed
  tuple; the general converse is mathematical. This is a different
  predicate from the75-operation endpoint relation, with no universal
  input or acceptance interface, so the universal bound remains89.
  No TeX/PDF changes were made for this standalone component checkpoint.

  The subsequent radix16 short-mask variant gives69=38M+31A for the
  abstract cyclic Rule110 relation, with the same23 existential unknowns,
  three positive supplied parameters and16 equations. Its numerical
  parameters differ from the radix128 encoding. The scalar field
  `1+l+3c+3r+4y` has one forbidden bit; inverse packing and a doubled
  Boolean field make the exact valuation threshold log2(q^3). The positive
  packed-index equation recovers the upper field bound before any power
  or typing argument, and the shared low bound excludes field carry.
  The first Pell kernel is audited directly at the pre-power scale q^3;
  squarehood is a later consequence. Factoring the local transport
  expression removes a multiplication. The actual new index is odd,
  and the complete fixed-minus positive converse is constructed afresh.
  Author and independent complete scoped mathematical/source reviews
  pass; a fresh default run reproduces the saved JSON. All69 primitives,
  16 residuals,90,036 cyclic cases,33 accepted positive outer tuples,
  non-power prebounds, inverse-carry cases and separate odd main/auxiliary
  Pell checks pass. A separate outer implementation checks90,036 cases
  and784 additional preliminary-bound cases. No enormous full packed
  Pell tuple is numerically instantiated. The proof/checker are
  `1980/EXPLORATION_RULE110_CYCLIC_SHORT_MASK.md` and
  `verification/explore_rule110_cyclic_short_mask.py`. The raw-input,
  marker and acceptance interface remains unresolved, so universal89
  and the distinct finite-endpoint75 result retain their stated scopes.
  No TeX/PDF changes were made for this standalone component checkpoint.

  The multi-bit local compiler in
  `1980/EXPLORATION_MULTIBIT_AFFINE_CELL.md` packs every fixed-alphabet
  state into one integer cell and checks its weighted bits with one
  product per neighboring site. A nonnegative coefficient mass bound
  prevents all carries; off-diagonal terms are untested, and dummy bits
  cannot alter the projected state. Repeated forbidden clauses ensure
  enough dummy positions to balance both mask weights exactly. Author and
  independent scoped proof/source reviews pass. A fresh default checker
  run matches the saved JSON:274 compilations,2,116 genuine assignments,
  33,674 state/dummy combinations, nine padded-clause cases and200 packed
  words. The local cost is independent of alphabet size, but geometry,
  bounds, cyclic transport and the universal interface remain outside
  this lemma. No TeX/PDF changes were required for this research checkpoint.

  The period-preserving lift in
  `1980/EXPLORATION_FOUR_CELL_PERIOD_LIFT.md` stores vertical triples and
  replaces any3-by-3 relation by one left/center/right/next relation.
  Overlaps force every globally valid triple field to be exactly the
  lift of its middle projection. Translation-equivariant inverse maps
  preserve the entire period lattice, including dimensions one and two.
  The marked tableau's intersection becomes the single state(V,X,V),
  preserving both the halting predicate and independent rectangular
  padding. Author and independent scoped mathematical/source reviews
  pass; a fresh default checker matches the JSON:4,096 local tuples,
  537,736 arbitrary triple fields,202 exact lifts,100 marked padded tori,
  100 repetitions,100 rejected inconsistent triples and20 consecutive
  cyclic presentations. Its finite table depends on both machine and
  input; no raw-input arithmetic compiler or universal count follows.
  No TeX/PDF changes were required for this research checkpoint.

  The full generic cyclic construction in
  `1980/EXPLORATION_MULTIBIT_CYCLIC_CERTIFICATE.md` uses70=40M+30A,
  with23 positive existential unknowns, supplied q,P,C and16 equations.
  The finite alphabet and four-cell relation affect only free fixed
  numerals. Nonzero state codes give a uniform strictly positive quotient;
  pre-power bounds, mask balance and a fresh odd-index Pell extension
  establish both directions. Adding the complete unit marker C=2+B*T
  gives72=41M+31A,27 positive unknowns and17 equations in
  `1980/EXPLORATION_MARKED_CYCLIC_72.md`. Composition with the marked
  tableau and exact-period lift proves an effective halting-instance
  reduction whose constants depend on both machine and input. This does
  not lower the fixed-index raw-input universal89 result. Author and
  independent complete scoped proof/source reviews pass. Source checks
  cover all70/72 primitives and16/17 residuals,2,880 pre-power candidates,
  2,180 cyclic cases with182 accepted,45 genuine-state transition
  rejections, six marked examples and retained odd Pell regressions.
  An independent source/marker/prebound recomputation matches the receipt.
  The JSON comparison explicitly normalizes tuple-valued equation pairs.
  The final fresh default run passes with exact saved-receipt equality.
  No full enormous packed Pell tuple is materialized. No TeX/PDF changes
  were required for this standalone research milestone.

  The homogeneous one-hot follow-up in
  `1980/EXPLORATION_HOMOGENEOUS_MARKED_CYCLIC_70.md` lowers the marked
  halting-instance construction from72 to70=40M+30A, with27 positive
  unknowns and17 equations. Homogeneous at-most-one, occupancy-equality
  and forbidden-tuple clauses remove the affine guard. The actual marker
  propagates occupancy1 along consecutive shifts, excluding zero states;
  DC*C>0 proves the actual field positive before that propagation, so
  modular recovery is sound. Author and independent complete scoped
  proof/source reviews and fresh default receipt checks pass. Evidence
  includes10,304 scalar cases,3,348 cyclic cases,80 complete positive
  marked outer tuples,71 positive dummy-only words,236 locally valid
  unmarked words, and six zero-expression padding clauses for32 symbols.
  The source verifies all70 primitives and17 residuals and retains the
  full43-operation odd-index Pell kernel and its positive converse.
  Constants still encode machine and input; universal89 is unchanged.
  No TeX/PDF changes were required for this research milestone.

  The next exact-period construction in
  `1980/EXPLORATION_THREE_CELL_PERIOD_LIFT.md` uses allowed3-by-3 windows
  as alphabet states. Horizontal and vertical overlaps give one ternary
  relation on center/right/next, whose valid fields are exactly the window
  lifts of their center projections. Every period survives. Stronger
  unused blank margins and height at least3 supply one fixed accepting
  block while preserving independent dimension padding. This is an
  existence-level marker refinement; arbitrary old intersections need
  not have the selected block. Author and independent full scoped
  proof/source reviews and fresh receipt checks pass:524,800 arbitrary
  block fields,32,768 compatible triples,714 original binary tori,6,426
  rejected one-component corruptions,100 marked padded tori and20
  consecutive cyclic presentations. The finite table depends on machine
  and input. No TeX/PDF changes were needed for this research milestone.

  The complete marked three-cell construction in
  `1980/EXPLORATION_THREE_CELL_MARKED_67.md` uses67=38M+29A,27 positive
  unknowns and17 equations. Its weighted1,1,2 homogeneous forbidden-triple
  clauses and two forward cyclic neighbors give a five-operation local
  equality with a positive quotient. Pre-power bounds, both masks, exact
  marker propagation and the full fresh positive Pell converse remain
  included. The exact-period block lift composes to an effective
  halting-instance reduction; both machine and input are in fixed numerals,
  leaving the fixed-index raw-input universal bound89 unchanged. Author
  and independent full scoped proof/source reviews and fresh default
  receipt checks pass:1,568 scalar cases,3,348 cyclic cases,84 positive
  marked outer tuples and four additional directional cases. The separate
  `verification/audit_three_cell_marked.py` evaluates all256 binary ternary
  relations in32,768 cases, without using the candidate's scalar-truth
  helper, and records immutable proof/source/receipt hashes. No full
  enormous packed Pell tuple is materialized. No TeX/PDF changes were
  required for this research milestone.

  The new `1980/EXPLORATION_RAW_INPUT_EXPONENT_BRIDGE.md` adds17=7M+10A
  to the marked67 schedule. It includes the raw index x+c0 and the
  stronger field bound, reuses the retained Pell solution, and proves
  exact index and power recovery with all five new Pell witnesses
  strictly positive. Its complete84-operation source has21 equations
  and33 positive coordinates including the endpoint W. Author and
  independent full scoped proof/source reviews pass; fresh checks cover
  every source residual,75 positive bridge examples, and out-of-range
  aliases demonstrating the necessity of the external W<q condition.
  This is a conditional component, leaving the universal bound unchanged.
  No TeX/PDF changes were required for this research milestone.

  The new `1980/EXPLORATION_UNIQUE_START_CYCLIC_67.md` retains67=38M+29A,
  27 positive unknowns and17 equations while proving exactly one Start
  state in a cyclic word of length at least2. Reusing the paid product
  B*Tmarker in the low field and adding one dummy position makes the
  uniqueness mask free. Its conditional endpoint pin costs4=2M+2A and
  supplies W<C<q before power decoding. Full author and independent
  scoped proof/source reviews and fresh receipts pass:1,536 scalar and
  3,144 cyclic cases, duplicate-start and short-word rejections, and
  endpoint checks with arbitrary dummy bits. Same-rectangle input
  identification remains a separate theorem. No TeX/PDF changes were
  required for this research milestone.

  The fixed unary-input theorem in
  `1980/EXPLORATION_FIXED_UNARY_TABLEAU.md` keeps its machine, alphabet
  and four initialization phases fixed while raw x varies. A forced
  first transition gives one uniform initial-head block in every
  rectangle, even on short inputs; another fixed block marks the input's
  left end. A unique Start and End at h(x+2)<N force the same rectangle
  and exact input. Both directions, one-sided machine normalization,
  no-escape acceptance, independent padding and cyclic signs have full
  author and independent reviews. Fresh checks pass for171 padded tori,
  57 cyclic presentations and rejected nonhalting truncations. The
  separately preserved `verification/audit_fixed_unary_tableau.py` checks
  30 noncanonical cyclic presentations and11,490 local triples with
  N!=h(h+1), and records immutable artifact hashes. This note states no
  arithmetic operation count. No TeX/PDF changes were required.

  The complete integration in `1980/FIXED_RAW_UNIVERSAL_88_PROOF.md`
  establishes **88=47M+41A**,36 strictly positive existential unknowns
  and23 equations for every positive raw input, with compiler numerals
  fixed once for the represented recursively enumerable set. It combines
  unique-start67, the17-operation exponent bridge at offset2, and the
  four-operation endpoint pin. The semantic proof identifies the same
  initialized rectangle; the arithmetic derives W<C<q before power
  decoding and supplies fresh positive witnesses at the actual odd r.
  Author and independent complete proof/source reviews pass. The fresh
  integrated checker verifies all88 primitives,23 residuals, fixed-only
  aliases and60 composed outer/endpoint/bounded-Pell interface examples,
  including wrong-input rejection. Full enormous packed Pell tuples
  are not materialized; their converse is proved. This improves the
  complete universal89 bound, unlike the previously refuted direct
  square-scale deletion. The new standalone proof and checker carry88;
  the existing208-page TeX/PDF remains89 and the Lean theorem remains90.
  No TeX/PDF source was changed for this research milestone.

  The subsequent `1980/FIXED_RAW_UNIVERSAL_84_PROOF.md` reduces the
  complete fixed-index raw-input system to **84=44M+40A**,33 positive
  existential witnesses and21 equations. It supplies the positive
  remainder Z directly, forbids both marker slots there, and inserts
  Start and End by C=CS+Z+W. The native End code1 removes its numeral
  multiplication. Soundness decodes the kernel and W before typing C;
  the two absent bits then insert without carries. Later occupancy
  eliminates other genuine bits at the marked cells. Z remains even,
  and the minimum native cell1 still gives a strictly positive transport
  quotient. Complete author and independent proof/source reviews pass.
  Fresh checks verify84 primitives,21 residuals,180 composed interfaces,
  nonzero unit remainders, duplicate-marker rejection, reversed transport
  rejection and raw-input rejection. The separate
  `verification/audit_fixed_raw_universal_84.py` independently constructs
  the coefficients for261 compilations and evaluates40,960 scalar/dummy
  cases, including every binary ternary relation, plus60 complete outer
  insertion examples. Its receipt records immutable reviewed hashes.
  The full positive Pell converse is proved, not numerically materialized.
  The fixed raw-input contract is unchanged; no TeX/PDF or Lean source
  was changed, so their separate89/90 evidence boundaries remain explicit.

  The fixed-base bridge in
  `1980/EXPLORATION_FIXED_BASE_EXPONENT_BRIDGE.md` costs15=7M+8A,
  including d(x+2), and reuses the retained kernel's a and4a+3.
  Both positive directions and the exact conditional82=44M+38A source
  have author and independent scoped proof/source reviews. Fresh checks
  cover all21 residuals,1,952 base-two congruences and18 common helical
  outer/adapter examples, including nondivisible Z and positive aliases
  without the raw bound. The changed offsets1,h require a separate
  computational interpretation; no universal improvement follows from
  this component alone. No TeX/PDF or Lean source was changed.

  The semantic theorem `1980/EXPLORATION_HELICAL_UNARY_TABLEAU.md`
  changes the cyclic neighbor offsets to1,h. Its horizontal boundary
  propagates inside a vertical strip only, and the vertical boundary
  symbol is constant at every time. Adjacent strips may therefore have
  shifted time origins, while initialization, exact transitions,
  no-escape acceptance and unique-marker input recovery remain valid.
  Completeness uses a genuine helical quotient and lifts actual cyclic
  windows, never an unjustified row-major rectangular group isomorphism.
  Full author and independent proof/source reviews and fresh receipts
  pass:171 padded and210 noncanonical presentations,48,213 local triples,
  3,789 seam windows, nonhalting truncations and malformed initial-row
  rejections. All210 noncanonical cases have h not dividing N. No
  arithmetic count is asserted by this semantic note, and no TeX/PDF
  or Lean source was changed.

  The complete integration `1980/FIXED_RAW_UNIVERSAL_82_PROOF.md`
  establishes **82=44M+38A**,33 positive existential witnesses and21
  equations for every positive raw input with fixed machine-dependent
  numerals. It combines the helical unary semantics and15-operation
  fixed-base bridge. Both full positive directions, all equation/name
  bindings, strict preliminary bounds, exact masks, positive transport,
  input recovery and the fresh actual-index Pell converse have author
  and independent complete reviews. Fresh integrated checks verify82
  instructions,21 residuals, fixed-only aliases,48,213 helical triples,
  1,952 base-two congruences and18 common arithmetic interfaces. The
  receipt stores the unchanged component artifact hashes. The raw
  bound's positive-alias counterexamples remain explicit. No TeX/PDF
  or Lean source was changed; their separate89/90 evidence remains
  distinct from this new mathematical82 theorem.

  `1980/EXPLORATION_HELICAL_ALIGNMENT_OMISSION.md` refutes the exact
  deletion of the two P-alignment instructions from82. Its80-operation
  source has32 positive witnesses and20 equations but accepts false
  raw inputs for the actual helical tableau compiler. High dummy bits
  supply an independent successor row after a shift within cells; the
  current forbidden-clause compiler guarantees enough dummies. The
  proof includes a fixed positive-odd-input machine and the false
  input x=2, with fresh full positive kernel and bridge extension.
  Author and independent full reviews and fresh receipt checks pass
  for26 arithmetic cases and32 initial slabs,14 nonhalting. This is a
  counterexample to the precise deletion, not an80-operation lower bound.

  The complete `1980/FIXED_RAW_UNIVERSAL_81_PROOF.md` uses a stationary
  first step and places Start at the last unary I cell, End at the first.
  Input initialization has x+1 I cells, so the marker distance is x and
  W=B^x. Removing raw_t=x+2 saves one addition: **81=44M+37A**, with
  all33 positive witnesses and21 equations. Both full directions retain
  fixed compiler numerals. The input x=1 has uniform adjacent windows;
  one-I strips contain neither marker and do not invalidate the
  destination-strip crossing proof. Completeness obtains N>=4 by padding
  for Z>0; soundness assumes only N>x. Author and independent full reviews
  and fresh exact-receipt checks pass for all81 instructions and21 source
  residuals,56,016 helical triples,21 smallest-input presentations,54 short
  unmarked presentations,1,920 wrong-strip crossings,1,952 congruences
  and18 arithmetic interfaces. The positive bridge proof uses d*x>=4;
  no full astronomical packed-kernel tuple is claimed to be materialized.
  Existing TeX/PDF89 and Lean90 artifacts retain their separate evidence.

  `1980/EXPLORATION_WIDE_GUARD_ALIGNMENT_OMISSION.md` closes the proposed
  repair by larger zero guards and highest-position Start. For every
  L>=k+m+1, arbitrary clause order, zero-expression padding and larger
  admissible R, the same linear compiler admits independently chosen
  successor states through its dummy band. Unwanted high contributions
  miss the tested block and remain below the next cell boundary. Thus
  the79-operation deletion from81 is unsound for the actual fixed
  tableau compiler, with a full positive false input x=1 for the
  positive-even machine. Author and independent complete reviews and
  fresh exact-receipt checks pass:73 arithmetic cases,49 untyped
  successors,16 stay-step slabs and9 nonhalting cases. The proof is
  specific to these compiler modifications; other encodings remain open.

  `1980/FIXED_RAW_UNIVERSAL_80_PROOF.md` replaces the generic forbidden-
  triple compiler with native window selectors and nine linked tile
  copies. Two separated sets of parity tests enforce the actual window
  overlaps. The successor coefficient becomes1, removing DY*P and giving
  **80=43M+37A**, with the same33 positive witnesses and21 equations.
  Both alignment operations, all input equations and the43-operation
  kernel remain. Independent full reviews cover malformed selectors,
  copy/dummy isolation, pre-decoding no-carry bounds, exact marker and
  overlap semantics, and every positive completeness witness. Fresh
  checks verify80 primitives,21 residuals,14,625 basis identities,
  400 malformed triples,742 canonical/empty triples,900 copy defects
  and6 packed outer examples; a separate independent audit checks1,500
  triples with larger tile alphabets. Fixed numerals grow but have no
  cost in the selected measure. TeX/PDF89 and Lean90 are unchanged.

  `1980/EXPLORATION_FIXED_RAW_SCALE_Q2.md` refutes the direct q^3-to-q^2
  deletion from81. The exact valuation3dN-V loses one unit for every
  forbidden local triple, so every genuine marked state word passes
  the weakened2dN threshold. The full fixed empty-machine compiler has
  a positive false input x=1; the proof constructs all33 witnesses at
  its actual packed r without importing the old q^3 soundness bounds.
  Author and independent complete reviews and fresh receipt checks
  pass for80 primitives,21 residuals,317 scalar triples,84 outer tuples
  and exact main/auxiliary Pell examples. The finite numerical compiler
  is explicitly a four-window subalphabet, with the full alphabet and
  enormous Pell extension proved symbolically. This rejected80 source
  is separate from the valid80 compiler change, which retains q^3.

  `1980/EXPLORATION_INPUT_PELL_GAP_PROJECTION.md` characterizes the
  deletion of c=kappa+phi from81: the input bridge projects exactly to
  W in the coset 2^u<2^(a+1)> modulo4a+3. For a genuine fixed outer
  witness with W=B^y, the criterion for a replacement x is the retained
  strict raw bound and gcd(a+1,ord_(4a+3)(2)) dividing d(y-x).
  Infinitely many positive larger-index witnesses at the same accepted
  input prove that the deleted gap is not implied by the other equations.
  They do not prove a false raw input. Author and independent scoped
  reviews and exact receipt checks pass for80 instructions,20 residuals,
  11,419 CRT cases and finite positive lifts. Input-set equivalence of
  the deletion remains unresolved; the valid80 construction retains it.

  `1980/EXPLORATION_WINDOW_COPY_PERIOD_DIVISOR.md` rules out deleting
  P*v=q from80. Its exact79-operation source admits a false x=1 for
  the actual empty-machine window-copy compiler. The construction
  retains alignment, both masks and popcount(r)=3dN, but supplies an
  odd P>1 that cannot divide q. All32 remaining witnesses are positive
  by the fresh actual-index kernel and raw-input converse. Author and
  independent complete reviews and fresh receipt checks pass for79
  primitives,20 residuals, the empty-machine reachability graph and84
  explicitly surrogate numerical examples. The actual huge compiler
  instance is proved by formulas, not silently replaced by those examples.

  `1980/EXPLORATION_WINDOW_COPY_ALIGNMENT_OMISSION.md` refutes deleting
  the remaining two alignment operations from80 without changing its
  compiler. P=R^(3a_tiles)<B divides q and makes each vertical parity
  coefficient twice the same center-copy bit. A genuine nonhalting
  initial slab yields a complete positive false input with the original
  mask valuation3dN. Author and independent complete reviews and fresh
  receipt checks pass for78 primitives,20 residuals,6 exact outer tuples,
  3,132 vertical coefficients,3,132 horizontal coefficients and58 center
  coefficients. The proof treats the full fixed machine alphabet; finite
  arithmetic examples use its explicitly identified slab subalphabets.
  Other compilers may enforce alignment by different local constraints.

  `1980/FIXED_RAW_UNIVERSAL_78_PROOF.md` supplies a new native compiler
  that forces period alignment through fixed encoded clauses. One of
  two separated center-clause bands is untouched by any bit rotation.
  After that band decodes the cells, Start's four synchronization bits
  force zero bit residue and a whole-cell shift. The proof excludes
  P=1 and P=q before using the retained helical semantics. Removing
  the two alignment operations gives **78=42M+36A**, with 32 positive
  witnesses and 20 equations; P*v=q, the 43-operation kernel and the
  14-operation input bridge remain. Author and independent complete
  proof/source reviews pass. Fresh default receipt verification covers
  all 78 instructions and 20 residuals, 41,952 coefficient identities,
  all 93,069 inner offsets for both support claims, 1,206 bit residues,
  300 malformed triples, 870 canonical/empty triples, 379 copy/anchor
  defects and two exact packed outer examples. Their indices have over
  14 million and 24 million bits. The universal alphabet and enormous
  complete Pell tuples are covered by proof; no proof-assistant claim
  follows. Larger fixed numerals have no cost in the chosen measure.
  The existing TeX/PDF89 and Lean90 artifacts remain separate.

  `1980/EXPLORATION_CYCLIC_MARKER_BIJECTION.md` proves a canonical
  bijection between Start and End occurrences in every genuine cyclic
  word. The first and last cells of each proper initialization I-run
  are the inverse endpoints, so the proof needs no injectivity of the
  covering plane or assumption that h divides N. Unique End therefore
  implies unique Start. Author and independent proof/source review and
  fresh receipt checks pass for 34,923 phase cycles, 468 genuine helical
  presentations and 63,828 local triples. The checks include rotations,
  repeated words, 96 unmarked short-run cases and 198 noncanonical
  strides. This is a semantic lemma with no arithmetic count claim.

  `1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` proves that every positive
  solution of the retained fixed-minus kernel necessarily has r odd.
  Its proof retains both signs after the stronger plus-sign step-down
  modulo 4m and covers noncanonical auxiliary indices and both reduction
  signs. The main index is recovered independently of parity first.
  Author and independent proof/source review and fresh receipt checks
  pass for 608,840 step-down cases, 6,960 polynomial congruences, 147 exact
  modular skeletons (140 noncanonical choices) and five full auxiliary
  tuples. The theorem applies before word decoding; it changes no source
  equation and makes no smaller complete-certificate claim by itself.

  `1980/FIXED_RAW_UNIVERSAL_77_PROOF.md` integrates those two lemmas
  into **77=42M+35A**, with 32 positive witnesses and 20 equations.
  Start becomes the native unit selector, forced at the origin by the
  necessary odd packed-index parity. Only End is explicitly inserted,
  as W=R*B^x. An odd inner bit width and even cell length make its Pell
  index d*x+b odd. Using the already computed discriminant as the
  index modulus removes one addition and pays for that fixed offset,
  retaining the 14-operation bridge. Unique End then gives unique Start.
  The proof preserves the raw bound d*x and derives d*x+b<2q, sufficient
  for exact input recovery and fresh strictly positive completeness.
  Author and independent complete proof/source reviews and fresh receipt
  checks pass: all 77 operations and 20 residuals, 35,364 basis identities,
  77,064 offsets per synchronization claim, 1,068 bit-residue parity checks,
  5,049 discriminant residues, 338,349 index projections, 12 positive input
  bridges and two exact packed outer tuples. Independent checks include
  additional compiler layouts, residues and positive bridge witnesses.
  The universal alphabet and full enormous Pell extension are proved
  mathematically, with no proof-assistant claim. TeX/PDF89 and Lean90
  remain separate artifacts; numerals are fixed and free as x varies.

  `1980/EXPLORATION_DELTA_INPUT_BOUND_OMISSION.md` refutes deleting
  d*x from the77 raw bound, which would give76=42M+34A. For one fixed
  even-input machine, every genuine input2 tuple maps to a false odd
  input x'=2+Delta through delta'=delta-d and alpha'=alpha+2d. The exact
  quotient bound delta_n>=2(n-1) proves the changed witnesses positive;
  all other coordinates and compiler numerals remain fixed. Author and
  independent complete proof/source review and fresh receipt checks pass
  for all20 symbolic residual maps, 1,519 quotient cases, 1,470 growth
  identities, six illustrative positive maps and32 machine inputs.
  The actual enormous full tuple is supplied by the77 positive converse.
  This is a complete false input for the stated deletion, not a lower
  bound on all76-operation certificates. Dependency hashes normalize
  CRLF to LF for reproducibility across Git line-ending conversions.

  `1980/EXPLORATION_FIXED_STRIDE_CYCLIC_OBSTRUCTION.md` proves a scoped
  finite-state obstruction to fixed temporal strides. A cyclic word with
  two unique markers at distance x is exactly a closed walk containing
  one Start edge, x-1 ordinary edges, one End edge and an ordinary return.
  The graph correspondence covers periods shorter than the offset span.
  A shortest return supplies a complete finite witness bound, including
  a total computable minimum length. Fixed offsets give an effectively
  ultimately periodic input language; input-computable offsets or a
  computable bound on the stride still give a decider. Author and
  independent complete reviews and fresh receipt checks pass: 5,040
  word/walk comparisons, 272 short cycles, 470 complete-bound marker cases,
  64 periodic-language inputs and 192 minimum-length cases. Additional
  independent automaton checks pass. The theorem excludes unbounded
  nonlocal arithmetic constraints and claims no universal operation bound.

  `1980/EXPLORATION_FIVE_ADIC_DUMMY_CONTROL.md` proves that a Boolean subset
  of weights at cells4j and optionally1 covers every residue modulo dN
  for powers of five d,N with N>25d. The proof uses the exact subgroup
  enumerated by B^(4j), with distinct consecutive residue parameters.
  It proves internal-cell bounds, the affine change of the actual packed
  index, and a fixed high-coefficient correction that makes its slope a
  unit modulo5. Compiler layout and positive-witness requirements are
  explicit hypotheses of the application. Author and independent complete
  proof/source reviews and fresh exact receipt checks pass:500 valuation
  cases, all3,250 targets in two small examples with independent subset
  dynamic programming,626 larger sampled targets,500 unit corrections
  and six exact moderate packed-index examples. An additional independent
  audit checks300 modular-power targets. No complete operation count or
  materialized full universal tuple is claimed by this lemma alone.

  `1980/FIXED_RAW_UNIVERSAL_76_PROOF.md` integrates Boolean dummy control
  into a complete **76=41M+35A** universal certificate, with30 positive
  existential coordinates and19 equations. It removes P*v=q and the two
  coordinates, using the already computed X=2^(2r+1) as temporal rotation.
  Fixed compiler sizes and canonical padding are powers of five. A dummy
  subset makes the actual final packed index satisfy2r+1=d*h modulo dN;
  an optional unchecked high DC monomial makes its coefficient a unit.
  Both compiler branches preserve native masks, field bounds and alignment.
  A fixed machine for the doubled input set and coefficient2d preserve
  the raw-input contract without an extra operation. The direct kernel
  proof and fresh positive converse apply to the genuinely nonsquare q^3.
  Author and two independent complete proof/source reviews pass. Fresh
  receipt checks cover76 primitives,19 residuals,41,664 basis identities,
  390,625 offsets per synchronization claim,2,250 bit residues,451 high-term
  checks and12 doubled-input bridge tuples, plus the five-adic dependency.
  Independent checks add two compiler layouts and two actual3,125-cell
  computation tableaux. No astronomical packed tuple or proof-assistant
  formalization is claimed. Existing TeX/PDF89 and Lean90 remain separate.

  `1980/EXPLORATION_NATIVE_MASK_RELATIONS.md` rules out two direct mask
  identifications in the retained76 interface. Equal masks at exact q-cubed
  population saturation require even d; alignment of X=2^(2r+1) requires
  odd d. Complementary masks force even local fields and a singleton-Start
  parity equation, whose only temporal shifts are zero or the chosen spatial
  neighbor. Both contradict specific entries of the actual Start window.
  Author and independent complete reviews and fresh exact receipt checks
  pass:1,506 packed examples,6,279 odd-index divisibility cases,51,408 parity
  cases in both orientations and2,744 actual neighbor completions. Fixed
  cell-mask bounds are explicit. Population surplus is not itself declared
  unsound, and different scale, marker or carry interfaces remain outside
  the result. The complete certificate bound remains76.

  `1980/EXPLORATION_SINGLE_PRODUCT_AUXILIARY_SCALE.md` records a precise
  **75=40M+35A candidate**, with30 positive coordinates and19 equations,
  obtained by replacing (i*c^2)^2 by i*c^2. Every76 witness maps positively
  by i_new=(i_old*c)^2, preserving all19 source residuals. Full soundness
  is open. An exact parametric q=16,r=259 witness disproves the weakened
  42-operation kernel interface: all ten equations, strict ratio and both
  congruence signs hold at main index517 rather than519, but the central
  binomial valuation is3 rather than the required12. The actual compiler's
  mask residues are also proved: even tile-alphabet size excludes this
  rational r=1 modulo3 family for all periods. No full false input is
  asserted. The auxiliary construction has the exact criterion gcd(p,c)|J
  for its prescribed CRT family, using the reduced odd modulus c/g;
  it is not a necessity theorem for arbitrary weakened-kernel witnesses.
  Author and independent complete scoped reviews and fresh receipt checks
  pass:19 source maps,238 successful modular auxiliary cases (40 noncoprime),
  97 exclusions,360 target cases over eight complete CRT periods, four
  materialized auxiliary tuples, three first/main tuples, exact large-family
  parameter data and60 compiler layouts. Dependency hashes use canonical
  LF text and match committed blobs. The established complete bound is76.

- Added the dyadic balanced wrong-index family for the weakened 42-operation
  kernel. Odd D and an odd divisor n of 2D^2+1 give an exact exponent
  balance, removing the need to search digits of a large irrational root.
  The strict Pell ratio follows from X>4pY. Primary q=16,r=269,p=329,
  Y=2^91 and secondary q=16,r=851,p=887,Y=2^37 both have odd r=2 modulo3
  and insufficient central-binomial valuation. The checker materializes
  seven first/main equations and finite auxiliary CRT parameters; the
  published exact-g lemma supplies the final three positive auxiliary
  equations. Actual compiler packing, transport and raw input remain
  outside this counterexample, so full75 soundness is still open.
  Author and two independent complete scoped reviews and fresh receipt
  checks pass for223 parameter identities, two q16 first/main tuples,
  a separately scoped q8 example and a rejected gcd37 neighbor.

- Updated the machinery-selection discussion to the current 76-operation
  ledger: 19 outer, 43 kernel and 14 input operations. It distinguishes
  small rule tables from cheap complete arithmetic verification and gives
  explicit remaining budgets for the Rule 110 and PD0L components.
  Added Lafont's interaction combinators as a primary-source example of
  a small universal calculus, with graph and input verification left
  explicitly uncounted. This research assessment claims no new bound.

- Added a constant-length nine-symbol queue with an ordinary ternary input
  and zero-word acceptance. A provisional delimiter permits one-symbol
  output on every scan step; accepting erasure keeps length constant while
  making both terminal coordinates zero. Initialization and the two full
  transports cost 14=7M+7A, including all scalar appendant products. The six
  packed histories are positive on accepting runs. Author and two independent
  complete scoped reviews and fresh receipt checks pass: six symbolic source
  residuals, 420 padded runs, 80,278 queue steps, 140 accepting transport
  tuples and 15,024 exhaustive scans. An independent larger runtime audit
  also passes. Controller arithmetic, field bounds, masks and power geometry
  remain explicitly unpaid; the complete universal bound stays 76.

- Added a separate delayed-blank successor with 13=6M+7A initialization and
  complete queue transport. The initial coordinates are x and L; a finite
  loader replaces the final raw zero with a true blank and rejects nonzero
  high digits. The proof retains fixed ordinary-input semantics, existential
  space padding, zero-word acceptance and positive packed histories.
  Author and two independent complete scoped reviews and fresh checks pass:
  five symbolic source residuals, all 1,093 initial words through six trits,
  420 padded client runs, 463 positive accepting transport tuples and the
  inherited 15,024 exhaustive short scans. The 14-operation predecessor is
  unchanged and hashed as a dependency. This conditional component leaves
  controller arithmetic and power geometry open; the complete bound is 76.

- Python 3.14.4 with SymPy 1.14.0; run the checkers with `PYTHONUTF8=1` on
  Windows. Each `round4_*_checks.py` runs in under a minute; the 1978
  script avoids expanding the degree-38 product (it sums factor degrees).
- LaTeX: MiKTeX. The 1982 article builds with XeLaTeX once fontconfig has
  seen the Libertine and Lato fonts shipped with MiKTeX; the 1978 article
  builds with LuaLaTeX after 78-R4-01. The MiKTeX `noto` package does not
  contain Noto Serif Devanagari.
- The checker `verification/jones1974_verify_counts.cpp` compiles with g++ (WinLibs) and
  runs in a few seconds.
