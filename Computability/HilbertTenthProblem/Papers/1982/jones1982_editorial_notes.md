# Jones (1982), *Universal Diophantine Equation* — consolidated editorial notes

James P. Jones, "Universal Diophantine Equation", *The Journal of Symbolic
Logic* **47** (3), September 1982, pp. 549–571, DOI
[10.2307/2273588](https://doi.org/10.2307/2273588). Received May 16, 1979;
revised March 9, 1981.

## 1. Article and scope

This document concerns three objects:

- **the scan**: `original/1982/jones1982.pdf`, 23 pages, journal pp. 549–571
  (PDF page $n$ is journal page $548+n$); every page carries a JSTOR download
  footer;
- **the naive OCR**: `original/1982/jones1982.tex`, the Mathpix transcription
  of the scan (it begins with JSTOR cover-sheet text);
- **the reconstruction**: `Papers/1982/jones1982_corrected.tex` and its PDF,
  the corrected reading edition.

It records every discrepancy between the naive OCR and the reconstruction and
says why each one exists. It is the complete record of the editorial
decisions for this article (the edition was first prepared on 13 September
2026); the dated log `Papers/EDITORIAL_NOTES.md` records revisions and checks
of the 1982 edition, such as 82-R4-01 and 82-R4-02, the pagination marks, the
edition notices and the findings of the Lean formalization. Each entry gives
the final state of the edition; where an earlier revision or an earlier
classification matters to a reader, the entry says so. The scan was compared
with every register entry. Seven items were first given a wrong
classification (the entries with a **Classification** line), one earlier
claim about the scan was refuted (Part 6, (3.14)), and a few typographic
items belong to the systematic classes of Part 3.

## 2. Classification legend

| Code | Meaning |
|---|---|
| **OCR** | Transcription defect: the scan is right, the OCR is wrong. |
| **ORIG** | Error in the printed original that affects a formula or a claim; corrected. |
| **CLAR** | Editorial clarification, stated hypothesis or proof completion added to the text. |
| **TYPO** | Typographical or cross-reference slip in the original (spelling, punctuation, wrong equation or lemma number, notation), with no change to the mathematics. |
| **BIB** | Bibliographic correction (names, titles, years, transliteration). |
| **EDN** | Edition apparatus: notices, pagination marks, metadata. |
| **LAYOUT** | Reflow or typesetting with no change of content. |

Only some CLAR additions are visibly marked as editorial in the article: the
footnotes described in Part 5 and the paragraph headed "Editorial proof-order
clarification". Most domain qualifications (for example "$B\geq2$" in
Lemma 2.8) are inserted inline without a mark. The edition notice says that
such clarifications have been made, and this register is the only record of
which words are editorial.

## 3. Systematic differences (described once)

These differences are not listed item by item in Part 4.

1. **Front matter (EDN).** The OCR's JSTOR cover-sheet text (title, author,
   "Source: The Tournal of Symbolic Logic, Vol. 47, No. 3 (Sep., 1982)",
   publisher, stable URL, access date, terms of use, JSTOR description) and the
   per-page JSTOR footers are not reproduced. The journal's own page furniture
   (the header "The Journal of Symbolic Logic, Volume 47, Number 3, Sept.
   1982", running heads, page numbers, the copyright line "© 1982, Association
   for Symbolic Logic 0022-4812/82/4703-0004/$03.30") is replaced by a new title
   block giving the journal, volume, issue, month, pages and DOI.
2. **Title-page footnote (EDN).** The received and
   revised dates, the 1980 Mathematics Subject Classification (03D25, 10N05,
   12L05) and the acknowledgment to Julia Robinson are kept verbatim as an
   unnumbered footnote. The author's footnote mark ¹ and the OCR's
   hidden-footnote macros are dropped; "1975-76" is set with an en dash.
3. **Edition notice and header comments (EDN).** A boxed notice under the title
   states that this is a corrected reading edition, not author-approved, that
   equation and reference numbers are kept and pagination is new, and that
   margin numbers mark the original page starts. It calls the text a
   continuously revised edition, names this document as the explanation of
   every discrepancy, and says that a dated log of revisions and checks is
   `Papers/EDITORIAL_NOTES.md` (with an `\allowbreak` in the file path). The
   header comments say "% Continuously revised edition; last source revision
   24 September 2026." and "% A dated log of revisions and checks is
   ../EDITORIAL_NOTES.md."
4. **Original pagination (EDN).** The macro
   `\origpage{n}` puts a bold `[n]` in the margin of the line on which journal
   page $n$ begins, for all 23 pages (549–571; p. 549 is marked at the first
   body paragraph). The marks are accurate to the line, not the word. The
   starts of pp. 550, 551, 554, 556, 557, 560 and 570 were placed by hand from
   the scan; p. 563 starts inside the sentence before (B3′), p. 568 inside the
   first sentence of §5, p. 557 at (B12) and p. 570 at (D32) (marks inside
   displays use `\marginnote` directly).
5. **Reflow and headings (LAYOUT).** New page
   layout, new line and paragraph breaks, no line-end hyphenation, forced `\\`
   breaks removed. The run-in headings "§n. Title." become numbered sections
   printed "§n Title". Theorem and lemma headings (small capitals with italic
   statements in the scan) become bold headings with upright statements, and
   "Proof." and "Remark." are italic. Long variable lists get `\allowbreak`.
   The 1982 edition builds with XeLaTeX (Linux Libertine O, Lato, Latin Modern
   Math); the Mathpix preamble is replaced.
6. **Mathematical markup (LAYOUT).** The OCR's `\left…\right` pairs (some of them
   malformed, such as `\left.` and `\right.\right.`), `(\bmod …)` groups and
   spacing are normalized, for example `x y`→`xy` and `$\cdots$` spacing.
   Commas and final periods are added between and after the equations of the
   multi-equation displays in Theorems 2 and 3. In the formula for $r$ the
   scan's square brackets $[n^2-n]$, $[n^2-1]$ become parentheses and the outer
   brackets become large brackets. The witness $o$ in Corollary 2.29 is set in
   math (first classified as OCR). The integer-part notation "[ ]" in
   §2 is set as $[\,\cdot\,]$ (first classified as OCR; the scan prints "[ ]"
   exactly as the OCR has it). "$i+1$ st" is closed up to "$i+1$st", and ranges
   in rewritten passages use en dashes ("(D1)--(D16)").
7. **Equation labels (LAYOUT).** All original tags (1)–(14), (i)/(ii), (3.1)–(3.14),
   (4.0)–(4.12), (A1)–(A7), (B1)–(B14), (B3′), (B8′), (C1)–(C3′), (D1)–(D37),
   (M1)–(M18), (M3′), (P1)–(P7), (Q1)–(Q3), (U0)–(U24), (U6′) are kept. The
   label changes in (B9)–(B11) and (C1)–(C3′), and the Cyrillic "М" in the
   (M5) tag, are entries of Part 4.
8. **Bibliography (LAYOUT, plus entries in Part 4).** The references become a list
   with bracketed numbers. The typography of the original (small-capital
   authors, italic titles, bold-italic journals) is dropped. The OCR's `→`
   arrows and `\\[0pt]` breaks are removed. The repeated-author dashes "———"
   of [8], [12]–[14], [17]–[20], [25] are expanded to the author's name ([8]
   becomes "J. P. Jones", [12]–[20] "Ju. V. Matijasevič", [25] "Julia
   Robinson"). Spacing inside "vol. 27 (1972)" in [13] and "vol. 68 (1977)" in
   [18] is normalized (first classified as OCR; the printed spacing is
   tight and ambiguous). The address block "Department of Mathematics and
   Statistics, University of Calgary, Calgary, Alberta, Canada, T2N 1N4" is
   set in ordinary case.
9. **Figures.** The article has no figures or tables other than the displayed
   Theorem 4 list (entry 1982-10).

## 4. Discrepancy register

Entries are in the order of the original pages. "OCR" quotes the naive
transcription (abridged with …). "Scan" is given only when it differs from the
OCR. "Reconstruction" quotes the current source or describes it. Where an item
was first given a different classification, a "Classification" line says so
and why it was corrected.

### 1982-01 · p. 549, §1, second paragraph · TYPO
- **Classification:** first classified as OCR; the scan shows that the period is missing in print.
- **OCR:** `the exponential relation $y=2^{x}$ is diophantine This together with [2]`
- **Scan:** identical; the period is missing in print.
- **Reconstruction:** "… is diophantine. This together with [2] …"
- **Justification:** sentence punctuation.

### 1982-02 · p. 550, §1 · BIB
- **OCR = scan:** `(This is a theorem of K.L. Siegel [22] …`
- **Reconstruction:** "C. L. Siegel".
- **Justification:** the author is Carl Ludwig Siegel, as in reference [22] ("Carl L. Siegel").

### 1982-03 · p. 550, §1, first paragraph · OCR
- **OCR:** `Kosovskii's polynomial` (the two preceding occurrences read `Kosovskiǐ`)
- **Scan:** "Kosovskiǐ's", with the breve, like the other occurrences.
- **Reconstruction:** "Kosovskiǐ's". "N.K." is spaced "N. K.".

### 1982-04 · p. 551, §1 · TYPO
- **OCR = scan:** `divisiblility`
- **Reconstruction:** "divisibility".

### 1982-05 · p. 551, §1, "These systems of equations are given in the following three theorems." · CLAR
- **OCR:** the sentence without a note.
- **Reconstruction:** adds a footnote: "Editorial clarification: the indices used here are the admissible coding triples constructed in (4.1), for a normalized representing polynomial as specified in §3. The proof below establishes the stated equivalences for these triples. It does not justify treating arbitrary unrelated positive triples as encodings of such polynomials."
- **Justification:** the proofs in §§4–5 use the digit structure of $u$, $y$ from (4.1) (for example $u>2z$, $y>(2z)^{(\delta+1)^{\nu+1}}$, and the coefficient bound on $z$). The theorems hold for these indices, which suffice for universality because every r.e. set has one. No claim is made about arbitrary positive triples. The Lean proofs (`Jones1982.exists_index_above`, `exists_index`) show that admissible triples exist, with all three coordinates positive when $\nu\geq1$. The 1980 edition makes the same point explicit.

### 1982-06 · p. 551 (Theorem 1), p. 565 (after (4.6)), p. 566 (before (U6′)) · OCR
- **OCR:** `e \lg ^{2}` (Theorem 1 and before (U6′)); `\operatorname{elg}^{2}` (p. 565)
- **Reconstruction:** $elg^2$.
- **Justification:** the scan prints the product of the three unknowns $e,l,g^2$; `\lg` (a logarithm) is an OCR artefact.

### 1982-07 · p. 552, Theorems 2 and 3, first line · OCR
- **OCR:** `q=b^{560}`
- **Scan:** $q=b^{5^{60}}$ (the 60 is a second-level superscript), as in Theorem 1 and in the text after Theorem 3.
- **Reconstruction:** $q=b^{5^{60}}$.
- **Justification:** (U2)–(U3) with $\delta=4$, $\nu=58$ give $B=b^5$ and $q=B^{5^{59}}=b^{5^{60}}$.

### 1982-08 · p. 552, Theorems 2 and 3, the formula for $r$ · ORIG
- **OCR = scan:** `…+\lambda b^{5}+\lambda b^{5} q^{4}) q^{4}][n^{2}-n] +[q^{3}-bl+l+\theta\lambda q^{3}+(b^{5}-2) q^{5}][n^{2}-1]`
- **Reconstruction (both theorems):**
  $r=\bigl[g+eq^3+lq^5+\bigl(2(e-z\lambda)(1+xb^5+g)^4+\lambda b^5+\lambda b^5q^4\bigr)q^7\bigr](n^2-n)+\bigl[q^3-bl+l+\theta\lambda q^3+(b^5-2)q^8\bigr](n^2-1)$,
  displayed on three lines (square brackets around $n^2-n$ and $n^2-1$ become parentheses, see Part 3).
- **Justification:** by (U12)–(U22), $S_1=g$, $S_2=e+lq^2$, $S_3=2(e-z\lambda)(1+xb^5+g)^4+\lambda b^5(1+q^4)$, $T_1=q^3-1-(b-1)l$, $T_2=\theta\lambda$, $T_3=(b^5-2)q$, with $N_1=q^3$, $N_2=q^4$, $N_3=q^9$ and $S=S_1+S_2N_1+S_3N_1N_2$, $T=T_1+T_2N_1+T_3N_1N_2$. The third block therefore starts at $N_1N_2=q^7$, not $q^4$, and $T_3$ contributes $(b^5-2)q\cdot q^7=(b^5-2)q^8$. Substituting into (U24), $r=S(n^2-n)+(T+1)(n^2-1)$ with $n=N=q^{16}$, gives the reconstruction exactly; the $-1$ of $T_1$ cancels the $+1$ of $T+1$. The printed version differs by the nonzero polynomial $S_3(q^4-q^7)(n^2-n)+(b^5-2)(q^5-q^8)(n^2-1)$. The same repair is made, and re-derived, in the edition of the 1980 announcement. Checked symbolically and proved in Lean (`Jones1982.centralCode_eq_rPolynomial`).

### 1982-09 · p. 552, Theorem 3, first equation of the third line · ORIG
- **OCR = scan:** `p=2 w s^{2} r^{2} n^{2}`
- **Reconstruction:** $p=2ws^2r^2n^6$.
- **Justification:** Theorem 3 transcribes Lemma 2.25. By (B1), (B5), (B9) and (B10), $P=2M^2U$, $M=RY$, $U=N^2w$, $Y=N^2s$, so $P=2(RN^2s)^2N^2w=2wR^2s^2N^6$. In lower-case letters this is $p=2ws^2r^2n^6$; the printed $n^2$ lacks a factor $n^4$. The same repair is made in the edition of the 1980 announcement. Checked symbolically and in Lean (Theorem 3).

### 1982-10 · pp. 552–553, Theorem 4, list of pairs · OCR
- **OCR:** the four columns are scrambled, e.g. `\nu=58, & \delta=4 \nu=28, & \delta=20 \nu=21, \delta=96 & \nu=12, \delta=1.3 \times 10^{44}`
- **Scan:** three rows of four pairs "$\nu=58,\ \delta=4$ | $\nu=28,\ \delta=20$ | $\nu=21,\ \delta=96$ | $\nu=12,\ \delta=1.3\times10^{44}$", then (38, 8), (26, 24), (19, 2668), (11, $4.6\times10^{44}$) and (32, 12), (25, 28), (14, $2.0\times10^5$), (10, $8.6\times10^{44}$).
- **Reconstruction:** the same twelve pairs in the same arrangement, printed as $(\nu,\delta)$ tuples such as $(58,4)$ (LAYOUT), with "≈" added by 1982-11.
- **Justification:** the scan. The 1982 original lists exactly twelve pairs; the 1980 announcement's sixteen-pair table is a different list and no row is missing. The heading's words "(unknown, degree)" (restored, see 1982-11) state the order $(\nu,\delta)$ of the tuples.

### 1982-11 · p. 552, Theorem 4 heading and the four scientific-notation degrees · CLAR
- **OCR = scan:** `Theorem 4. The following pairs (unknown, degree) are universal:`; entries `1.3 \times 10^{44}`, `4.6 \times 10^{44}`, `2.0 \times 10^{5}`, `8.6 \times 10^{44}`
- **Reconstruction:** the printed heading "The following pairs (unknown, degree) are universal:" with a footnote *Editorial clarification: the four degrees in scientific notation are the author's rounded sizes of degrees whose computation the article omits. They are marked ≈ here: they are approximate sizes, not exact integer degree bounds. The pairs are reported as the author states them; they have not been rederived in this edition.* The entries read $\approx1.3\times10^{44}$, $\approx4.6\times10^{44}$, $\approx2.0\times10^5$, $\approx8.6\times10^{44}$.
- **History:** an earlier revision of this edition replaced the heading by "The following universal constructions are reported; the large degrees in scientific notation are approximate sizes, not exact integer degree bounds:", which dropped the words "(unknown, degree)" and the author's claim. On 24 September 2026 (82-R4-02) the printed heading was restored and the qualification moved into the marked footnote; the replacement heading should not be re-proposed.
- **Justification:** these entries are rounded sizes of degrees that the author computed but did not publish ("The details of these calculations are omitted"). Rounded values are not certified degree bounds. For comparison, the one exact expression the article gives, $47216\cdot5^{58}+9728\approx1.638134\times10^{45}$ (§3), was printed in the 1980 announcement as $1.6\times10^{45}$, which is below the exact value. The small integer entries are unchanged.

### 1982-12 · p. 553, §1, operation-count paragraph · ORIG
- **OCR = scan:** `Thus 100 arithmetical operations are universally sufficient to determine membership of a number in any r.e. set.`
- **Reconstruction:** "Thus the stated 100 arithmetical operations suffice to check a supplied Diophantine certificate of membership in any r.e. set. They do not decide membership or bound the work of finding such a certificate."
- **Justification:** for $x\in W_v\Leftrightarrow\exists\mathbf a\,U(x,v,\mathbf a)=0$, a fixed arithmetic circuit evaluates $U$ on a *supplied* witness $\mathbf a$. It neither finds $\mathbf a$ nor decides whether one exists, and for nonrecursive $W$ no procedure decides membership. The printed claim is correct only as a verification claim.

### 1982-13 · p. 553, §1, paragraph before Theorem 5 · CLAR
- **OCR = scan:** `the theorems of an axiomatizable theory $T$ become in effect an r.e. set`
- **Reconstruction:** "effectively axiomatizable theory".
- **Justification:** the set of theorems is r.e. only for an effectively presented theory. Traditional usage often builds effectiveness into "axiomatizable"; the edit makes that explicit and does not suggest that the author meant otherwise.

### 1982-14 · p. 553, §1, same paragraph · ORIG
- **OCR = scan:** `Such solutions reflect faithfully the logical complexity of the original proof since the entire deduction is effectively recoverable from a solution.`
- **Reconstruction:** "A formal deduction is effectively recoverable from a solution, but no preservation of its length or computational complexity is asserted."
- **Justification:** effective recoverability gives no quantitative correspondence. For an effectively axiomatized theory a proof can always be recovered by enumerating proofs until the certified sentence appears, which shows that recoverability alone carries no size bound.

### 1982-15 · p. 553, Theorem 5 · CLAR
- **OCR = scan:** `Theorem 5. For any axiomatizable theory $T$ and any proposition $P$, if $P$ has a proof in $T$, then $P$ has another proof consisting of 100 additions and multiplications of integers.`
- **Reconstruction:** "Theorem 5 (certificate interpretation). For any effectively axiomatizable theory $T$ and any proposition $P$, if $P$ has a proof in $T$, then $P$ has a Diophantine certificate with the stated verification count of 100 additions and multiplications of integers." A footnote explains that "another proof" means an arithmetic certificate under a fixed effective encoding, not a 100-step derivation in the calculus of $T$, and that the count is whole-integer arithmetic (subtraction included) without equality tests, bit operations, integer lengths or certificate search. The footnote also says that the count 100 is reproduced by counting every indicated $+$, $-$ and $\times$ sign of the seventeen polynomial equations of Theorem 3 once (exponentiation not counted), that the same rule gives 87 for the 1976 system, and that the intended reading and a calculator model with powers computed by repeated multiplication are examined in the satellite article `Papers/1980/jones1980_theorem5_operations.pdf`. Until 14 September 2026 the footnote said instead that "the exact count 100 is the author's reported count; it has not been independently reconstructed"; that wording was replaced once the count had been reproduced.
- **Justification:** as for 1982-12 and 1982-13.

### 1982-16 · p. 553, §2, after the first paragraph · CLAR
- **OCR:** no such text.
- **Reconstruction:** a new paragraph: "For the digit and carry lemmas, the arguments of $\sigma_B$ and $\tau_B$ are nonnegative integers, the base $B$ is an integer at least $2$, and 'power of $2$' means $2^k$ with an integer $k\geq0$. In particular $\sigma_B(0)=0$. Unless a more specific domain is stated, Greek witness variables in the displayed Diophantine systems are also positive integers."
- **Justification:** the article's convention that lower-case letters denote positive integers does not cover the digits, carries and masks of §2, which can be zero (for example $v=0$ in Lemma 2.7, the zero digits in Lemma 2.9). The Lean formalization confirms that all equations are to be read over $\mathbb Z$ with the stated witness domains.

### 1982-17 · p. 554, Lemma 2.8 · CLAR
- **OCR = scan:** `If $B$ pow 2 and $|V|<B/2$, then …`
- **Reconstruction:** "If $B\geq2$, $B$ pow 2 and $|V|<B/2$, …"
- **Justification:** $B=1=2^0$ is a power of two, but then $B/2$ is not an integer and $\tau_2(B/2+V,B/2-1)$ is undefined. The edge case $B=2$ was checked.

### 1982-18 · p. 554, Lemma 2.9 and its proof · CLAR
- **OCR = scan:** `For $n \leq m \leq k, z$ pow $2, B$ pow $2,2 z^{m+1} \leq B$. Suppose $y=\sum_{i=0}^{n} y_i z^i$ …` and, in the proof, `Now consider the number $y'=\sum_{i=0}^{m} b_i z^i$`.
- **Reconstruction:** "Let $0\leq n\leq m\leq k$ be integers, $z\geq2$, $z$ pow $2$, $B$ pow $2$, and $2z^{m+1}\leq B$. Suppose $Y\geq0$ is an integer and …"; in the proof, "Extend the digits by $y_i=0$ for $i>n$." is inserted before "Now consider".
- **Justification:** the proof takes a base-$B$ expansion of $Y$ (so $Y\geq0$), needs $z\geq2$ for the digit comparison, and compares $\sum_{i=0}^{m}|b_i-y_i|z^i$ with $m$ possibly larger than $n$.

### 1982-19 · p. 554, Lemma 2.11 · ORIG (with LAYOUT)
- **OCR = scan:** `If $N_i$ pow $2, 0 \leq S_i<N, 0 \leq T_i<N (i=1,2,\ldots,n)$ and $S=\sum_{i=1}^{n} S_i N_1 N_2 \cdots N_{i-1}$, $T=\sum … $ and $N=\prod_{i=1}^{n} N_i$, then`
- **Reconstruction:** "Suppose $N_i$ pow $2$ and $0\leq S_i<N_i$, $0\leq T_i<N_i$ for $i=1,\ldots,n$. Put $S=\sum_{i=1}^{n}S_i\prod_{j=1}^{i-1}N_j$, $T=\sum_{i=1}^{n}T_i\prod_{j=1}^{i-1}N_j$, $N=\prod_{i=1}^{n}N_i$. Then …"
- **Justification:** the content change is $N\to N_i$ (ORIG). Each block must fit its own radix $N_i$: with only $S_i<N=\prod N_j$ the blocks may overlap, and the induction on Lemma 2.10 fails. All applications ((M13)–(M15), (U18)–(U22), (D13)–(D16)) verify $S_i,T_i<N_i$. Writing $N_1N_2\cdots N_{i-1}$ as $\prod_{j=1}^{i-1}N_j$ and setting the definitions in a display is LAYOUT.

### 1982-20 · p. 554, Lemma 2.11(i) · TYPO
- **OCR = scan:** `\wedge_{i=1}^{n} \tau_{2}(S_{i} T_{i})=0`
- **Reconstruction:** $\bigwedge_{i=1}^{n}\tau_2(S_i,T_i)=0$.
- **Justification:** $\tau_2$ takes two arguments; the separating comma is missing in print.

### 1982-21 · p. 554, proof of Lemma 2.12 · TYPO
- **OCR = scan:** `[(a+b)/B^i]=[a/B^i]+[b/B^i)+[(a'+b')/B^i]`
- **Reconstruction:** $[b/B^i]$, with a closing bracket.
- **Justification:** mismatched integer-part bracket.

### 1982-22 · p. 554, Lemma 2.13 · ORIG
- **OCR = scan:** `\tau_{B}(a, b)=\sum_{i=1}^{\infty}[(a+b)/B^{i}]-[a/B^{i}]-[b/B^{i}] .`
- **Reconstruction:** $\tau_B(a,b)=\sum_{i=1}^{\infty}\bigl([(a+b)/B^i]-[a/B^i]-[b/B^i]\bigr)$.
- **Justification:** read literally, the printed formula subtracts two terms from a divergent sum; by Lemma 2.12, all three integer parts belong inside the summation (each summand is the carry indicator 1 or 0).

### 1982-23 · p. 555, proof of Theorem 2.14 · ORIG
- **OCR = scan:** `According to Lagrange's theorem, if $B$ is a prime, then $B$ divides $n!$ to the exact multiplicity …`
- **Reconstruction:** "According to Legendre's formula, …"
- **Justification:** $v_p(n!)=\sum_{i\geq1}[n/p^i]$ is Legendre's formula; the result being proved is Kummer's theorem.

### 1982-24 · p. 555 (Lemma 2.16) and p. 558 (remark before Lemma 2.26) · OCR
- **OCR:** `N^{2} \lvert (\frac{2 R}{R})`
- **Reconstruction:** $N^2\mid\binom{2R}{R}$.
- **Justification:** the scan prints a binomial coefficient.

### 1982-25 · p. 555, Elementary inequalities 2.17 · ORIG + CLAR
- **OCR = scan:** `For any real number $\alpha$ : if $\alpha<1$, then $(1-\alpha)^{n} \geq 1-n^{\alpha}$`
- **Reconstruction:** "For any real number $\alpha$ and any nonnegative integer $n$: if $\alpha<1$, then $(1-\alpha)^n\geq1-n\alpha$".
- **Justification:** Bernoulli's inequality is $(1-\alpha)^n\geq1-n\alpha$ for integers $n\geq0$ and $\alpha<1$. The printed $1-n^\alpha$ is not what the proof uses: it is true only trivially (for $0<\alpha<1$ and $n\geq1$ its right side is $\leq0$; for $\alpha\leq0$ it is $<1\leq(1-\alpha)^n$) and it does not give inequality (2) of Lemma 2.25, which needs $\bigl(1-\frac1{2M(U+1)}\bigr)^{2R}\geq1-\frac{R}{M(U+1)}$ (ORIG). The domain of $n$ is stated explicitly (CLAR).

### 1982-26 · p. 555 and throughout §2 · OCR
- **OCR:** `y=\phi_{A}(n)` (definition), `\phi_{A}(n+1)` (Lemma 2.19), `C=\phi_{A}(B)` (Lemmas 2.27, 2.28, remark after 2.28, Corollary 2.29); `\psi` elsewhere; and `\psi(2R+1)` without index (see 1982-35).
- **Scan:** the same Pell symbol $\psi_A$ throughout.
- **Reconstruction:** $\psi_A$ everywhere. The positive witness $\phi$ of Lemma 2.25 and §5 is a different symbol and is unchanged.

### 1982-27 · p. 555, definition of $\chi_A$, $\psi_A$ · CLAR
- **OCR = scan:** `We denote the solutions by $x=\chi_A(n)$ and $y=\phi_A(n)$ as usual. These sequences have …`
- **Reconstruction:** "… as usual, with $A\geq2$, $n\geq0$, and nonnegative Pell coordinates. These sequences have …"
- **Justification:** fixes the branch ($\chi_A(n)+\psi_A(n)\sqrt{A^2-1}=(A+\sqrt{A^2-1})^n$) and the index origin used in Lemmas 2.18–2.23.

### 1982-28 · p. 555 (after the definition of $\chi_A,\psi_A$) and p. 556 (proof of Lemma 2.23) · ORIG
- **Log entry:** 82-R4-01 in `Papers/EDITORIAL_NOTES.md`.
- **OCR = scan:** `(cf. [23], [24], [15], [4], [18], [8] for proofs)`; `(cf. [23], [24] or [18])`
- **Reconstruction:** "[25], [24], …" in both places, with a footnote at the first: "Editorial emendation: the printed text cites [23], [24] here and again in the proof of Lemma 2.23. Reference [23] is Kummer's 1852 paper on the reciprocity laws, which contains nothing on Pell equations, and reference [25], Julia Robinson's *Existential definability in arithmetic*, the standard source for these properties, is otherwise never cited; so [23] is read as a slip for [25] in both places."
- **Justification:** as in the footnote. [23] is cited correctly for Kummer's theorem on p. 551 ("[23], [26]"); the 1976 and 1978 articles cite Robinson's 1952 paper for these Pell facts. The error is probably a citation left unrenumbered when [23] was inserted.

### 1982-29 · p. 555, Lemma 2.19 · CLAR
- **OCR:** `For $A>0,(2 A-1)^{n} \leq \phi_{A}(n+1) \leq(2 A)^{n}$`
- **Reconstruction:** "For $A\geq2$ and $n\geq0$, $(2A-1)^n\leq\psi_A(n+1)\leq(2A)^n$."
- **Justification:** $\psi_A$ was just defined for $A>1$ only; every application has $A\geq2$.

### 1982-30 · p. 556, Lemma 2.22 · CLAR
- **OCR = scan:** `For $0<V, 0<B$, in order that … there exist integers $A$ and $C$ such that:`
- **Reconstruction:** "For positive integers $V,B,W$, … there exist positive integers $A$ and $C$ such that:"
- **Justification:** without $W>0$, $V=1$, $W=-1$ satisfies (i)–(iii) with (iv) for suitable $A$ while $W\neq V^B$. The positive branch matches the Pell convention of 1982-27.

### 1982-31 · p. 556, Lemma 2.23 · CLAR
- **OCR = scan:** `Suppose $0<B_{1} \leq B<A$ and $C=\psi_{A}(B)$.`
- **Reconstruction:** "Suppose $C_1>0$, $0<B_1\leq B<A$ and $C=\psi_A(B)$."
- **Justification:** the square condition (i) is also satisfied by $-\psi_A(n)$. The conclusion $C_1=\psi_A(B_1)$ needs the positive coordinate.

### 1982-32 · p. 556, Lemma 2.25, equations (B9)–(B11) · OCR
- **OCR:** `Y=N^{2} s, \tag{B9}` followed by `W=b w, \tag{B10}`; no (B11).
- **Scan:** (B9) $U=N^2w$, (B10) $Y=N^2s$, (B11) $W=bw$.
- **Reconstruction:** as in the scan.
- **Justification:** the OCR dropped a whole equation and shifted the next two labels. The proof refers to (B9) for $U$ and to (B11) for $W$ ("Therefore (B11) implies $bw=2^{2R+1}$"), and Theorem 3 depends on $U=N^2w$ (1982-09).

### 1982-33 · p. 557, sentence after (B14) · TYPO
- **OCR = scan:** `the initial conditions together with (B5), (B6), (B7), (B8), (B10), (B12) imply that $1<A$, …`
- **Reconstruction:** "(B5), (B6), (B7), (B8), (B9), (B10), (B12)".
- **Justification:** $A=M(U+1)>1$ needs $U=N^2w\geq1$ from (B9).

### 1982-34 · p. 557, remark after Lemma 2.25 · OCR
- **OCR:** `\frac{C}{K}=\frac{\psi(2 R+1)}{\psi(R+1)}`
- **Scan:** $\psi_{M(U+1)}(2R+1)$ over $\psi_{2M^2U}(R+1)$ (the Pell bases are printed as subscripts under the $\psi$).
- **Reconstruction:** $\frac{C}{K}=\frac{\psi_{M(U+1)}(2R+1)}{\psi_{2M^2U}(R+1)}$.

### 1982-35 · p. 557, sufficiency proof of Lemma 2.25, first displayed inequality · OCR
- **OCR:** `\frac{C}{K} \leq \frac{\psi(2 R+1)}{\psi_{2 M^{2} U}(…)} … \leq\left(\frac{2 M(U+1)}{\left.4 M^{2} U-1\right)}\right)^{2 R}`
- **Scan:** numerator $\psi_{M(U+1)}(2R+1)$; last fraction $\bigl(2M(U+1)/(4M^2U-1)\bigr)^{2R}$.
- **Reconstruction:** as in the scan.

### 1982-36 · p. 557, beginning of the sufficiency proof · TYPO
- **OCR = scan:** `(B4), (B5) and (B6) imply $U \geq 64, Y \geq 64, M \geq 512$ and $A \geq 33280$.`
- **Reconstruction:** "(B5), (B6), (B9), (B10) and the initial conditions imply …"
- **Justification:** $U=N^2w\geq64$ by (B9), $Y=N^2s\geq64$ by (B10) (with $N\geq8$), $M=RY\geq512$ by (B5), $A=M(U+1)\geq512\cdot65=33280$ by (B6). (B4) is not used.

### 1982-37 · p. 557, after the first displayed inequality · ORIG
- **OCR = scan:** `contradicting (B3) and (B10) which imply $Y \leq 1$.`
- **Reconstruction:** "contradicting (B3) and the bound $Y\geq64$ from (B10)."
- **Justification:** $C/K<1/2$ together with (B3), $(C/K-Y)^2<1/4$, forces $Y<1$; this contradicts $Y\geq64$ from (B10). The printed wording attributes "$Y\leq1$" to (B10), which gives the opposite bound.

### 1982-38 · p. 557, before inequality (4) · TYPO
- **OCR = scan:** `By (B2) and (3) we get`
- **Reconstruction:** "By (B3) and (3) we get"
- **Justification:** (4), $U^{R-1}<Y$, follows from $C/K>U^{R-1}+\frac12$ in (3) and the approximation (B3); the square condition (B2) plays no role.

### 1982-39 · p. 557, inequality (6) · ORIG
- **OCR = scan:** `A \geq R U^{R}>U^{R}=(N^{2} w)^{R} \geq(b w)^{R}=(w)^{R} \geq W^{3}`
- **Reconstruction:** $\ldots\geq(bw)^R=W^R\geq W^3$.
- **Justification:** $W=bw$ by (B11); $(bw)^R\neq w^R$ in general.

### 1982-40 · p. 558, before inequality (8) · ORIG
- **OCR = scan:** `Now (3) implies $\rho / 2<2 Y+1$ and (B3) implies $C / K<Y+\frac{1}{2}$. Hence by (B5)`
- **Reconstruction:** "Now (3) and (B3) give $\rho/2<C/K<Y+\frac12$, and hence $\rho<2Y+1$. Therefore, by (B5)"
- **Justification:** the first step of (8) uses $\rho<2Y+1$. This follows by chaining $\rho/2<C/K$ from (3) with $C/K<Y+\frac12$ from (B3); the printed "$\rho/2<2Y+1$" is not what (3) gives and is too weak for the displayed step.

### 1982-41 · p. 558, necessity proof of Lemma 2.25 · ORIG
- **OCR = scan:** `Since $U=N^{2} w \geq 4 N w>4 b w=8 \cdot 2^{2 R}$`
- **Reconstruction:** $U=N^2w>4Nw\geq4bw=8\cdot2^{2R}$.
- **Justification:** $N\geq8$ gives $N^2w>4Nw$ strictly; $N\geq b$ gives only $4Nw\geq4bw$. The printed strict inequality would need $N>b$.

### 1982-42 · p. 558, inequality (10) · TYPO
- **OCR = scan:** `(C/K)-\rho<R\rho/2 M^{2} U`
- **Reconstruction:** $(C/K)-\rho<R\rho/(2M^2U)$.
- **Justification:** the whole of $2M^2U$ is the denominator, as in (1) and (9).

### 1982-43 · p. 558, end of the proof of Lemma 2.25 · TYPO
- **OCR = scan:** `Lemma 2.5 is proved.`
- **Reconstruction:** "Lemma 2.25 is proved."

### 1982-44 · p. 559, Lemma 2.26 · CLAR
- **OCR = scan:** `For $R, N, b$ as in Lemma 2.25. If $3<3B_1 \leq B \leq Q \leq N \leq R$, …`
- **Reconstruction:** "For $R,N,b$ as in Lemma 2.25, take the new witnesses $C_1,D_1,\Delta$ to be positive integers (with $D_1$ needed only in the primed system). If …"
- **Justification:** Lemma 2.23 needs $C_1>0$ (1982-31), and the $\chi$-form (C1′) needs the positive Pell coordinate $D_1$. The Lean proof (`Jones1982.lemma_2_26`) supplies positive witnesses in both directions.

### 1982-45 · p. 559, Lemma 2.26, the two groups of conditions · OCR
- **OCR:** a single `gather` with labels (C1), (C2) only; `C_{1}=B_{1}+\Delta(A-1) \text { or }` and the primed equations unlabelled.
- **Scan:** six labelled lines (C1), (C2), (C3) "… or", (C1′), (C2′), (C3′).
- **Reconstruction:** two aligned groups (C1)–(C3) and (C1′)–(C3′) separated by "or"; the congruences are set with `\pmod`.

### 1982-46 · p. 559, remark after Lemma 2.27 · TYPO
- **OCR = scan:** `then (A2) may be replaced by $E=i J C^{2}$`
- **Reconstruction:** "then (A3) may be replaced by $E=iJC^2$".
- **Justification:** the equation that defines $E$ is (A3), $E=iJDC^2$; (A2) defines $D$.

### 1982-47 · p. 560, Lemma 2.28, (P7) · ORIG
- **Classification:** first classified as OCR ("the scan has the numeral 1"); the scan prints a capital italic $I$, the same glyph as in $I^2$ on the left.
- **OCR = scan:** `I^{2}=(G^{2}-I) H^{2}+1`
- **Reconstruction:** $I^2=(G^2-1)H^2+1$.
- **Justification:** (P7) is the Pell equation with parameter $G$, as in (A7), $I=(G^2-1)H^2+1$, in (Q3), and in (D37).

### 1982-48 · p. 560, remark after Lemma 2.28 · ORIG
- **OCR = scan:** `Of course (P5) may be replaced by $G=A^{2}+F^{2}(F^{2}-A)$.`
- **Reconstruction:** $G=A+F^2(F^2-A)$.
- **Justification:** an alternative to (P5) must keep $G\equiv A\pmod{F^2}$, as (P5) does; the printed form gives $G\equiv A^2\pmod{F^2}$, which differs from $A$ in general. The corrected form is the one used in (D35). The difference between $D^2$ and $F^2$ is not a correction: see Part 6.

### 1982-49 · p. 560 (remark after Lemma 2.28) and p. 567 (proof of Theorem 3) · TYPO
- **OCR = scan:** `$D=W+C(A-V)(\bmod 2 A V-V^{2}-1)$`
- **Reconstruction:** $D\equiv W+C(A-V)\pmod{2AV-V^2-1}$.
- **Justification:** a congruence written with "=". Lemma 2.22 itself prints $\equiv$ for the same relation.

### 1982-50 · p. 560, beginning of §3 · CLAR
- **OCR = scan:** `Let $(\nu,\delta)$ be a universal pair. Then any r.e. set …` and `Also, we may suppose that, for all $x \geq 0, P(x,0,0,\ldots,0) \neq 0$ and hence that $P(x,0,0,\ldots,0) \geq 1$ and in particular $P(0,0,\ldots,0) \geq 1$.`
- **Reconstruction:** "Let $(\nu,\delta)$ be a universal pair furnished by a normalized, nonnegative sum-of-squares representation, as described below." and "Choose the representing polynomial to be nonnegative (a sum of squares) and normalized so that $P(x,0,\ldots,0)\neq0$ for every $x\geq0$. Then $P(x,0,\ldots,0)\geq1$, and in particular $P(0,\ldots,0)\geq1$. Such a normalized quartic representation is supplied by the quadratic system of §5, with positive witnesses shifted to nonnegative variables; one may fix admissible indices with $u>2z$, so that its equation (D9) cannot hold when all the shifted witnesses are zero. Nonvanishing alone, without the nonnegative normalization, would not justify the displayed sign conclusion."
- **Justification:** "$\neq0$ hence $\geq1$" is false for sign-changing integer polynomials. The repair uses a sum of squares (nonnegative) and does not square an arbitrary degree-$\delta$ polynomial, which would double its degree. At the shifted zero tuple every original positive witness equals 1, and the (D9) residual $l-u-t(B-2z)$ equals $2z-u\neq0$ because $u\geq(2z)^5>2z$ for $\nu\geq1$. Proved in Lean (`index_normalized`, `quartic58_index_normalized`). The forward reference to §5 is removed by 1982-51.

### 1982-51 · p. 560, after the normalization sentence · CLAR
- **OCR:** no such text.
- **Reconstruction:** a paragraph headed "Editorial proof-order clarification": take any nonnegative quartic sum of squares $P_0(x,\mathbf z)$ and use $P_{\mathrm{init}}(x,\mathbf z,t)=P_0(x,\mathbf z)+(t-1)^2$. It represents the same set over nonnegative witnesses, satisfies $P_{\mathrm{init}}(x,\mathbf0,0)=P_0(x,\mathbf0)+1\geq1$, and has degree at most four. The §5 construction accepts any finite number of starting witnesses and reduces it to 58, so the extra witness does not change the bound, and the (D9) argument of 1982-50 then normalizes the 58-witness polynomial.
- **Justification:** removes the circularity of using the output of §5 to justify the input of §3–§5. Nonnegativity is essential: $P_0=-1$, $t=0$ gives $P_0+(t-1)^2=0$ although $P_0\neq0$. The Lean formalization normalizes the 58-witness system by the witness shift alone, without a 59th witness, and supplies the initial quartic for every Diophantine set (`EnumerationQuartic`, $6n+7$ natural witnesses with a guard residual $-1$ at the zero tuple).

### 1982-52 · p. 560, the multinomial identity (3.3) · OCR
- **OCR:** `(1+z_0+z_1+\cdots+z_\nu)^\delta=\sum_{i=1} c_{i_0,i_1,\ldots,i_\nu} z_0^{i_0} \ldots z_\nu^{i_\nu}`
- **Scan:** $\sum$ with the range $i_0+i_1+\cdots+i_\nu\leq\delta$ written under it; this subscript is partly cut off at the foot of the scanned page.
- **Reconstruction:** $\sum^{*}$.
- **Justification:** the OCR misread the clipped range as `i=1`. The reconstruction uses the article's own notation $\sum^*$, which the text after (3.5) defines as "a sum with the same range as (3.3)", and 1982-53 makes that definition explicit. The two notations denote the same sum.

### 1982-53 · p. 561, definition of $\sum^*$ after (3.5) · CLAR
- **OCR = scan:** `a sum with the same range as (3.3), $i_{0}+i_{1}+\cdots+i_{\nu} \leq \delta$.`
- **Reconstruction:** "… the same range as (3.3): $i_0,\ldots,i_\nu\geq0$ and $i_0+i_1+\cdots+i_\nu\leq\delta$."
- **Justification:** the multi-indices are nonnegative integers.

### 1982-54 · p. 561 ((3.8)) and p. 565 (bound on $l$) · OCR
- **OCR:** `g<2 b B^{(\delta+1) \nu}`; `l<2 B^{(\delta+1) \nu}`
- **Scan:** $B^{(\delta+1)^\nu}$.
- **Reconstruction:** $g<2bB^{(\delta+1)^\nu}$; $l<2B^{(\delta+1)^\nu}$.

### 1982-55 · p. 561, (M4) · OCR
- **OCR:** `M_{1}=\sum_{j=0}^{(\delta+1) v} m_{j} B^{j}`
- **Scan:** upper limit $(\delta+1)^\nu$.
- **Reconstruction:** $M_1=\sum_{j=0}^{(\delta+1)^\nu}m_jB^j$.

### 1982-56 · p. 561, (M5) · OCR
- **OCR:** `D_{n}=\Gamma * P . \quad . B^{(\delta+1)^{\nu+1}-i_{0}-i_{1}(\delta+1)^{1}-\cdots-i_{\nu}(\delta+1)^{\nu}} . \tag{М5}` (Cyrillic М in the tag)
- **Scan:** "(M5) $D_0=\sum^*P_{i_0,i_1,\ldots,i_\nu}B^{(\delta+1)^{\nu+1}-i_0-i_1(\delta+1)^1-\cdots-i_\nu(\delta+1)^\nu}$"; the subscripts of $P$ are cut off at the foot of the scanned page.
- **Reconstruction:** $D_0=\sum^*P_{i_0,i_1,\ldots,i_\nu}\,B^{(\delta+1)^{\nu+1}-i_0-i_1(\delta+1)-\cdots-i_\nu(\delta+1)^\nu}$, tag (M5).
- **Justification:** the visible parts of the scan together with (3.5) and the following text ("$P_{0,0,\ldots,0}\geq1$ implies that $D_0$ is a positive integer"). With $h=(\delta+1)^{\nu+1}$ and $e(\mathbf i)=\sum_j i_j(\delta+1)^j$, the exponents $e(\mathbf i)$ are distinct (base-$(\delta+1)$ digits $0\ldots\delta$), so the coefficient of $B^h$ in $c^\delta D_0$ is $\sum^*c_{\mathbf i}P_{\mathbf i}z_0^{i_0}\cdots z_\nu^{i_\nu}=\delta!P(z_0,\ldots,z_\nu)$, as the text states. The writing of $(\delta+1)^1$ as $(\delta+1)$ is LAYOUT.

### 1982-57 · p. 562, after (M5) · CLAR
- **OCR = scan:** `$c^{\delta} D_{0}$ is a polynomial in $B$ of degree $(2 \delta+1)(\delta+1)^{\nu}$.`
- **Reconstruction:** "… of degree at most $(2\delta+1)(\delta+1)^\nu$."
- **Justification:** the top encoded digit may be zero, so the stated number is an upper bound. The argument uses only the bound.

### 1982-58 · p. 562, after (M5) · TYPO
- **OCR = scan:** `all coefficients of powers of $B$ in $c^{\delta} D_{0}$ and $<B / 2$ in absolute value`
- **Reconstruction:** "… are $<B/2$ …"

### 1982-59 · p. 562, (M9) · OCR
- **OCR:** `N_{1}=2 B^{(2 \delta+1)(\delta+1)^{\nu+1}}`
- **Scan:** $N_1=2B^{(2\delta+1)(\delta+1)^\nu+1}$, the final $+1$ on the level of the first exponent.
- **Reconstruction:** $N_1=2B^{(2\delta+1)(\delta+1)^\nu+1}$.
- **Justification:** $S_1=2E_0$ is a base-$B$ number with at most $(2\delta+1)(\delta+1)^\nu+1$ digits below $B$, so $S_1<2B^{(2\delta+1)(\delta+1)^\nu+1}$. Nesting the $+1$ into the exponent of $(\delta+1)$, as the OCR does, would be wrong.

### 1982-60 · p. 563, end of §3 · TYPO
- **OCR = scan:** `This gives the degree $47216 \times 5^{58}+9728$ or approximately $1.638 \times$` (end of page; p. 564 begins with §4)
- **Reconstruction:** "… or approximately $1.638\times10^{45}$."
- **Justification:** $47216\cdot5^{58}+9728=1\,638\,134\,072\,834\,418\,475\,395\,068\,526\,268\,005\,371\,093\,759\,728\approx1.638\times10^{45}$ (exact integer arithmetic). The power of ten and the period are missing in print. The computation of the author's degree formula $47216\cdot5^\nu+9728$ itself was not reconstructed.

### 1982-61 · p. 564, §4, first paragraph · OCR
- **OCR:** `Let the integers $P_{i_{0}, i_{1}, \ldots, i_{y}}$ be determined as before`
- **Reconstruction:** $P_{i_0,i_1,\ldots,i_\nu}$.

### 1982-62 · p. 564, (4.1), definition of $y$ · OCR
- **OCR:** `…-i_{\nu}(\delta+1) \nu}`
- **Reconstruction:** $(2z)^{(\delta+1)^{\nu+1}-i_0-i_1(\delta+1)-\cdots-i_\nu(\delta+1)^\nu}$.

### 1982-63 · p. 564, (U0) · TYPO
- **Classification:** first classified as OCR ("remove the stray closing parenthesis"); the stray parenthesis is printed in the scan.
- **OCR:** `\left.v=\left((y z u)^{2}+u\right)^{2}+z\right)`
- **Scan:** "$v=((yzu)^2+u)^2+z)$", with an unmatched closing parenthesis.
- **Reconstruction:** $v=((yzu)^2+u)^2+z$.
- **Justification:** unbalanced parenthesis in print; the OCR's malformed `\left.`/`\right)` pair only transcribes it. The final $+z$, which differs from the $+y$ of the introduction, is kept (Part 6).

### 1982-64 · p. 564, after (U0) · TYPO
- **OCR = scan:** `Still a third possbility`
- **Reconstruction:** "possibility".

### 1982-65 · p. 564 ((4.3)) and p. 566 (expansion of $-D_0$ after (U11)) · OCR
- **OCR:** `\sum_{i=0}^{4(\delta+1) \nu+1-1}`
- **Scan:** upper limit $4(\delta+1)^{\nu+1}-1$.
- **Reconstruction:** $\lambda=\sum_{i=0}^{4(\delta+1)^{\nu+1}-1}B^i$, and the same limit in $-D_0$.
- **Justification:** from (U3)–(U4), $\lambda=(q^4-1)/(B-1)$ with $q^4=B^{4(\delta+1)^{\nu+1}}$.

### 1982-66 · p. 565, application of Lemma 2.9 · OCR
- **OCR:** `m=2(\delta+1)^{2+1}`
- **Scan:** $m=2(\delta+1)^{\nu+1}$.
- **Reconstruction:** $m=2(\delta+1)^{\nu+1}$.

### 1982-67 · p. 565, (U8) · ORIG
- **OCR = scan:** `e \equiv y+m \theta`
- **Reconstruction:** $e=y+m\theta$.
- **Justification:** $m$ is the quotient witness, as in (U7) $l=u+t\theta$, in Theorems 1–3 ($e=y+m\theta$) and in (D10). A congruence without a modulus has no meaning here.

### 1982-68 · p. 565, after (4.6) · ORIG
- **OCR = scan:** `Conversely, $l$ and $e$ as given by (4.5) and (4.6) satisfy conditions (U6), (U7), (U8) and (4.4).`
- **Reconstruction:** "… satisfy conditions (U7), (U8) and (4.4). Condition (U6), which also involves $g$, is verified below for an actual code."
- **Justification:** (U6) is $elg^2<q^2$ and involves $g$, which is not yet restricted; it is proved a few lines later for a code $c$ (1982-70).

### 1982-69 · p. 565, digits of the mask after (U9) · OCR
- **OCR:** `(1 \leq i \leq v)`
- **Scan:** the glyph is ambiguous; in this typeface italic $v$ and $\nu$ are nearly identical.
- **Reconstruction:** $(1\leq i\leq\nu)$.
- **Justification:** $i$ ranges over the $\nu$ coded unknowns, by (4.5). The index $v$ is unrelated.

### 1982-70 · p. 565, the bound proving (U6) · ORIG + CLAR
- **OCR = scan:** `elg^{2}<4 z b B^{(\delta+1)^{\nu}(\delta+3)}<B B^{(\delta+1)^{\nu}(\delta+3)}<B^{(\delta+1)^\nu(2 \delta+2)}=q^{2}` (the OCR also garbles `(\delta+1)^\nu` as `(\delta+1) \nu` in the last exponent)
- **Reconstruction:** $elg^2<4zb^2B^{(\delta+4)(\delta+1)^\nu}<B^{(\delta+4)(\delta+1)^\nu+1}<B^{2(\delta+1)^{\nu+1}}=q^2$, followed by "Here $4zb^2<B$ follows from (U1), (U2) and the size of $y$, and $1<(\delta-2)(\delta+1)^\nu$. Therefore (U6) holds."
- **Justification:** with $t=(\delta+1)^\nu$, the stated bounds $l<2B^t$, $e<2zB^{(\delta+1)t}$, $g<bB^t$ multiply to $elg^2<4zb^2B^{(\delta+4)t}$, not $4zbB^{(\delta+3)t}$. The conclusion still holds: $B=b^{\delta+1}$ and $b>xy\geq y>(2z)^{(\delta+1)^{\nu+1}}$ give $4zb^2<B$, and $(\delta+4)t+1<2(\delta+1)t$ is equivalent to $1<(\delta-2)t$, true for $\delta\geq3$, $\nu\geq1$. The corrected chain is ORIG; the justifying sentence is CLAR. The chain was also checked by hand.

### 1982-71 · p. 566, after the expansion of $-D_0$ · CLAR
- **OCR = scan:** `the polynomial $-c^{\delta} D_{0}$ has much higher degree than before, namely $(5 \delta+4)(\delta+1)^{\nu}$ - 1.`
- **Reconstruction:** "… has a much higher degree bound than before, namely $(5\delta+4)(\delta+1)^\nu-1$."
- **Justification:** as in 1982-57.

### 1982-72 · p. 566, (4.9) · OCR
- **OCR:** `\sum_{i=0}^{8(\delta+1) \nu^{\nu+1}-1}`
- **Scan:** upper limit $8(\delta+1)^{\nu+1}-1$.
- **Reconstruction:** $-c^\delta D_0+\sum_{i=0}^{8(\delta+1)^{\nu+1}-1}\frac B2B^i$.
- **Justification:** besides the scan, $(5\delta+4)(\delta+1)^\nu-1<8(\delta+1)^{\nu+1}$ covers every coefficient (a check of the series lengths).

### 1982-73 · p. 566, before (U12) and after (U17) · CLAR
- **OCR = scan:** `Now define $S_{i}, T_{i}(i=1,2,3)$ by` … (U16) $S_3=-2c^4D_0+\ldots$ … `If we take $\delta=4$, then (U1)-(U17) imply that …`
- **Reconstruction:** "From this point in §4 set $\delta=4$. Now define $S_i,T_i\ (i=1,2,3)$ by" … "With $\delta=4$, (U1)–(U17) imply that …"
- **Justification:** (U16) already writes $c^4$, so the specialization $\delta=4$ has to come before it.

### 1982-74 · p. 567, proof of Theorem 3 · ORIG
- **OCR = scan:** `Conditions (U1)-(U2) imply $8 \leq r, 8 \leq N, b \leq r$ and $0<b \leq N$.`
- **Reconstruction:** "The preceding defining equations and bounds imply $8\leq r$, …"
- **Justification:** (U1)–(U2) do not mention $r$ or $N$; these bounds use (U3), (U18)–(U24) and the size estimates. The Lean proof derives $r,n\geq8$ and $b\leq n\leq r$ from the common equations and the polynomial for $r$ (`UEqs.packing_sizes`).

### 1982-75 · p. 567, proof of Theorem 3 · TYPO
- **OCR = scan:** `(cf. the remark following Lemma 2.8)`
- **Reconstruction:** "Lemma 2.28".
- **Justification:** the $\chi$-form congruence is introduced in the remark after Lemma 2.28. The accompanying $=\to\equiv$ is 1982-49.

### 1982-76 · p. 568, §5, second paragraph · OCR
- **OCR:** `(\mathrm{Cl})-(\mathrm{C} 3)`, `(\mathrm{Cl}^{\prime})-(\mathrm{C} 3^{\prime})`
- **Reconstruction:** (C1)–(C3), (C1′)–(C3′).

### 1982-77 · p. 568, §5, second paragraph · ORIG
- **OCR = scan:** `and replace (B8) by $C=C_{1}+B+\phi$.`
- **Reconstruction:** $C=C_1+B'+\phi$.
- **Justification:** Lemma 2.26 replaces (B8) by $C=C_1+B'+\phi$, where $B'=2R+1$ is the Pell index; $B$ is the digit base. (D25) has $C=2R+1+C_1+\phi$.

### 1982-78 · p. 568, definition of $B$ before (D1) · OCR
- **OCR:** `B=2(2 z)^{(\delta+1)^{\gamma+1}+1} b^{\delta}`
- **Scan:** exponent $(\delta+1)^{\nu+1}+1$.
- **Reconstruction:** $B=2(2z)^{(\delta+1)^{\nu+1}+1}b^\delta$.

### 1982-79 · p. 568, (D2) · OCR
- **OCR:** `\left.B=2 b^{\delta}(2 z)^{(\delta+1)}\right)^{\nu+1+1}`
- **Scan:** $B=2b^\delta(2z)^{(\delta+1)^{\nu+1}+1}$.
- **Reconstruction:** as in the scan.
- **Justification:** agrees with the definition in the text (1982-78). The large exponent is a constant once $z,\nu,\delta$ are fixed, so $b$ occurs with degree $\delta$.

### 1982-80 · p. 568, paragraph after (D16) · CLAR
- **OCR = scan:** `For any positive integers $x, u, z, y, x \in W_{\langle z,u,y\rangle}$ if and only if it is possible to satisfy (D1)-(D16) together with $b$ pow 2 and $\tau_{2}(S,T)=0$. To see this it is first of all necessary to check that (D1)-(D16) imply …`
- **Reconstruction:** "For each admissible coding triple $\langle z,u,y\rangle$ from (4.1), the following argument describes the coding part of the equivalence. At this stage retain the intended equation $Q=B^{(\delta+1)^{\nu+1}}$. Its replacement by (D3)–(D5) is justified only after the Pell and size conditions (D17)–(D37) have been adjoined, through Lemma 2.26. The full resulting system is equivalent to $x\in W_{\langle z,u,y\rangle}$. First check that (D1)–(D16) imply …"
- **Justification:** (D3)–(D5) alone do not force $Q=B^{(\delta+1)^{\nu+1}}$; Lemma 2.26 needs the size chain $3<3B_1\leq B\leq Q\leq N\leq R$ and the Pell system. The printed statement also quantifies over arbitrary positive $z,u,y$ (1982-05). The Lean formalization proves the size chain from (D1), (D2), (D7), (D17), (D18) without assuming the power equation, so the converse is not circular.

### 1982-81 · p. 569, upper bound for $S_3$ · CLAR
- **OCR = scan:** `which proves that $0<S_{3}$. Finally $S_{3}<N_{3}$ then follows from $B\lambda(1+Q) \leq(B\lambda+1)(1+Q)<2Q(1+Q)=2Q+2Q^{2}<4Q^{2}$.`
- **Reconstruction:** "which proves that $0<S_3$. For the upper bound, the same estimate gives $S_3<Q^2+B\lambda(1+Q)$, while [the same display]. Thus $S_3<5Q^2<8Q^2=N_3$."
- **Justification:** $D_0$ may be negative, so $-2c^\delta D_0$ can add up to $Q^2$ to $S_3$ ($2c^\delta|D_0|<Q^2$ by the preceding display). The printed argument omits this term; the conclusion holds with the margin $5Q^2<8Q^2$.

### 1982-82 · p. 569, powers of two · CLAR
- **OCR = scan:** `Now $b$ pow 2 and $z$ pow 2 imply that $B, Q$ and $N$ are also powers of 2 .`
- **Reconstruction:** "Combining $b$ pow 2 and $z$ pow 2 with (D2) and the retained equation $Q=B^{(\delta+1)^{\nu+1}}$ shows that $B$, $Q$ and $N=N_1N_2N_3$ are powers of 2."
- **Justification:** (D7) alone does not make $Q$ a power of two; the retained exponential equation (1982-80) does, and $N=Q\cdot2zQ^2\cdot8Q^2=16zQ^5$.

### 1982-83 · p. 569, coefficient argument after the expansion of $-D_0$ · TYPO + CLAR
- **OCR = scan:** `By the choice of $z$ in (D2) the polynomial $-c^{\delta} D_{0}+\sum_{i=0}^{2(\delta+1)^{\nu+1}-1}(B/2) B^{i}$ has nonnegative coefficients.`
- **Reconstruction:** "By the choice of $B$ in (D2), and the coefficient bound on $z$ preceding (4.1), the polynomial … has coefficients strictly between $0$ and $B$ at every position in this sum." It is followed by a proof: with $L=(\delta+1)^{\nu+1}$, $K=(\delta+1)^\nu$ and $B$ treated as a formal base, every coefficient of $-D_0$ has absolute value at most $z$; the coefficients of $c^\delta$ sum to $(1+z_0+\cdots+z_\nu)^\delta<((\nu+2)b)^\delta$; hence every coefficient $h_j$ of $-c^\delta D_0$ satisfies $|h_j|<z(\nu+2)^\delta b^\delta<(2z)^{L+1}b^\delta=B/2$ (using $\nu+2\leq2^{\nu+1}$ and $\delta(\nu+1)<L$); and $\deg_B(-c^\delta D_0)\leq\delta K+L<2L$. So no carries occur, and the digit in position $L$ is $B/2+\delta!P(z_0,\ldots,z_\nu)$.
- **Justification:** (D2) defines $B$, not $z$ (TYPO, confirmed in the scan). "Nonnegative coefficients" is too weak: Lemma 2.8 needs genuine base-$B$ digits, i.e. $0<h_j+B/2<B$ at every position (CLAR). The bound was also checked by hand, and the Lean formalization proves it (`coeff_shortHpoly_lt`, `short_tau3_iff`).

### 1982-84 · p. 569, (D30) · OCR
- **OCR:** `D=W+C(A-V)+r\left(2 A V-V^{2}-1\right)`
- **Scan:** a damaged Greek $\gamma$ with its descender missing, which resembles a raised "r".
- **Reconstruction:** $D=W+C(A-V)+\gamma(2AV-V^2-1)$.
- **Justification:** $\gamma$ is the congruence witness of Theorem 3 ($4a\gamma-5\gamma$) and is in the variable list after (D37); $r$ is not a variable of §5 (the capital $R$ is). The Lean proof shows that the quotient $\gamma$ is positive.

### 1982-85 · p. 570, (D33) · ORIG
- **OCR = scan:** `E=i C^{2}+1`
- **Reconstruction:** $E=iC^2$.
- **Justification:** (D33) is (P3), $E=iC^2$; the construction needs $C^2\mid E$, which the $+1$ destroys. It is also consistent with (Q2) $F^2=(A^2-1)i^2C^4+1$ and with the auxiliary list ($C^2$, $AE$).

### 1982-86 · p. 570, (D37) · ORIG
- **OCR = scan:** `I^{2}=(G-1) H^{2}+1`
- **Reconstruction:** $I^2=(G^2-1)H^2+1$.
- **Justification:** (D37) is the Pell equation (P7) with parameter $G$ (see 1982-47); (D31) with the $\chi$ form needs it.

### 1982-87 · p. 570, list of variables after (D37) · TYPO
- **Classification:** first classified as OCR; the comma is also missing in the scan.
- **OCR = scan:** `N, N_{1} N_{2}, N_{3}`
- **Reconstruction:** $N,N_1,N_2,N_3$.
- **Justification:** $N_1$ and $N_2$ are separate quantities; the count of 53 variables (34 capital, 19 lower-case) requires both.

### 1982-88 · p. 570, after the list of variables · CLAR
- **OCR = scan:** `such that conditions (D1)-(D37) hold. There are 53 variables here.`
- **Reconstruction:** "… hold. The Pell square-root witnesses $C_1,D_1,D,F,I$ are taken positive; all remaining capital quantities in this system, except the possibly signed $D_0$, may also be taken positive. There are 53 variables here."
- **Justification:** the printed list says only "integers" for the capitals. The Pell lemmas need positive roots, and $D_0$ can be negative (the text says so before the $S_3$ estimate). The Lean formalization confirms that all 52 quantities other than $D_0$ can be taken positive.

### 1982-89 · p. 570, qualifier "with $\nu\geq13$" · ORIG
- **Classification:** first classified as a clarification (the qualifier omitted as "doubtful"); the analysis below confirms the omission and shows that the printed qualifier is wrong.
- **OCR = scan:** `The pairs of high degree, with $\nu \geq 13$, were calculated by the author using the equations of §3.`
- **Reconstruction:** "The pairs of high degree were calculated by the author using the equations of §3."
- **Justification:** the pairs of very high degree in Theorem 4, $(12,\approx1.3\times10^{44})$, $(11,\approx4.6\times10^{44})$ and $(10,\approx8.6\times10^{44})$, have $\nu\leq12$, so "$\nu\geq13$" does not describe them. Systems of the §3 type keep the terms $B^{(\delta+1)^{\nu+1}}$ (degrees of order $5^\nu$), so only those pairs can come from §3. The printed bound is therefore the wrong way round (probably "$\nu\leq12$" was meant). Since the calculations are omitted, the edition does not substitute a guessed cutoff and simply drops the qualifier. The source of the intermediate pairs $(19,2668)$ and $(14,\approx2.0\times10^5)$, which fall under neither "$\delta<2668$" (Wada) nor the $10^{44}$ group, is not stated in the article and is left open.

### 1982-90 · p. 570, final relation-combining example · CLAR
- **OCR = scan:** `a=\square \wedge b=\square \Leftrightarrow \exists x \prod^{4}(x \pm \sqrt{a} \pm \sqrt{b})=0`
- **Reconstruction:** $a=\square\wedge b=\square\Leftrightarrow\exists x\in\mathbb Z_{>0}\ \prod_{\epsilon,\eta\in\{-1,1\}}(x+\epsilon\sqrt a+\eta\sqrt b)=0$.
- **Justification:** the product runs over the four independent sign choices, and $x$ must be positive (the article's convention for lower-case letters, stated explicitly). The product is $x^4-2(a+b)x^2+(a-b)^2$. If it vanishes at a nonzero rational $x$, one signed sum equals $x$, and squaring gives $\pm\sqrt a=(x^2+a-b)/(2x)\in\mathbb Q$, so $a$ (an integer) is a square, and likewise $b$. Conversely $x=\sqrt a+\sqrt b>0$ works. With $x=0$ allowed, $a=b=2$ would be a counterexample. Checked on 6,241 cases and symbolically.

### 1982-91 · p. 570, reference [1] · OCR
- **OCR:** `→ A. Baker, Contributions …`
- **Reconstruction:** "[1] A. Baker, …"

### 1982-92 · p. 570, reference [8] · BIB
- **OCR = scan:** `Acta Arithmetica, vol. 35 (1978), pp. 209-221.`
- **Reconstruction:** "vol. 35 (1979)". The repeated-author dash is expanded to "J. P. Jones".
- **Justification:** the publisher's record gives *Acta Arithmetica* 35 (1979), 209–221, DOI 10.4064/aa-35-3-209-221.

### 1982-93 · p. 571, reference [10] · OCR
- **OCR:** `N.K. KosovskiÍ`
- **Scan:** "N.K. Kosovskiǐ" (small capitals, breve).
- **Reconstruction:** "N. K. Kosovskiǐ".

### 1982-94 · p. 571, reference [12] · OCR
- **OCR:** `NorthHolland`
- **Scan:** "North-" at a line end, "Holland" on the next line.
- **Reconstruction:** "North-Holland".

### 1982-95 · p. 571, reference [13] · BIB
- **Classification:** first classified as OCR; the scan prints "transl," without a period.
- **OCR = scan:** `English transl, Russian Mathematical Surveys`
- **Reconstruction:** "English transl., Russian Mathematical Surveys", as in the other references.

### 1982-96 · p. 571, references [14], [16], [17], [18] · BIB
- **Classification:** first classified as OCR; the scan prints "Mathematičeskogo" in these four references and "Matematičeskogo" in [10].
- **OCR = scan:** `Mathematičeskogo`
- **Reconstruction:** "Matematičeskogo" throughout.
- **Justification:** the standard transliteration of *Математического*, consistent with [10].

### 1982-97 · p. 571, reference [17] · BIB
- **Classification:** first classified as OCR; the scan prints "Naučhnyh".
- **OCR = scan:** `Naučhnyh`
- **Reconstruction:** "Naučnyh", as in [10], [14], [16], [18].

### 1982-98 · p. 571, reference [19] · BIB
- **OCR = scan:** `Foundations of mathematics and computability theory (Butts and Hintakka, editors)`
- **Reconstruction:** "Logic, Foundations of Mathematics, and Computability Theory (R. E. Butts and J. Hintikka, editors)".
- **Justification:** the publisher's record of the volume, DOI 10.1007/978-94-010-1138-9; the editor's name is Jaakko Hintikka.

### 1982-99 · p. 571, reference [22] · BIB
- **OCR = scan:** `Zur theorie der quadratischen formen`
- **Reconstruction:** "Zur Theorie der quadratischen Formen".
- **Justification:** German nouns are capitalized.

### 1982-100 · p. 571, reference [23] · BIB
- **OCR = scan:** `Über die Ergänzungssätze zu der Allgemeiner Reziprozitätsgesetzen`
- **Reconstruction:** "Über die Ergänzungssätze zu den allgemeinen Reciprocitätsgesetzen".
- **Justification:** the publisher's record, DOI 10.1515/crll.1852.44.93, with its historical spelling; the printed case endings are wrong.

### 1982-101 · p. 571, reference [25] · OCR
- **OCR:** `[25] → → -, Existential definability in arithmetic`
- **Scan:** "[25] ———, Existential definability …" (the dash stands for Julia Robinson, the author of [24]).
- **Reconstruction:** "[25] Julia Robinson, Existential definability in arithmetic, …"

## 5. Editorial additions

Every addition to the text is a register entry above. They are:

- **Marked in the article as editorial** (footnotes or labelled paragraph):
  the footnote on admissible coding triples in §1 (1982-05); the heading
  "(certificate interpretation)" and the footnote of Theorem 5 (1982-15); the
  footnote on the citation [23]→[25] (1982-28); the paragraph "Editorial
  proof-order clarification" in §3 (1982-51); the footnote to the heading of
  Theorem 4 (1982-11).
- **Unmarked inline additions** (domain statements, hypotheses and proof
  completions): 1982-13 ("effectively"), 1982-16 (domain paragraph of §2),
  1982-17, 1982-18, 1982-25 (domain of $n$), 1982-27, 1982-29, 1982-30,
  1982-31, 1982-44, 1982-50, 1982-53, 1982-57, 1982-70 (justifying sentence),
  1982-71, 1982-73, 1982-80, 1982-81, 1982-82, 1982-83 (no-carry proof),
  1982-88, 1982-90.
- **Rewritten claims of the author** (not marked in the text): 1982-12, 1982-14, 1982-68, 1982-74,
  1982-89 (qualifier deleted).
- **Apparatus:** the edition notice, title block and pagination marks (Part 3).

## 6. Readings examined and retained

- **(3.14), p. 563.** An earlier version of these notes said that the scan
  omits $n$ from the existential quantifier and that the OCR had repaired it.
  The scan in fact prints "$\exists g,h,i,j,s,w,\varepsilon,\phi,n\
  M_2(\ldots)=0$", so the scan, the OCR and the reconstruction agree and there
  is no discrepancy.
- **Alternative Pell parameters.** Theorem 3's last equation and (Q3) use
  $a+f^2(d^2-a)$ ((P5) form), while (D35) uses $G=A+F^2(F^2-A)$. The remark
  after Lemma 2.28 permits the $F^2$ version, and it allows the single $F^2$
  auxiliary in the §5 degree reduction. Both are kept (both forms proved in
  Lean, `Jones1982.lemma_2_28`). Only the printed $A^2$ in the
  remark was wrong (1982-48).
- **(U0) ends in $+z$, the introduction's code in $+y$.** Both are injective
  on positive triples. For $v=((zuy)^2+u)^2+y$: with $t=zuy$, $s=t^2+u$ and
  $1\leq y\leq t<s$, the integer square root of $v$ is $s$ with remainder
  $y$; then that of $s$ is $t$ with remainder $u$, and $z=t/(uy)$. The $+z$
  variant is inverted the same way. Not harmonized.
- **Theorem 4 has twelve pairs.** The 1980 announcement's sixteen-pair table
  is a different list; no row is missing.
- **"R. Krisnis"** (remark after Lemma 2.27) is the original spelling; kept.
- **Lemma 2.25:** the necessity proof says "since $A\geq32768$" and the
  sufficiency proof derives $A\geq33280$; both are true, so both are kept.
  The sentence before (5) lists "(B6), (B7), (B9), (4)" although (B5) and
  (B12) are also used; kept. In (13) one chain has $N^N\leq U^R$ and the other
  $N^N<U^R$ (the strict form holds); kept.
- **Reference style kept as printed:** [13] has no "pp.", [10]
  prints "pp.49-59", [3] has a spaced colon; [5], [6] and [20] are never cited
  in the text; the "to appear" of [6] is kept as a historical statement.
  [11]'s "354–357" is the correct page range of the English translation (the
  corpus-wide 354–357 / 354–358 question is settled in favour of 357 by the
  *JSL* Reviews record of the translation), so 1982 needed no change.
- **Proof details checked in the Lean formalization, no edit:**
  the sign $D_0>0$ used after (U17) is established before (4.9) from
  $e<q^2<q^3<\lambda<z\lambda$; the weaker (U6′) of Theorem 2 already gives the
  six block bounds; positivity of $\eta$, of the new witnesses of Theorem 2,
  and of $\gamma$ in Theorem 3 follows from the equations; in Lemma 2.27,
  working modulo $C$ admits $B+t_0=C$, which parity excludes and which
  otherwise occurs only in the harmless case $A=B=t_0=2$, $C=4$; in (D8) the
  valid bound is $e<2zQ$, which the text uses; Theorem 2's $w$ (in $b=2^w$)
  and Theorem 3's $w$ (in $U=n^2w$), and Theorem 2's $\eta$ (the
  central-binomial quotient) and Theorem 3's $\eta$ (the approximation
  slack), are different witnesses with the same names.
- **Degree convention of §5.** "4 and 58 take into account the degree of
  occurrence of $x$ but not that of the other parameters $z,u,y$"; the
  remark that 57 would suffice without counting $x$ is kept.
- **Spelling.** A dictionary check of all prose words found no
  other misspelling besides 1982-04 and 1982-64.

## 7. Verification summary

*Programs.* The verification programs are
`Papers/verification/jones1982_verification.py`, `corpus_cross_review.py` (the $r$
and $p$ formulas of 1980 and 1982, parsed from the current sources) and
`corpus_review.py` (the (D2) source text and coefficient encoding). They were re-run
on 24 September 2026; all pass.

- **Scan comparison.** The text was compared with every page of the scan.
  In addition a normalized word-level diff against the OCR, a diff of all
  multi-digit numbers against the scan, and a check that every equation label
  and cross-reference resolves were made. For these notes the OCR and the
  reconstruction were compared token by token (with whitespace,
  markup, and `\allowbreak`/`\origpage` normalized, and a second pass
  preserving braces to catch exponent-nesting differences). Every difference
  found is covered by Part 3 or Part 4. The scan regions of the classification-sensitive
  entries were checked again at high resolution.
- **Symbolic and numeric checks** (exact arithmetic). The results of the
  following checks are recorded here, since not every script that produced
  them is kept: 6,400 Kummer valuation instances, 2,128 two-block packings,
  341 instances of Lemma 2.16, 10,368 of Lemma 2.9, 45 coefficient extractions for (M5) with signed
  coefficients ($\delta=3,4$; $\nu=1,2$), 6,241 instances of the four-sign
  example; symbolic identities for the $r$ packing (1982-08), $p=2ws^2r^2n^6$
  (1982-09) and the four-sign product; an explicit 58-unknown system of 46
  residuals, each of degree at most 2 counting $x$ (36 retained unknowns plus
  22 auxiliaries; the packed $T$ ends in $-4zv_{10}$); the $r$ and $p$
  formulas parsed from the TeX source and compared with the derivations; all 46
  residuals eliminated; the binary Lucas/Kummer equivalence on 32,896 pairs;
  the $\chi$-form Pell congruence on 2,508 instances; the exact value of
  $47216\cdot5^{58}+9728$; 276 encoding cases (12 of them zeros of $P$)
  for the coefficient bound, support and bit mask of 1982-83; the bootstrap
  of 1982-51 on $0\leq P_0,t\leq20$ with the negative counterexample. Further
  checks are made by
  `Papers/verification/round4_1982_checks.py` (results in
  `round4_1982_results.json`: digit and carry lemmas, Lemma 2.9, the Pell
  lemmas, the packing identity of Theorems 1–3, the degree $D_9$) and
  `Papers/verification/round4_1982_lemma225.py` (`round4_1982_lemma225_results.json`:
  an exact instance of Lemma 2.25 with $R=63$, $N=b=8$, all of
  (B1)–(B14), (B8′) and the $\chi$-form congruence, with
  $C=\psi_A(127)$ of about $10^6$ bits).
- **Lean formalization** (`Lean/Diophantine/Paper1982/`, status in
  `Lean/STATUS.md`). This machine-checks, with only the standard axioms,
  the lemmas of §2 (Kummer's theorem, Lemmas 2.1–2.28, Corollary 2.29),
  Theorems 1–3 in their corrected form (12, 14 and 28 positive witnesses,
  $q=b^{5^{\nu+2}}$, the $q^7$/$q^8$ packing, $p=2ws^2r^2n^6$), the complete
  §5 system (D1)–(D37) with the corrections of 1982-77, 1982-84 to 1982-87, its
  reduction to 46 quadratic equations in 58 witnesses and the normalized
  quartic, the universal pair $(58,4)$ as one joint polynomial, and §3's
  reduction to nine unknowns. It found no further error in the article's
  equations. The count of 100 operations in Theorem 5 is examined in the
  satellite article to the 1980 announcement (`Papers/1980/`); it is not
  part of this article's corrections beyond 1982-15.

---

*Counts.* The register has 101 entries: OCR 29; ORIG 23 (of which two are
ORIG + CLAR and one ORIG with a LAYOUT restatement); CLAR 23; TYPO 18 (of
which one is TYPO + CLAR); BIB 8. EDN and LAYOUT differences are treated
systematically in Part 3 (and in parts of 1982-08, 1982-10, 1982-19 and
1982-56).
