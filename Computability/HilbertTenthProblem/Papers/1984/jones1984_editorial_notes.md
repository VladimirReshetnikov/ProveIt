# Editorial notes: Jones and Matijasevič (1984)

**J. P. Jones and Y. V. Matijasevič, *Register machine proof of the theorem on
exponential diophantine representation of enumerable sets*, The Journal of
Symbolic Logic 49 (3), September 1984, pp. 818–829, DOI
[10.2307/2274135](https://doi.org/10.2307/2274135).**

This document explains every discrepancy between three objects:

- **the scan**: `original/1984/jones1984.pdf`, twelve printed pages, 818–829;
- **the naive OCR reading**: `original/1984/jones1984.tex`, the Mathpix OCR of
  the scan;
- **the reconstruction**: `Papers/1984/jones1984_corrected.tex` and its PDF,
  the reconstructed intended mathematical content of the article.

Every entry describes the edition in its current state. A dated log of
revisions and checks across the corpus is `Papers/EDITORIAL_NOTES.md`; its
row identifiers (such as `84-R4-03`) are cited here where a change is
registered there. Page numbers are those of the original printing; the
reconstruction marks them in its margin as `[818]` … `[829]`. The footnotes
of the reconstruction that say "see the editorial notes" refer to this
document.

Stated counterexamples and identities were rechecked with exact integer
arithmetic for this document.

## 1. Classifications

| Code | Meaning |
|---|---|
| **OCR** | Transcription defect: the scan is right, the OCR is wrong. |
| **ORIG** | Error in the printed original, corrected in the reconstruction. |
| **CLAR** | Editorial clarification, stated hypothesis or proof completion added to the text. Where the text marks it (an "Editorial note" footnote or an italic label), the entry says so. |
| **TYPO** | Typographical, grammatical or cross-reference slip in the original. |
| **BIB** | Bibliographic correction or normalization. |
| **EDN** | Edition apparatus: notices, pagination marks, metadata. |
| **LAYOUT** | Reflow or typesetting with no change of content. |

## 2. Systematic differences

These classes of difference are described once here, not item by item. The
direct comparison of OCR and reconstruction (section 7) found no difference
outside them that is not in the register of section 3.

1. **Reflow and document structure (LAYOUT).** The text is re-typeset in a
   new page layout. It is not a facsimile. Hard line breaks (`\\`, `\\[0pt]`)
   and page-break fragments are removed. This includes the sentence on
   p. 818–819 that the OCR splits around the first-page footnote ("…every
   recursively enumerable" / "relation could be represented"). The Mathpix
   preamble (the footnote-marker override, `mhchem`, `stmaryrd`, the Unicode
   arrow workaround) is replaced by the edition's own preamble. Long displays
   (1), (2), (5), (47) and (49) are broken over two lines. Running heads
   ("DIOPHANTINE REPRESENTATION OF ENUMERABLE SETS", "J. P. JONES AND Y. V.
   MATIJASEVIČ") are replaced by "Jones–Matijasevič / Corrected edition". The
   capitalised title is set in sentence case. The run-in section headings
   ("§1. Introduction.") become unnumbered section headings without the final
   period. The addresses are set in small capitals in two blocks.
2. **Emphasis (LAYOUT).** The scan italicises defined terms (*exponential
   diophantine*, *parameters*, *unknowns*, *register machines*, *singlefold*,
   *unary*, *steps*, *contents*, *location j*, *accepts*, *starting condition*,
   *register equations*, *macros*, *polynomial time*, …) and sets
   DEFINITION, LEMMA and PROOF in small capitals. The OCR drops the italics,
   and the reconstruction follows the OCR. It sets **Definition**, **Lemma**
   and *Proof* in bold or italic. The bibliography's typography (small-capital
   author names, italic titles, bold journals and MR volumes) is not
   reproduced either.
3. **Equation numbers (LAYOUT, with OCR repairs listed in section 3).** All
   original numbers (1)–(54) are kept, each exactly once and in order. The
   numbers that the OCR lost, (18), (20), (22) and (41), are restored as
   register entries 1984-12, 1984-14, 1984-18 and 1984-29. The OCR's
   `\tag{}` positions inside `array` environments are replaced by `align` or
   `gather` displays.
4. **Notation normalized (LAYOUT).**
   - Masking is always $\preccurlyeq$. Where the OCR misread it as $\leqslant$,
     this is an OCR repair (1984-09). Numerical order is always $\leq$. The
     scan's $\leqq$ (p. 820, "less than or equal to"; p. 827, $s\leqq
     P(|x|)$) is set as $\leq$.
   - The scan prints the ceiling and floor with corner brackets
     (⌜ ⌝, ⌞ ⌟). The reconstruction uses $\lceil\ \rceil$ and
     $\lfloor\ \rfloor$. The places where the OCR garbled them are OCR entries
     (1984-05, -28, -29, -31, -32, -34).
   - The ampersand has two roles in the scan. As bitwise AND in (10) and (11)
     it is set as $a\mathbin{\&}b$. As logical "and" it is set as $\land$: in
     (5), in (53), and in the shorthand $(\exists y)[|y|\leq P(|z|)\land\dots]$.
     The final sentence of §5 still names the logical operation "\&", as
     printed. (5) is also given parentheses:
     $(A=0\ \text{or}\ B=0)\leftrightarrow AB=0$ and
     $(A=0\land B=0)\leftrightarrow A^2+B^2=0$.
   - The scan's $Z_p[x]$ and $Z_p$ are set as $\mathbb Z_p[x]$ and
     $\mathbb Z_p$. The divisibility bar is set as $\mid$. In (43),
     $\Leftrightarrow$ and $(\bmod 2)$ are set as $\Longleftrightarrow$ and
     $\pmod 2$. Arrows $\leftrightarrow$ in (1) and (2) are set long. The OCR's
     `rem $(x, y)$` is set as $\operatorname{rem}(x,y)$.
5. **Punctuation and spacing (OCR/LAYOUT).** Mathpix inserts a space before
   punctuation after mathematics: `power of 2 :`, `0 and 1 , in place`,
   `instead of $x$ )`, `power of 2 .` (twice), `equal to 1 .`,
   `R k(i \neq j \neq k \neq i)$ :`, `Condition (22)(and`, `the $t$ th`. The
   scan has none of these, and the reconstruction removes them (84-R4-03;
   OCR). Straight ASCII quotes (`"and"`, `"Nauka"`, `"tag"`) become
   typographic quotes (84-R4-07). Page ranges use en dashes throughout, both in
   the text (Minsky [1967, pp. 170–172, 204–206], twice; 84-R4-02) and in the
   bibliography. The OCR's `vol. 54(1947)` and `no. 5(167)` get a space before
   the parenthesis. `MR 81f: 03055` (spaced as in the scan) becomes
   `MR 81f:03055`. The initials `V.A.` become `V. A.` (in the scan too they are
   unspaced). Accented names use portable LaTeX escapes.
6. **Example 1 punctuation (LAYOUT).** The scan ends every line of the
   program with a comma and the last line with a period (`L14 STOP.`). The
   reconstruction drops this line-final punctuation and sets the program as one aligned array. Commas *between* parallel
   assignments are kept.
7. **Edition apparatus (EDN).**
   - A journal line ("The Journal of Symbolic Logic 49 (3), September 1984,
     pp. 818–829"), the original DOI and the line "Corrected, re-typeset
     edition • 13 September 2026" are added.
   - An edition notice is added. It says that equation numbers are retained,
     that this is an editorial reconstruction, that bracketed margin numbers
     mark original page starts, and where changes are explained: every
     discrepancy in this document, and "a dated log of revisions and checks
     is `Papers/EDITORIAL_NOTES.md`" (84-R4-10).
   - Header comments in the source record the revision state: "% Continuously
     revised edition; last source revision 24 September 2026." and "% A dated
     log of revisions and checks is ../EDITORIAL_NOTES.md."
   - `\origpage{n}` marks set a bold `[n]` in the margin on the line where
     journal page n begins, twelve marks for pp. 818–829. Pages 823 (inside
     Example 1, at L7), 824 (at (28)) and 828 (the reference list) were
     placed by hand from the scan.
   - The macro `\ednote` ("Editorial note." footnotes) marks the editorial
     interventions, and `\bibentry` sets hanging-indent references. An unused
     `\originalpage` macro was removed (84-R4-06).
   - The PDF metadata title is "Register machine proof of exponential
     Diophantine representation: corrected edition".
8. **Figure/table handling (LAYOUT).** The history table of p. 824 is
   rebuilt. See 1984-21 for its content.

## 3. Discrepancy register

The register is ordered by position in the original. "OCR" quotes
`original/1984/jones1984.tex`; "Scan" is given where the scan differs from the
OCR or where it decides the classification; "Now" is the text of
`Papers/1984/jones1984_corrected.tex`. Identifiers of the form `84-R4-nn`
are rows of the dated log `Papers/EDITORIAL_NOTES.md`.

### 1984-01 · p. 818, first-page footer · EDN
- **OCR:** has the received dates, the subject classification and the
  acknowledgement footnote, but not the copyright line.
- **Scan:** "©1984, Association for Symbolic Logic 0022-4812/84/4903-0009/$02.20".
- **Now:** "© 1984 Association for Symbolic Logic. Original publication code:
  0022-4812/84/4903-0009/\$02.20." It is set with the received dates and the
  classification under the title block. The acknowledgement becomes the
  footnote to the authors' names.
- **Justification:** publication metadata the OCR omitted, restored from the
  scan.

### 1984-02 · p. 818 §1; p. 827 §5 (four times) · OCR
- **OCR:** `the class $N P$`, `characterization of $N P$`, `belongs to $N P$`,
  `the class $N P$`, `$A \in N P$`.
- **Now:** $\mathrm{NP}$ in all places. The §5 section text's "class NP" was
  already upright in the OCR.
- **Justification:** the scan's italic *NP* is a class name, not the product
  $N\cdot P$.
- **Log:** 84-R4-01 for the last occurrence.

### 1984-03 · p. 819 §1, definition of *unary* · TYPO
- **OCR:** `Unary (Russian, oonarnoe) means that…`
- **Scan:** the same, "*Unary* (Russian, *oonarnoe*)".
- **Now:** "Unary (Russian, унарное)", and in the preceding sentence
  "Singlefold (Russian однократное; French univoque)" for the printed
  "(Russian odnokratnoe; …)". A footnote records the printed Latin spellings
  *odnokratnoe* and *oonarnoe* and explains the second.
- **Justification:** *oonarnoe* is an English-phonetic spelling of Russian
  *унарное* ("unary"; standard transliteration *unarnoe*), not a corruption.
  Both Russian terms are therefore given in Cyrillic, which removes the
  transliteration question.
- **History:** an earlier revision of this edition took *oonarnoe* for a
  corrupted transliteration and printed "Unary (one-place)" with a footnote
  giving the English meaning. That reading was reverted (84-R4-09): the
  Russian parenthesis is restored and both Russian words are set in Cyrillic.
  In that earlier revision the footnote marker sat on the §2
  domain-conventions sentence (p. 820); it now sits on the emended word
  (84-R4-04).

### 1984-04 · p. 819 §1 and p. 820 §2, "one place" / "two place" · TYPO (p. 819), OCR (p. 820)
- **OCR:** `only one place exponentials`, `two place exponentials` (p. 819);
  `they contain twoplace exponential functions` (p. 820).
- **Scan:** p. 819 prints "one place" and "two place" without hyphens. On
  p. 820 "two-" is hyphenated at a line end ("two-/place"), which the OCR
  merged into "twoplace".
- **Now:** "one-place", "two-place" throughout.
- **Justification:** these are compound adjectives. The next sentence of the
  scan itself writes "two-place" and "one-place".
- **Classification:** both places were first classified TYPO; the scan shows
  that the p. 820 form is an OCR merge of a line-end hyphenation.

### 1984-05 · p. 820 §2, notation paragraph · OCR + CLAR
- **OCR:** `…(nonnegative integers), $q$ pow 2 means that $q$ is a power of $2 .{ }_{\lfloor } x_{\rfloor}$and ${ }^{r} x^{7}$ are the floor and the ceiling of $x$, rem $(x, y)=$ remainder after $x$ is divided by $y$.`
- **Scan:** "…(nonnegative integers). *q* pow 2 means that *q* is a power of 2.
  ⌞x⌟ and ⌜x⌝ are the floor and the ceiling of *x*. rem(x, y) = remainder
  after *x* is divided by *y*."
- **Now:** "…(nonnegative integers). The notation $q$ pow 2 means that $q$ is a
  power of $2$; $\lfloor x\rfloor$ and $\lceil x\rceil$ are the floor and the
  ceiling of $x$; and $\operatorname{rem}(x,y)$ is the remainder after $x$ is
  divided by $y$, with $y>0$. We use $x^0=1$ (also when $x=0$), and
  $\binom nk=0$ when $k>n$." The footnote reads *Editorial note. The domain
  conventions are made explicit here.*
- **Justification:**
  - OCR: the floor and ceiling brackets were garbled into sub- and
    superscripts (`{ }^{r} x^{7}`).
  - CLAR: the positive modulus, $0^0=1$ and $\binom nk=0$ for $k>n$ make the
    natural-number relations used later total. Examples are (6) with $0<c$,
    (8) at $k>n$, and (9) at $x=0$.
  - LAYOUT: the rewording "The notation … means", the semicolons, and "is the
    remainder" in place of "= remainder"; the content is unchanged.

### 1984-06 · p. 820 §2, after (3): divisibility · CLAR (marked)
- **OCR:** `Further examples would be the relations $\leqq$ (less than or equal to), $\neq$ and | (divisibility).`
- **Now:** the same sentence, with $\leq$ and $\mid$ (section 2, item 4) and
  an editorial footnote. The footnote says that divisibility remains singlefold
  when zero is allowed, but $0=0q$ does not determine $q$. A uniform repair is
  $a\mid b\leftrightarrow\exists q,t\,[b=aq\land b=q+t]$. It adds that for
  $a>0$ the quotient is unique and $q\leq b$, that for $a=b=0$ the second
  equation forces $q=t=0$, and that the two equations combine by (5).
- **Justification:** the printed assertion is correct. The footnote supplies a
  definition that is singlefold on the whole domain.
  - For $a>0$ and $a\mid b$: $q=b/a\leq b$ is unique, so $t=b-q$ is unique.
  - For $a=0<b$ there is no solution.
  - For $a=b=0$: $q=t=0$.
  - Combined: $(b-aq)^2+(b-q-t)^2=0$.
  - The witness count was also checked exhaustively for $0\leq a,b\leq 64$.
    The proof above covers all inputs.

### 1984-07 · p. 820 §2, before (4) · CLAR (unmarked)
- **OCR:** `Another example would be the relation of congruence`
- **Now:** "… of congruence (for $c>0$)".
- **Justification:** for $c=0$ the witness $x$ in (4) is arbitrary when $a=b$,
  so the singlefold reading needs $c>0$. The congruence is used in (6) only
  with $0<c$.

### 1984-08 · p. 821 §2, after (9) · CLAR (unmarked)
- **OCR:** `Formula (9) is easy to prove using $2^{x y} \equiv x\left(\bmod 2^{x y}-x\right)$.`
- **Now:** the same sentence, followed by: "The cases $y=0$ and $y=1$ are
  handled separately by $x^0=1$ and $x^1=x$; auxiliary variables belonging to
  an unused case may be fixed to zero to preserve singlefoldness."
- **Justification:** (9) is stated for $1<y$ and is correct there (section 5).
  Replacing every two-place power in (8) needs the cases $y\in\{0,1\}$ too. The
  three cases are disjoint, so fixing unused auxiliaries to zero keeps the
  representation singlefold.

### 1984-09 · pp. 821 and 825, the masking symbol · OCR
- **OCR:** `$\leqslant$` in five places:
  - "Next we define a new binary relation, $\leqslant$ (masking)";
  - "Definition. $r\leqslant s$ if and only if …";
  - "The relation $\leqslant$ has …";
  - "$r\leqslant s$ implies $r\leq s$";
  - "Lemma. $r\leqslant s$ if and only if $\binom sr\equiv1\pmod 2$";
  - and p. 825 "i.e. $Q L_{i} \leqslant L_{i+1}$".
- **Scan:** the curly masking sign ≼ everywhere, as in (10)–(13).
- **Now:** $\preccurlyeq$ in all places.
- **Justification:** masking and numerical order differ. The text itself says
  that $r\preccurlyeq s$ *implies* $r\leq s$.

### 1984-10 · p. 821 §2, (12) · CLAR (unmarked)
- **OCR and scan:** $a \text{ pow } 2 \leftrightarrow a \preccurlyeq 2a-1$.
- **Now:** $a \text{ pow } 2 \leftrightarrow a>0\ \text{and}\ a\preccurlyeq 2a-1$.
- **Justification:** at $a=0$, $2a-1$ is not a natural number. Under truncated
  subtraction $0\preccurlyeq 0$ would make 0 a "power of 2". The guard makes
  the natural-number reading exact. It is the form proved in Lean
  (`JM1984.pow_two_iff_mask`: `a pow 2 ↔ 0 < a ∧ a ≼ 2a−1`). The scan
  confirms that the guard is editorial.

### 1984-11 · p. 822 §3 · TYPO
- **OCR and scan:** `In addition, to a STOP command we suppose…`
- **Now:** "In addition to a STOP command …"
- **Justification:** stray comma in the printed text.

### 1984-12 · p. 822 §3, commands (15)–(18) · OCR
- **OCR:** splits the display into a `COMMAND` heading with (15), (16) and an
  `array` holding both (17) and (18). A separate `MEANING` heading follows with
  the four meanings as loose lines. The number (18) is lost.
- **Scan:** a two-column table of numbered commands (15)–(18) with their
  meanings.
- **Now:** a two-column table, Command / Meaning, with the numbers (15)–(18).
- **Justification:** transcription of the printed table.

### 1984-13 · p. 822 §3, meaning of (16) · TYPO
- **OCR and scan:** "If the contents of $Rj$ is less than the contents of
  $Rm$ …"
- **Now:** "If the contents of $R j$ are less than …"
- **Justification:** grammatical agreement.

### 1984-14 · p. 822 §3, (20)–(21) · OCR + LAYOUT
- **OCR:** one `array` with `L i & \text { IF } R j=0, …` and
  `L i+1 & \text { ELSE } R j \leftarrow R j-1 . \tag{21}`. The number (20) is
  lost.
- **Scan:** two numbered lines, (20) "*Li* IF *Rj* = 0, GO TO *Lk*," and (21)
  "*Li* + 1 ELSE *Rj* ← *Rj* − 1."
- **Now:** (20) and (21) both numbered, with the label written $L(i+1)$.
- **Justification:**
  - OCR: the lost tag.
  - LAYOUT: $L(i+1)$ disambiguates the label of line $i+1$ from "$Li$ plus
    1". The running text keeps the printed "$L i+1$" ("to execute $L i+1$
    after $L i$").

### 1984-15 · pp. 822–823 §3, Example 1 · OCR
- **OCR:** lines L0–L6 in a math `array`; lines L7–L14 in a `verbatim` block
  with Unicode arrows (`L7 R2←R2+1,R4←R4-1,` …).
- **Now:** one array with all fifteen lines, identical in content to the scan:
  - L5 has three parallel updates, $R3\leftarrow R3+1,\ R4\leftarrow R4+1,\
    R2\leftarrow R2-1$;
  - L7 has two, $R2\leftarrow R2+1,\ R4\leftarrow R4-1$;
  - L12 has three, $R1\leftarrow R1-1,\ R2\leftarrow R2-1,\ R3\leftarrow R3-1$.

  Line-final punctuation is dropped (section 2, item 6).
- **Justification:** transcription. No instruction of the program is changed.
  A check parses the fifteen lines from the TeX source and executes them
  (section 6).

### 1984-16 · p. 823 §3, after Example 1 · ORIG
- **OCR and scan:** `Here there are $r=4$ registers and $l=14$ lines in the program.`
- **Now:** "Here there are $r=4$ registers and $l+1=15$ program lines, labelled
  $L0,\ldots,L14$, so $l=14$."
- **Justification:** the lines are labelled $L0,\dots,Ll$, so $l=14$ is the
  largest label and there are fifteen lines. The printed sentence conflates the
  two. The value $l=14$ used in (25), (30) and (33) is unaffected.
- **Classification:** first described as a "counting typo"; classified ORIG
  because it misstates a quantity.

### 1984-17 · p. 823 §3, definition of s · CLAR (unmarked)
- **OCR and scan:** `Let $s$ be the number of steps in the computation (assuming the machine stops).`
- **Now:** "Let $s$ be the number of transitions in the computation before the
  STOP configuration (assuming the machine stops), so the configurations are
  indexed by $t=0,\ldots,s$."
- **Justification:** makes the time convention of (22), (23), (27) and (33)
  explicit. There are $s+1$ recorded configurations. Registers are recorded
  before the instruction at time $t$ is executed. STOP is the terminal
  configuration, not an extra transition. The paper's "$s=18$ steps" for input
  2 (18 transitions, 19 columns) fits this reading.

### 1984-18 · p. 823 §3, (22)–(23) · OCR
- **OCR:** one `array` with only `\tag{23}`.
- **Scan:** (22) and (23) both numbered.
- **Now:** both numbered, with the digit bounds $0\leq r_{j,t}<Q/2$ and
  $0\leq l_{i,t}\leq 1$ retained.

### 1984-19 · p. 823 §3, after (26): the fixed base · ORIG (marked)
- **OCR and scan:** `For example we can put $Q=2^{x+s+l}$ (for singlefoldness).`
- **Now:** $Q=2^{x+s+l+2}$, with the footnote *Editorial note. The extra 2 in
  the exponent ensures (24)–(26) even when $x=s=l=0$, the immediate-STOP case.*
- **Justification:** for the one-line program "L0 STOP" with input 0,
  $x=s=l=0$. The printed choice gives $Q=1$, which violates (24) and (25).
  - This is the only accepting computation for which the printed choice fails.
    If $l\geq1$, then $s\geq1$ and $x+s<2^{x+s+l-1}$, $l+1<2^{x+s+l}$. If $l=0$,
    acceptance forces $s=x=0$. This was checked twice, the second time by
    exhaustive search over small $x,s,l$.
  - $2^{x+s+l+2}$ satisfies (24)–(26) for all $x,s,l\geq0$. It is still
    determined by the input and the length of the computation, which
    singlefoldness requires.
  - The Lean completeness proof uses exactly this base
    (`JM1984.RM.sys_of_accepts`).

### 1984-20 · p. 824 §3, after "(The set of accepted numbers is the set of primes.)" · CLAR (marked by the label *Editorial invariant check*)
- **OCR and scan:** no such paragraph.
- **Now:** a paragraph proving the parenthetical claim for every nonnegative
  input:
  - For $x\geq2$ the trial value $k$ in $R2$ starts at 2. Lines 2–4 clear
    $R3$. Lines 5–8 add $k$ to $R3$ and restore $R2=k$, $R4=0$.
  - At line 9, $R3$ is a positive multiple of $k$. The first multiple
    $\geq x$ either exceeds $x$, in which case line 10 returns to line 1, which
    increases $k$, or equals $x$.
  - A proper divisor $k<x$ traps the machine in the unchanged cycle 10–11.
    $k=x$ leads to lines 12–13, which clear all registers and stop.
  - Every subtraction is from a positive register. Inputs 0 and 1 always
    overshoot and never stop.
- **Justification:** the paper asserts the claim only for the displayed input-2
  trace. The full argument runs as follows.
  - At each visit to line 9, $R1=x$, $R2=k\geq2$, $R4=0$ and $R3=jk$ with
    $j\geq1$.
  - Every decrement is safe. Line 3 runs only after a nonzero test. Lines 5
    and 7 decrement positive remaining counts. Line 12 is entered with
    $R1=R2=R3=x>0$ and repeated only while they are positive.
  - The first divisor reached is a proper divisor for a composite input and $x$
    itself for a prime input.
  - For $x\in\{0,1\}$ every trial overshoots, so the run diverges without
    period (unlike the composite two-line cycle).
- **History:** an earlier revision of the paragraph said "causing line 10 to
  increase $k$"; the wording was corrected (84-R4-08). Line 10 is
  `IF R1 < R3, GO TO L1` and changes no register. It is line 1 that increases
  $k$.

### 1984-21 · p. 824 §3, the computation table · OCR + LAYOUT
- **OCR:** a 21-column `tabular` with the 19 digits of each row, the row name
  and a repeated command column ("REGISTER" for R1–R4, the instruction for
  L0–L14). Ten digit cells are damaged. Two wrapped updates are lost from the
  command column: $R2\leftarrow R2-1$ at L5 and $R3\leftarrow R3-1$ at L12.
- **Scan:** as the OCR's layout, but with correct digits. The wrapped updates
  are printed on continuation lines.
- **Now:** a 19-column table with a header row $t=18,17,\ldots,0$ (time
  increasing to the left, as printed), rows $R_1,\dots,R_4,L_0,\dots,L_{14}$,
  and a note: "Time increases to the left. The line numbers refer to the full
  program in Example 1; in particular, its parallel updates at L5, L7 and L12
  are retained." The command column is omitted in favour of the program
  (LAYOUT).
- **The ten damaged cells (OCR → scan/now), by row and time $t$:**

  | Row | $t$ | OCR | Now |
  |---|---:|---|---:|
  | $R_2$ | 15 | blank | 1 |
  | $R_2$ | 14 | 1 | 2 |
  | $R_2$ | 1 | `10` (two cells merged) | 1 |
  | $R_2$ | 0 | blank | 0 |
  | $L_1$ | 0 | blank | 0 |
  | $L_4$ | 15 | blank | 0 |
  | $L_4$ | 14 | blank | 0 |
  | $L_9$ | 0 | blank | 0 |
  | $L_{10}$ | 0 | blank | 0 |
  | $L_{13}$ | 15 | 0 | 1 |

- **Justification:**
  - All $19\times19=361$ cells were regenerated from an execution of the
    program on input 2 and agree with the scan. This was done three times,
    independently.
  - The execution visits L0, L1, L2, L5, L6, L5, L6, L7, L8, L7, L8, L9, L10,
    L11, L12, L13, L12, L13, L14: 18 transitions, ending with all registers
    zero.
  - The restored 1 in $L_{13}$ at $t=15$ matters, since the conditional L13
    runs at both $t=15$ and $t=17$.

### 1984-22 · pp. 824–825 §3, before (30) · TYPO
- **OCR and scan:** `Since\\ $l<Q$, by (25), we may use for this purpose the conditions`
- **Now:** "Since $l+1<Q$, by (25), …"
- **Justification:** the sentence cites (25), which reads $l+1<Q$, and only
  that bound makes the argument work. The column sums in (30) are
  $\sum_i l_{i,t}\leq l+1$, and they are proper base-$Q$ digits only if
  $l+1<Q$. With $l<Q$ alone a column sum could equal $Q$ and carry. The Lean
  proof of the §3 equivalence uses (25) exactly here.
- **Classification:** first described as a clarifying sharpening (CLAR). The
  scan confirms that "$l<Q$" is printed, so it is classified as TYPO
  (misquotation of (25)); the substance is unchanged.

### 1984-23 · p. 825 §3, before (33) and before (36): self-targeting conditional jumps · ORIG (marked)
- **OCR and scan:**
  - `By means of GO TO commands we may suppose that the STOP command appears
    only once, say at the end of the program. Hence the condition for stopping
    …`
  - Later: `This works for the general case $k \neq i+1$. If $k=i+1$ use
    (34). A similar remark applies to the following conditional transfer
    commands. If $k \neq i+1$, the command (16), $L i$ IF $R j<R m$, GO TO $L
    k$, can be simulated by`
- **Now:**
  - After "say at the end of the program" this is inserted: "Before encoding,
    we also replace any self-targeting conditional jump by a jump to a fresh
    trampoline line whose sole instruction is GO TO the original conditional
    line. The trampoline block is isolated from ordinary fall-through, all
    labels are adjusted, and the unique STOP remains last." It carries the
    footnote *Editorial note. This normalization is necessary for the
    strict-comparison encoding (36) when its original target is the current
    line. A concrete spurious accepting computation for the printed self-target
    case is given in the editorial notes.*
  - The (36) sentence reads "After the normalization just described, and with
    $k\notin\{i,i+1\}$, the command (16) … can be simulated by". Formula (36)
    itself is unchanged.
- **Justification.** For a conditional at line $i$ that tests $R_j<R_m$,
  write $\kappa_t$ for the digit of $L_k$ in block $t$ and $h_t\in\{0,1\}$
  for the carry into block $t$.
  - In $D=L_k+QI+2R_j-2R_m$, block $t$ has raw value
    $Q+2(r_{j,t}-r_{m,t})+\kappa_t+h_t$.
  - When line $i$ runs at time $t$ and $k\neq i$, $\kappa_t=0$. Then the carry
    out of block $t$ is 1 exactly when $r_{j,t}\geq r_{m,t}$, and bit 0 of
    block $t+1$ is $\kappa_{t+1}+h_{t+1}\bmod 2$. So $QL_i\preccurlyeq D$
    forces the jump exactly when $r_{j,t}<r_{m,t}$.
  - When $k=i$, $\kappa_t=1$. At a difference $r_{j,t}-r_{m,t}=-1$ with
    incoming carry 1, the extra unit fakes the "no borrow" carry.

  Counterexample to the printed encoding (rechecked with exact arithmetic):

  ```text
  L0  R2 <- R2+1
  L1  IF R1<R2, GO TO L1
  L2  R2 <- R2-1
  L3  STOP
  ```

  - On input $x=0$, the machine reaches L1 with $(R1,R2)=(0,1)$ and loops
    forever. It does not accept.
  - Yet the false path L0, L1, L2, L3 satisfies every printed condition with
    $s=3$, $l=3$, $Q=8$, $I=585$, $L_0=1$, $L_1=8$, $L_2=64$, $L_3=512$,
    $R_1=0$, $R_2=72$:
    - $x+s=3<4$ and $l+1=4<8$;
    - (29)–(33) hold;
    - the fall-through conditions $QL_0\preccurlyeq L_1$ and
      $QL_2\preccurlyeq L_3$ hold;
    - (39) for $R2$: $72=8\cdot72+8\cdot1-8\cdot64$;
    - (36): $QL_1=64$ is masked by $L_1+L_2=72$ and by
      $L_1+QI+2R_1-2R_2=8+4680-144=4544$.
  - The same construction works with the edition's base $Q=256$.

  Why the trampoline repairs this:
  - Replacing the self-jump by a jump to a fresh line whose only instruction is
    "GO TO $L_i$" makes $k\neq i$.
  - Isolating the trampoline from fall-through, for example by an
    unconditional jump over it, keeps the machine's behaviour.
  - It is deterministic, so a terminating computation stays unique.
  - It increases the number of executed steps by at most a constant factor.
  - (35) and (37) do not contain $L_k$ in the second condition, so they need
    only $k\neq i+1$ (1984-24).

  The normalization is proved in Lean (`JM1984.RM.normalize`,
  `accepts_normalize_iff` in `Lean/Diophantine/Paper1984/Normalize.lean`).
- **Confirmation:** an independent borrow analysis and the Lean lemma
  `JM1984.compare_cond` confirm that $\kappa_t=0$ at the deciding block is
  exactly the hypothesis used.

### 1984-24 · p. 825 §3, before (37) · CLAR (unmarked)
- **OCR and scan:** `The command (19), $L i$ IF $R j \leq R m$, GO TO $L k$, can be simulated by`
- **Now:** "The command (19), $L i$ IF $R j\leq R m$, GO TO $L k$, with $k\neq
  i+1$, can be simulated by"
- **Justification:** this spells out, for (37), the paper's own "A similar
  remark applies to the following conditional transfer commands" (the case
  $k=i+1$ is encoded by (34)). No self-target exclusion is needed for (37),
  because its second condition contains $L_{i+1}$, not $L_k$ (1984-23). The
  two qualifications were checked to be consistent.

### 1984-25 · p. 825 §3, after the fall-through sentence · CLAR (unmarked)
- **OCR:** none.
- **Now:** "When a comparison uses the constant $0$ or $1$ in place of a
  register, its encoded history is respectively $0$ or $I$."
- **Justification:** the paper permits the constants 0 and 1 in (16), (19),
  (20) and uses them in Example 1 (lines 6, 8, 13). In (35)–(37) the history
  of the constant 1 is $I=\sum_t Q^t$, not the integer 1, which would describe
  only the first column. Lean encodes the operands this way (`JM1984.RM.Sys`).
  - A boundary case: for the constant 1 the carries stay $\leq1$ only
    if $Q\geq8$. (24) supplies this whenever $s\geq2$.

### 1984-26 · p. 825 §3 · TYPO
- **OCR and scan:** `an equation in $R_{j}$ which ensure that,`
- **Now:** "… which ensures that, …"

### 1984-27 · p. 826 §3, before (40) · CLAR (unmarked)
- **OCR:** `with input $x$ in $R_{1}$ and output $y$ in $R_{1}$, the register equation for $R_{1}$ would become`
- **Scan:** as the OCR (*R*₁ with subscripts).
- **Now:** "with input $x$ in $R1$, output $y$ in $R1$, and the remaining
  registers cleared at termination, the register equation for $R_{1}$ would
  become"
- **Justification:**
  - Input and output live in the machine register $R1$, not in the history
    number $R_1$.
  - (40) changes only the equation of $R_1$. The other registers keep (39),
    whose form $R_j=QR_j+\cdots$ presupposes a final content of zero. So the
    convention that they are cleared at termination must be stated.

### 1984-28 · p. 826 §4, length of x · OCR
- **OCR:** `$\left.|x|={ }^{\Gamma} \log _{2}(x+1)\right\urcorner$`
- **Scan:** $|x| = ⌜\log_2(x+1)⌝$.
- **Now:** $|x|=\lceil\log_2(x+1)\rceil$.

### 1984-29 · p. 826 §4, (41)–(42) · OCR
- **OCR:** one array with `L n & R i \leftarrow R i+R j,` (no tag) and
  `L p & R j \leftarrow\ulcorner R j / 2\urcorner . \tag{42}`.
- **Now:** (41) $Ln\quad Ri\leftarrow Ri+Rj$ and (42)
  $Lp\quad Rj\leftarrow\lceil Rj/2\rceil$, both numbered.
- **Justification:**
  - The number (41) was lost.
  - The corner brackets are the scan's ceiling.
  - The ceiling is essential. The paper's own gloss "$Lp\ Rj\leftarrow
    Rj-\lfloor Rj/2\rfloor$" before (49) and the parity trick (43) both need
    it (section 5).

### 1984-30 · p. 826 §4, clearing a register · ORIG (marked)
- **OCR and scan:** `For example, $R i \leftarrow 0$ is obtained by iterating (42).`
- **Now:** "For example, to obtain $R i\leftarrow0$, iterate (42) while
  $R i>1$, and then subtract $1$ if $R i=1$." The footnote reads *Editorial
  note. Iterating ceiling-halving alone does not clear a positive register:
  $\lceil1/2\rceil=1$. The final conditional decrement repairs the original
  macro.*
- **Justification:**
  - Under (42) every positive value converges to the fixed point 1, never 0.
  - The repaired macro leaves 0 unchanged and terminates in $O(|Ri|+1)$ steps.
  - Replacing the ceiling by a floor instead would break (43) and the
    reading of (49)–(50).
  - Lean: `JM1984.RM.zero_macro`, with the conditional decrement and a
    logarithmic step bound.
  - The scan confirms the printed wording.

### 1984-31 · p. 826 §4, (43) · OCR
- **OCR:** `\left.R i \equiv 0(\bmod 2) \Leftrightarrow 2^{\ulcorner } R i / 2\right\urcorner \leq R i`
  (the factor 2 misread as a base of an exponential).
- **Scan:** $Ri\equiv0\ (\mathrm{mod}\ 2)\Leftrightarrow 2⌜Ri/2⌝\leq Ri$.
- **Now:** $Ri\equiv0\pmod2\ \Longleftrightarrow\ 2\lceil Ri/2\rceil\leq Ri$.
- **Justification:** $2\lceil n/2\rceil$ equals $n$ for even $n$ and $n+1$ for
  odd $n$. Verified for $0\leq n\leq4095$ and in Lean
  (`JM1984.even_iff_two_mul_ceil`).

### 1984-32 · p. 826 §4, after (44): the quotient macro · OCR
- **OCR:** `the macros quotient, $R i \leftarrow{ }^{R i / 2}$,`
- **Scan:** "*quotient*, *Ri* ← ⌞*Ri*/2⌟".
- **Now:** "the macros quotient, $Ri\leftarrow\lfloor Ri/2\rfloor$,"

### 1984-33 · p. 826 §4, after (44): the parity macro · LAYOUT
- **OCR:** `$R i \leftarrow R E M(R i, 2)$`
- **Scan:** "*Ri* ← REM(*Ri*, 2)" in capitals.
- **Now:** $Ri\leftarrow\operatorname{rem}(Ri,2)$.
- **Justification:** harmonized with the $\operatorname{rem}$ of §2, with no
  change of meaning.

### 1984-34 · p. 826 §4, (45), line L3 · OCR
- **OCR:** `L 3 & \left.R k \leftarrow R_{k} / 2\right\rfloor,` (the left floor
  lost, and a spurious history symbol $R_k$).
- **Scan:** "*L*3 *Rk* ← ⌞*Rk*/2⌟,".
- **Now:** $L3\quad Rk\leftarrow\lfloor Rk/2\rfloor$.

### 1984-35 · p. 826 §4, after (45) · CLAR (unmarked)
- **OCR:** none.
- **Now:** "The multiplication macro uses $R j$ and $R k$ destructively; copy
  them to scratch registers first when their original values must be
  preserved."
- **Justification:**
  - The loop computes $Ri=Rj\cdot Rk$ correctly, but it halves $Rk$ to 0 and
    doubles $Rj$.
  - The loop invariant is: accumulator plus current multiplicand times
    current multiplier equals the original product.
  - Checked on 10,201 input pairs and in Lean
    (`JM1984.RM.mul_macro`).

### 1984-36 · p. 826 §4, after (46): a polynomial-size base · CLAR (marked)
- **OCR:** none.
- **Now:** "For polynomial-size encodings, one may take $Q=2^{s+|x|+l+3}$; this
  satisfies (25), (26), and (46), and has bit length $O(s+|x|+l)$." The
  footnote reads *Editorial note. A polynomial-bit-size choice is made explicit
  here; the value-based choice after (26) is not suitable for this complexity
  estimate.*
- **Justification:**
  - Since $x+1\leq2^{|x|}$, we have $2^s(x+1)\leq2^{s+|x|}<2^{s+|x|+l+2}=Q/2$,
    and $l+1<Q$.
  - The value-based $Q=2^{x+s+l+2}$ has bit length linear in $x$, which is
    exponential in $|x|$, so it cannot serve in §5's estimate.
  - This explains a choice the paper leaves open. It does not replace the
    paper's appeal to Adleman and Manders.

### 1984-37 · p. 826 §4, fall-through for (41) and (42) · ORIG (unmarked)
- **OCR:** none.
- **Now:** "For each command (41) or (42), also impose the fall-through
  condition $Q L_n\preccurlyeq L_{n+1}$ or $Q L_p\preccurlyeq L_{p+1}$,
  respectively."
- **Justification:** the paper requires $QL_i\preccurlyeq L_{i+1}$ for (17),
  (18) and (21) but not for the new commands. Register equations alone do not
  determine the next line, so without this condition the §4 system admits
  histories that jump arbitrarily after a fast command. The Lean §4 system
  includes "a fall-through condition for every fast line" (`JM1984.RM.XSys`,
  `xaccepts_iff`).

### 1984-38 · p. 827 §4, (49) · ORIG (marked)
- **OCR and scan:** $2J_{j,p}\preccurlyeq R_j,\quad J_{j,p}\preccurlyeq(Q/2-1)L_p,\quad R_j\preccurlyeq(Q-1)(I-L_p)+2J_{j,p}+I$.
- **Now:** the third condition is $R_j\preccurlyeq(Q-1)(I-L_p)+2J_{j,p}+L_p$,
  followed by the sentence "The final term in (49) is $L_p$, not $I$." and the
  footnote *Editorial note. The printed $+I$ produces carries in unselected
  blocks and can reject a valid computation. The replacement $+L_p$ restores
  the required blockwise mask; see the proof and counterexample in the
  editorial notes.*
- **Justification (proof):** write $R=\sum r_tQ^t$ with $0\leq r_t<Q/2$,
  $L=L_p=\sum\lambda_tQ^t$ with $\lambda_t\in\{0,1\}$, and $J=\sum j_tQ^t$.
  - The second condition forces $j_t=0$ where $\lambda_t=0$, and $j_t<Q/2$
    elsewhere.
  - Since $Q$ is a power of 2, doubling a block does not carry.
  - The corrected right side has digit $Q-1$ where $\lambda_t=0$ and digit
    $2j_t+1$ where $\lambda_t=1$.
  - In a selected block, $2j_t\preccurlyeq r_t\preccurlyeq 2j_t+1$. This
    forces $j_t=\lfloor r_t/2\rfloor$, which is exactly (50) and makes $J$
    unique.
  - The register update is then $r_t-\lfloor r_t/2\rfloor=\lceil r_t/2\rceil$,
    that is, (42).
  - With the printed $+I$, the added 1 in every unselected block turns the
    all-ones digit $Q-1$ into a carry and destroys the mask.

  Counterexamples to the printed form (rechecked):
  - *First counterexample.* The program "L0 $R1\leftarrow\lceil R1/2\rceil$; L1
    $R1\leftarrow R1-1$; L2 STOP" on input $x=2$ has register history 2, 1, 0.
    Take $s=2$, $l=2$, $Q=32$. Then $I=1057$, $R=34$, $L=1$, $J=1$.
    - (46) holds: $12<16$.
    - The register equation holds: $34=32\cdot34-32\cdot1-32\cdot32+2$.
    - The first two conditions hold.
    - The printed right side is $33795=2^{15}+2^{10}+2+1$, which lacks the bit
      32 of $R$. The corrected right side $32739$ contains all bits of 34.

    So the printed (49) rejects a genuine accepting computation.
  - *Second counterexample.* The history $r=(3,5,2,7)$ with the halving line executed only
    at $t=0$ and $Q=16$ fails the printed form and satisfies the corrected one.

  Lean: `JM1984.mask49_iff` proves (49) ⟺ (50) with the term $L_p$.

### 1984-39 · p. 827 §5, (52) · ORIG (marked)
- **OCR and scan:** `To simulate, with exponential diophantine equations, the nondeterministic command (51) we need only write` (52) $QL_n\preccurlyeq L_i+L_j$.
- **Now:** "… the nondeterministic command (51) when $i\neq j$, we need only
  write" (52). This is followed by "When $i=j$, use the deterministic
  condition $Q L_n\preccurlyeq L_i$ instead: adding a mask to itself shifts its
  bits, rather than duplicating the available target." The footnote reads
  *Editorial note. The distinct-target qualification, absent from the source,
  is needed in (52).*
- **Justification:**
  - For $i\neq j$ the digits of $L_i$ and $L_j$ are disjoint by (30)–(31), so
    $L_i+L_j$ is the union of the allowed successors.
  - For $i=j$, $2L_i$ shifts every bit, and (52) would demand a 1 in a
    position no $L$ has.
  - Lean: `JM1984.branch_iff` and `JM1984.RM.naccepts_iff` (branch lines with
    distinct targets; $QL_n\preccurlyeq L_i$ when $i=j$).

### 1984-40 · p. 827 §5, (54) · OCR
- **OCR:** `\left(\exists\left|x_{0}\right|, \ldots,\left|x_{n}\right| \leq P(|x|)\left[F\left(…\right)=G\left(…\right)\right],\right.`
  (the closing parenthesis of the bounded quantifier is misplaced at the end).
- **Scan:** $(\exists|x_0|,\ldots,|x_n|\leq P(|x|))[F(x,x_0,\ldots,x_n)=G(x,x_0,\ldots,x_n)]$.
- **Now:** as the scan.

### 1984-41 · p. 827 §5, after (54) · CLAR (unmarked)
- **OCR and scan:** `…functions built up from $x, x_{0}, \ldots, x_{n}$ by the operations of addition, multiplication, and the logical "and" operation, \&.`
- **Now:** "… built up from $x,x_0,\ldots,x_n$ and nonnegative integer
  constants by the operations …"
- **Justification:** moving the negative coefficients of the integer
  polynomial $Q$ in (53) to the other side needs constants. This is the same
  convention as in (1) ("natural number constants").

### 1984-42 · pp. 828–829, structure of the reference list · BIB
- **OCR:** part of the list in an `itemize` environment. Repeated authors are
  given as `\item \hspace{0pt}`, `-`, `--` or `$\_\_\_\_$`.
- **Scan:** a plain list. Repeated authors are replaced by a 3-em dash.
- **Now:** every entry is a separate hanging-indent paragraph with the author
  written out: Adleman and Manders [1976]; Davis [1958], [1973], [1974]; Jones
  [1978], [1982]; Lucas [1878b]; Matijasevič [1971a]–[1979]; Minsky [1967];
  J. Robinson [1969]. All 38 entries are kept, in the printed order.

### 1984-43 · p. 828, Börger [1975] · OCR
- **OCR:** `F ISILC Logic Conference`
- **Scan:** "⊨ ISILC Logic Conference" (the logical symbol, as in the
  conference's name).
- **Now:** $\models$ ISILC Logic Conference.

### 1984-44 · p. 828, Davis [1953], Jones [1978], Jones [1982] · BIB
- **OCR and scan:** "this JOURNAL".
- **Now:** *The Journal of Symbolic Logic*.
- **Justification:** the edition is read outside the journal.

### 1984-45 · p. 828, Jones [1982] · TYPO
- **OCR and scan:** `[1982]. Universal diophantine equation`
- **Now:** "[1982], Universal diophantine equation".
- **Justification:** every other entry has a comma after the year. The full
  stop is confirmed in the scan.

### 1984-46 · p. 828, Matijasevič [1970] · OCR
- **OCR:** `Y. V. Matiuasevič [1970]`
- **Scan:** "Y. V. MATIJASEVIČ" in small capitals. The "IJ" was misread.
- **Now:** "Y. V. Matijasevič".
- **Classification:** first treated as a spelling correction of the original;
  the scan prints the correct spelling, so it is classified OCR.

### 1984-47 · p. 829, Matijasevič [1971a] · OCR
- **OCR:** `Mathematics of the USSR- Izvestija`
- **Scan:** "Mathematics of the USSR—Izvestija" (em dash at a line end).
- **Now:** "Mathematics of the USSR---Izvestija" (em dash).

### 1984-48 · p. 829, Melzak [1961] · BIB
- **OCR and scan:** `Canadian Mathematical Bulletin, vol. 4 (1961), pp. 279-294.`
- **Now:** "pp. 279–293".
- **Justification:** the publisher's record of the article, DOI
  [10.4153/CMB-1961-031-9](https://doi.org/10.4153/CMB-1961-031-9), gives
  279–293. The next article in that volume, Lambek's, starts at p. 295.
- **Check:** a diff of all numbers of the edition against the scan found this
  as the only numerical difference, apart from metadata.

### 1984-49 · p. 829, J. Robinson [1969] · TYPO
- **OCR and scan:** `Englewood Cloiffs`
- **Now:** "Englewood Cliffs".
- **Justification:** misspelling in the printed original (checked in the
  scan). The same publisher's place is spelled correctly in Minsky [1967].

## 4. Editorial additions

Every addition that the reconstruction makes to the article is an entry of
section 3. This index gives the marking status of each.

| ID | Addition | Marked in the text? |
|---|---|---|
| 1984-03 | Cyrillic for the printed transliterations *odnokratnoe*, *oonarnoe* | footnote |
| 1984-05 | positive modulus, $x^0=1$, $\binom nk=0$ for $k>n$ | footnote |
| 1984-06 | singlefold divisibility at zero | footnote |
| 1984-07 | congruence for $c>0$ | no |
| 1984-08 | the cases $y=0,1$ of (9) | no |
| 1984-10 | guard $a>0$ in (12) | no |
| 1984-16 | "$l+1=15$ program lines … so $l=14$" | no |
| 1984-17 | $s$ counts transitions; configurations $t=0,\dots,s$ | no |
| 1984-19 | $Q=2^{x+s+l+2}$ | footnote |
| 1984-20 | all-input proof that Example 1 accepts exactly the primes | italic label *Editorial invariant check* |
| 1984-21 | time header and note under the table | table note |
| 1984-23 | trampoline normalization; $k\notin\{i,i+1\}$ for (36) | footnote |
| 1984-24 | "with $k\neq i+1$" for (37) | no |
| 1984-25 | histories of the constants 0 and 1 | no |
| 1984-27 | remaining registers cleared at termination in (40) | no |
| 1984-30 | clearing macro with final conditional decrement | footnote |
| 1984-35 | multiplication macro is destructive | no |
| 1984-36 | $Q=2^{s+\lvert x\rvert+l+3}$ for polynomial size | footnote |
| 1984-37 | fall-through conditions for (41), (42) | no |
| 1984-38 | $+L_p$ in (49) and the sentence stating it | footnote |
| 1984-39 | distinct targets in (52); the case $i=j$ | footnote |
| 1984-41 | constants in (54) | no |

## 5. Readings examined and retained

These are places where a change was considered and the original kept, or
where a change was made and later reverted.

- **"say at the end of the program" (p. 825).** An earlier revision of this
  edition silently dropped "say". It was restored (84-R4-05), so the
  STOP-last convention is a choice, as the authors phrased it. There is no
  net discrepancy.
- **(11) is correct as printed.** $a\mathbin{\&}b=c\leftrightarrow
  c\preccurlyeq b$ and $b\preccurlyeq a+b-c$ needs no $c\preccurlyeq a$.
  - If $a\mathbin\&b=c$, write $a=c+e$ with $e$ disjoint from $b$. Then
    $a+b-c=b+e$.
  - Conversely, look at the least bit at which $a\mathbin\&b$ and $c$ could
    differ. There, $a+(b-c)$ has a 0 where $b$ has a 1.
  - Tested twice, independently, on all $64^3$ triples. Proved in Lean
    (`JM1984.land_eq_iff_mask`).
- **(9) is correct as printed for $y>1$, including $x=0,1$.**
  - For $x=0$ the modulus is 1 and both sides are 0.
  - For $x=1$ the modulus $2^y-1>1$.
  - For $x\geq2$, $2^{xy}\geq(2x)^y\geq4x^y>x^y+x$, so $x^y$ is the least
    residue.
  - Lean: `JM1984.rem_two_pow_eq_pow`. Only the cases $y=0,1$ were added
    (1984-08).
- **(47) is correct as printed.** At an unselected block the second condition
  forces 0 and the third is vacuous. At a selected block the first and third
  force equality with $R_j$, giving (48) uniquely. Lean: `JM1984.mask47_iff`.
  It was the analogy with (47) that exposed the $+I$ of (49).
- **(42) stays a ceiling and (50) a floor.** It was considered whether to
  make the command a floor; the ceiling stands because the parity trick (43)
  and the reading of (49)–(50) need it (1984-30, 1984-38).
- **(35)–(37) are correct for distinct targets.** The carry analysis was
  redone independently. The carry out of the deciding block is exactly $[r_j=0]$,
  $[r_j\geq r_m]$ or $[r_m\geq r_j]$ as long as carries are $\leq1$, which holds
  for $t<s$ since $r_{j,t}\leq x+t$. Only the self-target case of (36) needed a
  change (1984-23).
- **The divisibility claim is correct.** The footnote of 1984-06 clarifies it;
  it does not refute it.
- **Example 1 and "$s=18$ steps".** The program, the stated 18 transitions for
  input 2 and the claim that the accepted set is the primes are all correct.
  No instruction is changed.
- **Scan confirmations.** The scan prints "$l<Q$, by (25)"
  (1984-22), (12) without $a>0$ (1984-10), "$Ri\leftarrow0$ is obtained by
  iterating (42)" (1984-30), and "oonarnoe" (1984-03). So these are not OCR
  defects.
- **Barzdin'.** The text's "J. M. Barzdin' [1963]" (p. 823) differs from the
  bibliography's "Ja. M. Barzdin'", and the scan has the same. Both are left
  as printed.
- **Uncited references.** Jones [1982] and Matijasevič [1977] are not cited in
  the text of the original either. They are kept.
- **Matijasevič [1972], English pages 124–164.** Kept. Matiyasevich's
  publication list (Academia Europaea, item 85) gives *Russian Math. Surveys*
  27 (5), 124–164; DOI
  [10.1070/RM1972v027n05ABEH001386](https://doi.org/10.1070/RM1972v027n05ABEH001386).
- **Matijasevič [1970], English pages 354–357.** Kept. The corpus-wide
  354–357 / 354–358 question is resolved in favour of 354–357,
  from the *Journal of Symbolic Logic* Reviews record of the translation
  (errata in vol. 11 no. 6, p. vi). This article already prints 357.
- **Other bibliographic data.** The historical affiliations and the original
  "to appear" for the English translation of Matijasevič [1979] are kept. All
  other entries were checked without further change.
- **Zero-register convention.** The paper assumes that subtraction from a zero
  register never occurs. In the Lean formalization such a run has no
  successor, and (38)/(39) have no solution for it, so the convention costs
  nothing. No text change was made.
- **Spelling.** All prose words of the edition were checked against a
  dictionary; there is no misspelling beyond the items above.

## 6. Verification summary

*Programs.* The verification program is
`Papers/verification/jones1984_verification.py` (it writes
`jones1984_example1_trace.csv`), and the check that parses Example 1 from the
source is part of `Papers/verification/corpus_review.py`. Both were re-run on
24 September 2026 and pass.

- **Exact-arithmetic suite.** An exact-arithmetic suite, standard library
  only, which is not kept in the repository, checked:
  - (8) on 294 cases and (9) on 399 cases;
  - (11) on all $64^3$ triples; (12) for $a\leq4095$; (13) and the Lucas
    lemma for $p=2,3,5,7$;
  - both base choices, including zero inputs;
  - (35)–(37) on 49,920 three-column cases each (distinct labels);
  - (47) and the corrected (49) as unique witnesses; the printed (49) rejected
    the intended witness in 446 tested cases;
  - the counterexamples of 1984-23 and 1984-38;
  - the clearing macro and (43) for inputs 0–4095, and (45) on 10,201 pairs;
  - (24)–(39) exactly for the input-2 computation, and Example 1 on inputs
    2–40.
- **Lucas/Kummer and divisibility.** A further check covered the binary
  Lucas/Kummer link ($\binom sr$ odd ⟺ $r\mathbin\&s=r$ ⟺ no carry in
  $r+(s-r)$) on all 32,896 pairs $r\leq s\leq255$, and the divisibility definition of 1984-06 on 4,225 pairs.
- **Example 1 from the source.** The fifteen program lines were parsed from
  the edition's TeX source and run for all inputs 2–128, checking the
  invariant at every visit to line 9. Inputs 0 and 1 were run for 20,000
  transitions each (73 trial values) and are explicitly not claimed as divergence proofs.
- **`Papers/verification/round4_1984_checks.py`** and its
  `round4_1984_results.json` check:
  - the 19-column table, column by column;
  - inputs 2–60 accepted exactly when prime, with no subtraction from zero;
  - the whole encoding (24)–(39) as exact integer $\preccurlyeq$-relations
    with $Q=2^{x+s+l+2}$ for inputs 2, 3, 5, 7, 11, 13 (18, 57, 192, 405, 1042,
    1495 steps);
  - the §2 identities; (47) and (49) with $+L_p$;
  - the $+I$ counterexample of 1984-38.

  A second independent reading added inputs 0–59, with 200,000 steps for
  inputs 0 and 1, and the check that $Q=2^{s+|x|+l+3}$ satisfies (25), (26)
  and (46). A diff of all numbers against the scan found only the Melzak page
  range (1984-48).
- **Lean 4 / Mathlib** (`Lean/Diophantine/Paper1984/`, status in
  `Lean/STATUS.md`) proves:
  - (10)–(13), the Lucas lemma, (8), (9), and (12) with $a>0$;
  - the §3 equivalence "accepts ⟺ (24)–(39) solvable" (`JM1984.RM.accepts_iff`)
    with the constants 0/1 as operands and parallel updates, using
    $Q=2^{x+s+l+2}$;
  - the trampoline normalization (`Normalize.lean`);
  - the translation to a singlefold unary exponential Diophantine equation
    (`ExpSys.lean`, `DPR.lean`, `re_sfu`);
  - the §4 macros and system with the fall-through conditions and (49) with
    $+L_p$ (`FastMasks.lean`, `FastSystem.lean`, `FastSoundness.lean`);
  - §5's (52) with distinct targets (`NDet.lean`).

  The formalization made explicit three points the printed proof leaves
  implicit. First, the carries in (35)–(37) are 0 or 1, which uses
  $r_{j,t}\leq x+t$ and, for the constant 1, $Q\geq8$. Second, the
  zero-register convention (section 5). Third, the use of (25) for (30)
  (1984-22). Not formalized: the polynomial-time equivalences and the NP
  characterizations (53)–(54), which rest on Adleman–Manders and Minsky.

## 7. Completeness of this register

The OCR and the reconstruction were compared directly at token level, after
stripping LaTeX layout commands, equation tags and the `\origpage` marks. The
comparison was cross-checked against an earlier full OCR-to-edition diff and
against the recorded revisions of the edition. Every token-level difference falls into
a class of section 2 or an entry of section 3.

The scan was inspected for every entry whose classification depends on it:
1984-01, -03, -04, -05, -09, -10, -11, -13, -14, -16, -19, -21, -22, -26, -28,
-31, -32, -33, -34, -40, -43, -45, -46, -47 and -49.

Differences found only by this direct comparison, and classified here:
- 1984-14: the label $L(i+1)$, LAYOUT;
- 1984-24: "with $k\neq i+1$" in (37), CLAR;
- 1984-33: REM → rem, LAYOUT;
- the rewording of the §2 notation sentence inside 1984-05, LAYOUT;
- the Example 1 line-final punctuation (section 2, item 6), LAYOUT;
- the parentheses in (5) (section 2, item 4), LAYOUT;
- the unreproduced italics of the scan (section 2, item 2), LAYOUT.

Classifications corrected after inspection of the scan or the quantity
concerned (see the entries):
- 1984-04 (OCR cause on p. 820);
- 1984-22 (TYPO rather than CLAR);
- 1984-46 (OCR rather than a spelling correction);
- 1984-16 (ORIG).
