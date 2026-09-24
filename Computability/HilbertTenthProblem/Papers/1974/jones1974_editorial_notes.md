# Recursive Undecidability—An Exposition: consolidated editorial notes

**James P. Jones**, *Recursive Undecidability—An Exposition*,
*The American Mathematical Monthly* **81** (1974), no. 7 (August–September), pp. 724–738.

## 1. Scope and the three objects

This document compares three objects:

- **The scan.** `original/1974/jones1974.pdf` has 15 pages, printed pages 724–738.
- **The naive OCR.** `original/1974/jones1974.tex` is a Mathpix transcription of
  the scan. Six figures are not transcribed; they appear only as images under
  `original/1974/images/*.jpg`. These are the transition cards of Examples 1
  and 2, the extra card of §5 and the three cards of $M^{(2)}$.
- **The reconstruction.** `Papers/1974/jones1974_corrected.tex` and its PDF
  give the reconstructed intended mathematical content, with editorial
  qualifications.

This document is the complete editorial record for this article: every
discrepancy between the OCR and the reconstruction, with its classification
and justification, together with the supporting arguments, the readings
examined and retained, and the checks performed. The dated log
`Papers/EDITORIAL_NOTES.md` records individual revisions and checks; its row
IDs (74-R4-01 … 74-R4-11) are cited below where a row concerns an entry.

Each discrepancy is given in its final state. Page numbers always refer to the
**original printed pages**, not to the pages of the new PDF.

The document also records the result of a direct, whitespace- and
macro-normalized token comparison of the OCR against the current
reconstruction (278 raw difference blocks). Every block is covered either by
a register entry (§4) or by a systematic class (§3). Where a difference was
first identified by this comparison, while this consolidated document was
compiled, the scan was inspected and the difference classified; each such case
is marked **[classified during consolidation]**.

## 2. Classifications

| Code | Meaning |
|---|---|
| **OCR** | Transcription defect: the scan is right, the OCR is wrong. |
| **ORIG** | An error in the printed original (mathematical, historical or an overstatement), corrected. |
| **CLAR** | Editorial clarification, qualification, stated hypothesis or proof completion. It is added to the text and covered by the edition notice. Where marked, it is also flagged in place as editorial. |
| **TYPO** | A typographical, punctuation, numbering or cross-reference slip in the original. |
| **BIB** | Bibliographic: a wrong or misprinted datum in a reference. |
| **EDN** | Edition apparatus: notices, pagination marks, metadata. |
| **LAYOUT** | Reflow or typesetting with no change of content. |

## 3. Systematic differences (described once)

These classes are not repeated item by item in §4.

**Front matter and edition apparatus (EDN).**

- New preamble with the macros `\SH`, `\SC` (upright roman function names; the
  scan sets *SH*, *SC* in italic) and `\card`. PDF metadata and running heads
  "J. P. Jones / Recursive Undecidability" are set.
- The title is given in title case. The scan prints capitals with an em dash;
  the OCR has "RECURSIVE UNDECIDABILITY - AN EXPOSITION".
- A date line reads "Originally published in *The American Mathematical
  Monthly* 81 (September 1974), 724–738. Corrected transcription". The
  journal's running head reads "[September".
- The author's unmarked purpose footnote on p. 724 is set as the `abstract`
  with the text unchanged. The OCR emits it as a `\footnotetext` placed after
  the Gauss paragraph.
- The final address block is labelled "*Original affiliation:*" [classified
  during consolidation]. The journal's running heads and folios are not
  transcribed.

**Edition notice (EDN).** A boxed notice says the following:

- the text is a corrected transcription, not a facsimile;
- the historical narrative and Table 1 refer to 1974;
- added explanations are not verbatim wording;
- the 42 references are preserved;
- the bracketed margin numbers are original page starts.

The notice describes a continuously revised edition. It names this document
as the place where every discrepancy between the printed article and the
edition is explained with its justification, and states that a dated log of
revisions and checks is `Papers/EDITORIAL_NOTES.md`. The source header
comments read "% Continuously revised edition; last source revision 24
September 2026." and "% A dated log of revisions and checks is
../EDITORIAL_NOTES.md." Since 24 September 2026 the notice and the header
comments point to this document.

**Original pagination (EDN).** `\origpage{n}` puts a bold `[n]` in the margin
on the line where printed page *n* begins.

- There are 15 marks, for pages 724–738, placed to line accuracy.
- The page starts at 731 (at "Definition"), 733 (at "greatest element"), 736
  and 738 (at reference [19]) were placed by hand.
- Page 736 begins in the scan with "known values of these functions…". That
  sentence is reworded (entry 1974-55), and the mark sits on the corresponding
  words.

**Sections and run-in headings (LAYOUT).**

- The numbered run-in headings "1. Introduction." … "8. Generalizations of the
  Busy Beaver problem." become `\section`s, numbered automatically. Heading case
  is normalized: "Church's Thesis" becomes "Church's thesis", and "The Turing
  Machine Game." becomes "The Turing machine game." [classified during
  consolidation].
- The OCR wraps §1 in an `enumerate`.
- The missing number of §6 is a separate entry (1974-44).
- "Definition.", "Theorem 1.", "Corollary 1.", "Theorem 2.", "The Turing
  machine game." and "Acknowledgment." are `\paragraph` headings. The scan uses
  small capitals or bold for these.
- "Proof:" becomes *Proof.*
- The labels (i), (ii) and (1)–(4) are kept as `\tag`s.

**Emphasis (LAYOUT) [classified during consolidation].**

- The scan sets defined terms and key phrases in italics or bold ("decision
  procedure", "word problem for groups", "positive", "Turing computable", the
  theorem statements, the game rules, and so on).
- The OCR drops all of this emphasis, and the reconstruction does not restore
  it.
- No mathematical content depends on it.

**Reflow (LAYOUT).**

- The OCR's forced breaks `\\` and `\\[0pt]` are removed. At page ends they
  split sentences, for example "permitting\\ us", "State 0\\ is", "toward\\[0pt]
  its" and "historical\\[0pt] events".
- One paragraph break falsely introduced by the OCR is a register entry
  (1974-17).
- Two genuine paragraph breaks lost in the reconstruction are register entries
  (1974-07, 1974-38).

**Mathematical typesetting (LAYOUT).**

- `$$…$$` becomes `\[…\]`.
- `\leqq` (the scan's ≦) becomes `\leq`.
- `\cdots n` becomes `\ldots,n` in state lists and in the transition-map
  display. The scan has "0, 1, 2, ··· n". The Diophantine-definition paragraph
  keeps `\cdots`.
- The inline pair "(1) … and (2) …" and the display "(3) … and (4) …" become
  `align` displays; "Plainly" gains a comma before the display [classified
  during consolidation].
- Spaces that the OCR puts inside math are removed:
  - `$i$ th` becomes `$i$th`, in both occurrences of the sentence on p. 729
    (74-R4-03).
  - `" $v$ is the $2 u$ th Fibonacci number"` becomes `"$v$ is the $2u$th …"`
    (part of 74-R4-02).
  - `$(4 n+4)^{2 n} n$-state` becomes `$(4n+4)^{2n}$ $n$-state` (twice, §6 and
    §7). The trailing *n* inside the math group set no space before "-state"
    (74-R4-05).
- Digit grouping uses `{,}`: $25{,}600{,}000{,}000$ (74-R4-04) and the Table 1
  entries. In math mode a plain comma set "25, 600, 000, 000".
- A `%` stops a line break from setting a space before the Risch footnote mark
  (74-R4-06, build).

**Quotation marks and dashes (LAYOUT).**

- The scan uses typographic quotes throughout. The OCR's straight `"…"` (about
  20 pairs) become ``` ``…'' ``` (74-R4-02).
- En dashes are used for number ranges (1912–14, 74-R4-07; 1954–56; 1963–64;
  all page ranges) and in "win–lose", "Gödel–Rosser" and "Zermelo–Fraenkel".
- "so called" is a register entry (1974-39).

**Names.**

- Radó's accent is restored throughout, in the text and in references [19] and
  [32]. The scan prints "Rado".
- Initials are spaced: "P.S. Novikov" becomes "P. S. Novikov", as printed in
  [27].

**Figures and cards (OCR/LAYOUT).** The OCR renders all six card figures as
images only.

- The reconstruction resets them as native tables through `\card` for Example 1
  (2 cards), Example 2 (5 cards), card $n+1$ in §5 and $M^{(2)}$ (3 cards).
- Every transition was compared with the scan, and all agree. The blank rows of
  $M^{(2)}$ are an entry (1974-41).
- Presentation changes [classified during consolidation]:
  - the card title "Card *i*" is printed as "State *i*";
  - each card gets a column header "read / write / move / next";
  - the scan's comma triples "1,R,2" become three columns.
- The captions are set as bold lines with normalized case. Two caption wording
  changes are register entries (1974-25, 1974-29).
- The OCR's gridded game table is a register entry (1974-48).

**Citations and bibliography (LAYOUT/EDN).**

- In-text numeric citations are `\cite`s to `r1`…`r42`, so numbering and order
  are unchanged. "[18], p. 224" becomes "[18, p. 224]", and "[8, Chap. 6]" and
  "[26, p. 129]" are kept.
- Repeated-author dashes "———," are expanded to the names in [9], [12], [13],
  [23], [24] and [31].
- "North Holland" becomes "North-Holland" in [4], matching [40].
- "McGraw Hill" becomes "McGraw–Hill" in [8] and [38]. The source uses `--`;
  a hyphen would be the conventional form (minor open nit).
- "Ibid." becomes "ibid." in [42] [classified during consolidation].
- The dash in [23] "USSR — Izvestija" is set as an en dash.
- Content changes to references are entries 1974-64 … 1974-74.

## 4. Discrepancy register

Entries are ordered by position in the original. Each entry gives the naive
OCR reading ("OCR"), the scan where it differs from the OCR ("Scan"), the
current reconstruction ("Now"), the classification, the justification and the
history.

### p. 724, §1 Introduction

**1974-01 · CLAR · "trisecting the angle"**
- OCR: `doubling the cube and trisecting the angle with compass and straightedge`
- Now: "… trisecting **an arbitrary** angle …"
- Why: particular angles (for example a right angle) can be trisected with
  compass and straightedge. The impossibility is that of a general
  construction.

**1974-02 · CLAR · general quintic**
- OCR: `to solve the fifth degree polynomial equation`
- Now: "to solve the **general fifth-degree** polynomial equation"
- Why: individual quintics can be solvable by radicals. The Abel–Ruffini
  theorem concerns the general equation.

**1974-03 · ORIG · independence of the parallel postulate**
- OCR: `Gauss, Bolyai and Lobachevsky obtained the independence of the parallel postulate. They proved that this postulate cannot be proved from Euclid's axioms for geometry. Since the parallel postulate is consistent (assuming the theory of real numbers consistent), its negation is also unprovable. Thus the parallel postulate is undecidable on the basis of Euclid's axioms.`
- Now:
  - Gauss, Bolyai and Lobachevsky "developed non-Euclidean geometry".
  - "Later model constructions established the independence of the parallel
    postulate from the remaining axioms of an appropriate axiomatization of
    geometry."
  - Assuming the consistency of the real-number theory used for the models,
    both the postulate and its negation are consistent with those axioms, "Thus
    neither is provable from them."
- Why:
  - The postulate *is* one of Euclid's axioms, so independence must be from the
    remaining ones.
  - The nineteenth-century work developed the geometry. The independence proof
    comes from the later relative-consistency models (Beltrami, Klein,
    Poincaré).
  - The original also muddles which consistency statement yields which
    unprovability.

**1974-04 · ORIG · scope of Gödel's theorem**
- OCR: `More importantly, he proved that it was impossible to alter the foundations of mathematics so as to exclude undecidable propositions.`
- Now: "His work showed that incompleteness cannot simply be eliminated by
  adding axioms while retaining the relevant effectiveness and
  arithmetic-strength hypotheses. In its strengthened Gödel–Rosser form, the
  theorem applies to every consistent, effectively axiomatized theory that
  contains sufficient elementary arithmetic."
- Why: stated without hypotheses, the claim is false. Complete theories exist:
  decidable ones such as real closed fields, and true arithmetic, which is not
  effectively axiomatized. The hypotheses are attributed to the Gödel–Rosser
  form, not to the 1931 proof.

**1974-05 · CLAR · Cohen's independence results**
- OCR: `In 1963, P. Cohen [7] proved that the axiom of choice and the generalized continuum hypothesis were independent of the axioms of Zermelo-Fraenkel set theory.`
- Now: "In 1963–64, P. Cohen [7] established the independence results which,
  together with Gödel's relative-consistency work, show that the axiom of choice
  and the generalized continuum hypothesis are independent of Zermelo–Fraenkel
  set theory, assuming that theory is consistent."
- Why:
  - Independence is relative to the consistency of ZF.
  - Cohen supplies one direction; Gödel 1940 [12] supplies the other.
  - The date matches the two cited PNAS papers (50 (1963), 51 (1964)).

**1974-06 · TYPO · "Frederick"**
- OCR: `Carl Frederick Gauss`. The scan agrees.
- Now: "Carl Friedrich Gauss".
- Why: misprint of Gauss's name in the original.

### p. 725, §2 Recursive unsolvability

**1974-07 · LAYOUT · lost paragraph break [classified during consolidation]**
- OCR: `… absolutely unsolvable.\\ In the 1930's, proofs …`
- Scan: "It is natural to ask … absolutely unsolvable." is a one-line
  paragraph. "In the 1930's, …" begins a new, indented paragraph.
- Now: both sentences stand in one paragraph, separated by a single source
  newline.
- Why: this is a reflow slip in the reconstruction; the wording is unchanged.
  Restoring the paragraph break (a blank line) is recommended.

**1974-08 · CLAR · effective coding of inputs**
- OCR: `Suppose we are given a countable set $W$ and a particular subset $A$ of $W$.`
- Now: "… a countable set $W$, with a fixed effective representation of its
  elements by finite strings, and …"
- Why: an algorithm acts on finite codes. Abstract countability does not
  determine what "decide effectively" means.

**1974-09 · CLAR · words on generators and inverses**
- OCR: `given a word on the generators, whether or not`
- Now: "given a word on the generators **and their inverses**, …"
- Why: this is the standard alphabet of a group presentation.

### p. 726, §2

**1974-10 · CLAR · Boone–Rogers uniformity**
- OCR: `there is no partial algorithm to solve the word problem even for just those groups with solvable word problem.`
- Now: "there is no single uniform partial algorithm which, from an arbitrary
  finite presentation and a word, solves the word problem for every
  presentation of a group whose word problem is solvable."
- Why: each group with solvable word problem has an algorithm by definition.
  Boone–Rogers [5] concerns a single algorithm that works uniformly in the
  presentation.

**1974-11 · CLAR · 3-manifolds (dated)**
- OCR: `For 3-manifolds the problem is still open.`
- Now: "At the time of writing (1974), the problem for 3-manifolds was still
  open."
- Why: the author's report of an open problem is historical. No modern survey is
  substituted.

### p. 727, §2

**1974-12 · CLAR · Conway's Game of Life**
- OCR: `John Conway has announced that his "Game of Life" is undecidable.`
- Now: "John Conway has announced undecidability results for prediction problems
  in his ``Game of Life''."
- Why: undecidability is a property of a decision problem about the dynamics,
  not of a game as such.

**1974-13 · OCR · "nth roots"**
- OCR: `nth roots`
- Scan: italic *n*th.
- Now: `$n$th roots`.
- Why: the OCR lost the math variable.

**1974-14 · CLAR · domains of elementary functions**
- OCR: `The derivative of an elementary function is again elementary but some elementary functions do not have elementary integrals.`
- Now: "On intervals where the expression has regular, consistently chosen
  branches, its derivative is again elementary, but some elementary functions
  do not have elementary antiderivatives."
- Why: roots, logarithms and inverse functions need domains and branches. For
  example, the real $\sqrt{x^2}=|x|$ is not differentiable at $0$.

**1974-15 · ORIG · Richardson and elementary integration**
- OCR: `Interestingly enough, D. Richardson [34] has shown that no such algorithm exists.`
- Now:
  - "The answer depends on the precise expression class and its domain
    conventions."
  - Richardson [34] "proved undecidability results, including an integration
    problem, for suitably enlarged classes of real expressions allowing
    absolute value and a global real-domain interpretation."
  - "These qualifications are essential: this is not an unconditional
    impossibility theorem for the usual differential-algebraic formulation of
    elementary integration, for which decision procedures are available under
    suitable effective constant-field hypotheses."
  - A footnote, marked "Editorial qualification", cites R. H. Risch, *Bull. Amer.
    Math. Soc.* 76 (1970), 605–608. It is outside the numbered bibliography.
- Why: the unqualified negative claim overstates Richardson's result. In the
  Risch setting, elementary integrability is decidable, given effective
  constants and zero-testing.

**1974-16 · CLAR · language of Tarski's decision method**
- OCR: `… truth or falsity of all propositions of elementary algebra and geometry. The propositions of elementary algebra here include all formulas involving integers, inequalities, addition and multiplication in which the variables range over all real numbers.`
- Now: "… of all first-order sentences of elementary algebra and geometry. Here
  the algebraic language has integer constants, equality, inequalities, addition
  and multiplication, with all quantified variables ranging over the real
  numbers."
- Why: Tarski's theorem is for first-order sentences with the variables ranging
  over the reals. The original wording could be read as allowing quantification
  over the integers, which is undecidable.

### pp. 727–728, §2

**1974-17 · OCR · false paragraph at the page break**
- OCR: `… to deliver the coup de grâce to` then a new paragraph `Hilbert's tenth problem. By means of …`
- Scan: one sentence running across the page break 727/728.
- Now: the sentence is rejoined.

### p. 728, §2

**1974-18 · CLAR · domain of the prime-representing polynomial**
- OCR: `there exists a polynomial whose positive values are identical with the set of prime numbers.`
- Now: "a polynomial with integer coefficients whose positive values, on the
  prescribed domain of non-negative integer arguments, form exactly the set of
  prime numbers."
- Why: over real or rational arguments the statement is false. The
  Putnam–Matijasevič polynomial has integer coefficients and non-negative
  integer inputs.

**1974-19 · ORIG · complex solvability criterion**
- OCR: `A polynomial has solutions in complex numbers if and only if its degree is nonzero.`
- Now: "An equation $P=0$ over the complex numbers has a solution if and only if
  $P$ is the zero polynomial or is nonconstant; the only insoluble case is a
  nonzero constant polynomial."
- Why: the zero polynomial, whose degree is undefined or $-\infty$, vanishes
  everywhere. The criterion "degree nonzero" either omits it or depends on a
  convention. Proof of the corrected criterion: §5.2 (a).

**1974-20 · CLAR · rational solvability (dated)**
- OCR: `Oddly enough however, for rational numbers the problem is still open.`
- Now: "For rational numbers, however, the problem was still open at the time of
  writing (1974)."
- Why: this is a historical report. "Oddly enough" is dropped with the
  rewording.

**1974-21 · TYPO · "two person" [classified during consolidation]**
- OCR: `a two person win-lose game`. The scan agrees.
- Now: "a two-person win–lose game".
- Why: this is an unhyphenated compound modifier. The original itself writes
  "two-person" in the abstract and in §7.

**1974-22 · CLAR · total functions on ℕ**
- OCR: `Consider a function from the natural numbers to the natural numbers.` (§3)
- Now: "Consider a total function from the natural numbers
  $\mathbb N=\{0,1,2,\ldots\}$ to the natural numbers."
- Why: this fixes that $0\in\mathbb N$, which the unary convention "the number
  0 is represented …" needs. It also fixes the total-function convention used
  by Theorem 1 and Corollary 1.

### p. 729, §3 Turing machines

**1974-23 · CLAR · active states**
- OCR: `which we number $0,1,2, \cdots n$.`
- Now: "$0,1,2,\ldots,n$. Here $1,\ldots,n$ are the active states; the halting
  state $0$ is not counted in the phrase ``$n$-state machine''."
- Why: the count $(4n+4)^{2n}$, the cards, $\Sigma(n)$ and Table 1 all use this
  convention.

**1974-24 · TYPO · missing full stop**
- OCR: `one act per unit of time They are`. The scan agrees.
- Now: "… unit of time. They are …"

### p. 730, §3

**1974-25 · CLAR · Example 1 caption [caption wording classified during consolidation]**
- OCR: `\caption{Example 1. A Turing Machine with Two States.}` with the cards as an image.
- Now: "**Example 1. A Turing machine with two active states.**" followed by
  native cards. State 1 has 0: 1,R,2 and 1: 1,L,2. State 2 has 0: 1,L,1 and
  1: 1,L,0. These agree with the scan.
- Why: "active" makes the caption agree with the convention of 1974-23. The case
  change follows the heading conventions of §3.

**1974-26 · OCR · the trace of Example 1**
- OCR:
  ```
  \begin{array}{rl}
  001 & \rightarrow 001 \rightarrow 011 \rightarrow 111 \rightarrow \underset{1}{111 .} \\
  1 & 2 \\
  2
  \end{array}
  ```
- Scan: `001 → 001 → 011 → 111 → 111.`, with the state labels **1 2 1 2 0**
  set in a row beneath, one centred under each configuration.
- Now: $00\underset{1}{1}\to0\underset{2}{0}1\to\underset{1}{0}11\to1\underset{2}{1}1\to\underset{0}{1}11.$
  This is followed by an added sentence: "In this display, the subscript beneath
  a tape symbol gives the current state and identifies the scanned square; all
  unshown squares are blank." (CLAR)
- Why:
  - The OCR loses three labels, misaligns the rest and attaches the label "1"
    to the final configuration instead of "0".
  - The scan's centred labels give only the state sequence. The reconstruction
    puts each label under the scanned square, as determined by simulating the
    printed cards from state 1 on the rightmost square of `001`.
  - The first move changes only head and state, so the tape stays `001`.

**1974-27 · CLAR · "add 2" on a nonempty block**
- OCR: `started in state 1 scanning the leftmost of $n$ consecutive ones, then it will be seen to halt after 4 shifts.`
- Now: "… the leftmost of $n\geq 1$ consecutive ones, with the rest of the tape
  blank, then …"
- Why: on the blank tape ($n=0$) the machine takes 6 shifts and leaves 4 ones,
  as §5 says. The four-shift claim is for a nonempty block on an otherwise blank
  tape.

### p. 731, §3–4

**1974-28 · CLAR · clean unary input/output convention**
- OCR: `Definition. A function $f$ is Turing computable if there exists a Turing machine $M$ such that whenever $M$ is started in state 1 scanning the leftmost of $x+1$ consecutive ones, $M$ eventually halts scanning the leftmost of $f(x)+1$ consecutive ones.`
- Now: "A total function $f:\mathbb N\to\mathbb N$ is Turing computable if there
  exists a Turing machine $M$ such that, for every $x\in\mathbb N$, when $M$ is
  started in state 1 scanning the leftmost of exactly $x+1$ consecutive ones on
  an otherwise blank tape, $M$ eventually halts scanning the leftmost of exactly
  $f(x)+1$ consecutive ones, with every other tape square blank."
- Why: the composition $M[T[M^{(x)}]]$ in Theorem 1 feeds one machine's output
  to the next, so the output must be a valid clean input. The two printed
  example machines satisfy this stronger convention (§7).

**1974-29 · LAYOUT · Example 2 caption reworded [classified during consolidation]**
- OCR: `\caption{Example 2. A Turing Machine which Computes $f(x)=2 x$.}` with the cards as an image.
- Scan: "EXAMPLE 2. A TURING MACHINE WHICH COMPUTES $f(x) = 2x$."
- Now: "**Example 2. A Turing machine computing $f(x)=2x$.**" The five native cards
  agree with the scan:
  - state 1: 0,R,4 / 0,L,2
  - state 2: 1,R,3 / 1,L,2
  - state 3: 1,R,1 / 1,R,3
  - state 4: 0,L,4 / 0,L,5
  - state 5: 0,R,0 / 1,L,5
- Why: the rewording "which Computes" → "computing" has no reason on record and
  no content effect. As with 1974-A (the reverted Novikov–Boone wording, §6),
  restoring the printed "which computes" is recommended.

**1974-30 · ORIG · a sheet of paper in one tape square**
- OCR: `Is every computable function computable by a Turing machine? … However, as we allow any finite number of symbols in the alphabet, there is no reason why each individual tape square cannot be thought to correspond to an entire sheet of paper.`
- Now:
  - "Is every **intuitively effectively** computable function computable by a
    Turing machine?"
  - "However, finite portions of a two-dimensional array, together with their
    coordinates and symbols, can be encoded effectively by finite strings on a
    one-dimensional tape. A fixed finite alphabet does not require each entire
    sheet to fit into one tape square."
- Why:
  - The alphabet of a single machine is fixed and finite. It cannot contain a
    symbol for every possible sheet, since there are infinitely many possible
    finite sheets.
  - The correct reason is effective string or grid encoding.
  - The qualifier "intuitively effectively" separates the informal notion from
    Turing computability.
  - The original's next sentences about finite alphabets are retained.

**1974-31 · TYPO · unclosed parenthesis**
- OCR: `(Indeed, for this reason, … For a proof of this see [26, p. 129].`. The scan agrees, with no closing parenthesis.
- Now: "… see [26, p. 129].)"

**1974-32 · CLAR · statement of the thesis**
- OCR: `The assertion that every computable function is Turing computable, is known as the Church-Turing thesis.`
- Now: "The assertion that every intuitively effectively computable function is
  Turing computable is known as the Church-Turing thesis."
- Why: the thesis is otherwise tautological, since "computable" would mean
  Turing computable. The comma between subject and predicate is a
  punctuation slip (TYPO).

### p. 732, §5 A non-computable function

**1974-33 · CLAR · $n\ge1$ active states**
- OCR: `Formally, a 2-symbol Turing machine of $n$ states is simply a mapping`
- Now: "For $n\geq1$, a 2-symbol Turing machine of $n$ active states is formally a
  mapping"
- Why: a machine starts in state 1, so $n=0$ is outside the definitions, and the
  count uses active states (1974-23).

**1974-34 · CLAR · δ for the transition table**
- OCR: `f:\{0,1\} \times\{1,2,3, \cdots n\} \rightarrow\{0,1\} \times\{R, L\} \times\{0,1,2,3, \cdots n\}`
- Now: $\delta:\{0,1\}\times\{1,\ldots,n\}\to\{0,1\}\times\{R,L\}\times\{0,1,\ldots,n\}$
- Why: in the same section and in Theorem 1, $f$ is the number-theoretic function
  being dominated. Renaming the transition table avoids the clash.

**1974-35 · CLAR · what $(4n+4)^{2n}$ counts**
- OCR: `Thus there are exactly $(4 n+4)^{2 n}$ Turing machines with $n$-states, a finite number.`
- Now: "… exactly $(4n+4)^{2n}$ fully specified, labelled transition tables with
  $n$ active states, a finite number. Unreachable states and transitions are
  permitted, and are counted."
- Why:
  - Each of the $2n$ entries has $2\cdot2\cdot(n+1)=4n+4$ values.
  - The count is of labelled complete tables, not of behaviourally distinct
    machines.
  - $H(n)$, the retracing proof (1974-61) and the padding arguments depend on
    this convention.

**1974-36 · CLAR · the maximum exists**
- OCR: `$\Sigma$ is a well defined function of $n$, because a finite set of numbers has a greatest element.`
- Now: "… because the finite set of scores of halting machines is nonempty and
  hence has a greatest element. An immediate-halting transition supplies at
  least one such machine."
- Why: the empty set has no maximum.

### p. 733, §5

**1974-37 · CLAR · the extra card of $\Sigma(n)<\Sigma(n+1)$**
- OCR: an image of the card.
- Now: the native card "State $n+1$" with 0: 1,R,0 and 1: 1,R,$n+1$, which
  agrees with the scan. Two sentences are added: "Redirect each old transition
  to the halting state into state $n+1$ instead. The added state scans right
  across any ones and changes the first zero to a one before halting."
- Why: the card works only if the old halts enter it. It adds exactly one
  one, which needs the tape at halting time to hold finitely many ones. That
  holds, since a run of $t$ steps stays in $[-t,t]$.

**1974-38 · LAYOUT · lost paragraph break [classified during consolidation]**
- OCR: `Can a formula for $\Sigma(n)$ be found?\\ There are difficulties …`
- Scan: the question is its own paragraph, and "There are difficulties …"
  begins a new, indented paragraph.
- Now: one paragraph.
- Why: this is a reflow slip in the reconstruction. Restoring the break is
  recommended.

**1974-39 · TYPO · "so called" [classified during consolidation]**
- OCR: `This is the so called halting problem.`. The scan agrees.
- Now: "so-called".
- Why: the original writes "the so-called *domino problem*" on p. 727. The form
  is made uniform.

**1974-40 · ORIG · the printer $M^{(x)}$ needs $x\ge1$**
- OCR: `For each $x$, let $M^{(x)}$ be a Turing machine with $x+1$ states which will print $x+1$ consecutive ones onto a blank tape and halt scanning the leftmost of these.`
- Now: "For each integer $x\geq1$, let $M^{(x)}$ …"
- Why:
  - For $x=0$ no one-state machine does this under compulsory left or right
    movement (proof in §5.2 (b)).
  - The proof of Theorem 1 uses only $x\ge 6+c\ge1$, so neither the theorem nor
    the bound $n\ge 12+2c$ changes.
- Classification: this is an original edge-case error. A note of the Lean
  formalization says "the text is correct as printed" and "the text's $x\ge1$
  is necessary". That note refers to the edition's text, which already carries
  the emendation. The printed original (scan p. 733) says "For each $x$", so the
  classification ORIG stands.

**1974-41 · CLAR · blank rows of $M^{(2)}$ and the general printer**
- OCR: three card images.
- Scan: Card 1 has 0: 1,L,2 and 1: —. Card 2 has 0: 1,L,3 and 1: —. Card 3 has
  0: 1,R,3 and 1: 1,L,0. The read-1 rows of cards 1 and 2 are left blank (—).
- Now:
  - The same cards, with the blank rows filled as 1,L,0.
  - A note: "The read-1 rows in states 1 and 2 are unreachable on blank input;
    their entries above are arbitrary completions of rows left blank in the
    original."
  - A general description: states $1,\ldots,x$ write a one on a zero, move left
    and enter the next state; state $x+1$ writes a one on a zero and moves right
    in the same state, and on a one moves left and halts.
- Why: a card must be a total table. The completions are unreachable. The
  general $M^{(x)}$ is asserted but not described in the original.

### p. 734, proof of Theorem 1, Corollary 1, §6

**1974-42 · CLAR · how machines are composed**
- OCR: `It is obtained by relabeling states and is constructed so as to print $f(2 x)+1$ ones`
- Now: "It is obtained by relabeling the active states into disjoint blocks and
  redirecting each intermediate machine's halt transitions to the starting state
  of the next machine. By the clean unary input/output convention, it is
  constructed so as to print …"
- Why: relabelling alone does not compose programs. No connecting states are
  needed, so the count $x+6+c$ is unchanged (§5.2 (c)).

**1974-43 · CLAR · a strictly increasing majorant**
- OCR: `\hat{f}(n)=\sum_{i=0}^{n} f(i)`
- Now: $\hat f(n)=n+\sum_{i=0}^{n}f(i)$
- Why: the original sum is only non-decreasing; for $f\equiv0$ it is constant.
  Adding $n$ makes it strictly increasing under either reading of "increasing",
  and it is still a computable majorant (§5.2 (d)). Theorem 1's proof needs only
  monotonicity, so the original is not wrong under the non-strict reading.

**1974-44 · TYPO · missing section number 6**
- OCR: `The halting problem. Evidently, …`
- Scan: the bold run-in heading "The halting problem." has no number, between
  §5 and "7. An unsolvable game".
- Now: `\section{The halting problem}`, numbered 6.
- Why: this is a numbering slip in the original. The text's own "Section 7" for
  the game presupposes it.

**1974-45 · CLAR · blank-tape formulation**
- OCR: `the halting problem: To decide, given a Turing machine $M$, whether or not $M$ will eventually halt.`
- Now: "… to decide, given a Turing machine $M$, whether or not $M$ will eventually
  halt when started in state 1 on a blank tape."
- Why: the reduction from $\Sigma$ uses exactly the blank-tape problem.

**1974-46 · ORIG · attribution to Church alone**
- OCR: `The halting problem was the first decision problem to be proved unsolvable. Its unsolvability was obtained by Church in 1936 [6].`
- Now: "The foundational undecidability results were obtained by Church [6] and
  Turing [42] in 1936–37; their original formulations should be distinguished
  from this particular blank-tape formulation."
- Why: Church 1936 proved an unsolvable problem of elementary number theory,
  formulated with λ-definability. The halting-type problem for machines is
  Turing's (1936–37), and the blank-tape variant is later. Crediting the
  "halting problem" to Church alone is historically inaccurate.

**1974-47 · ORIG · "impartial win lose game"**
- OCR: `Consider the following two-person impartial win lose game with perfect information.`. The scan agrees.
- Now: "Consider the following two-person win–lose game with perfect information."
- Why:
  - "Impartial" is a technical term: both players have the same moves from every
    position. It does not fit this game, where I and II make different kinds of
    choices and have different winning conditions.
  - The proof needs only a finite, perfect-information, win–lose game.
  - The missing hyphen in "win lose" is a TYPO, corrected with it.

### p. 735, §7 An unsolvable game

**1974-48 · OCR · the move display**
- OCR:
  ```
  \begin{tabular}[t]{|l|l|} \hline
  first & $I$ picks $n$, \\ \hline
  then & II picks $m$ (knowing $n$ ), \\ \hline
  finally & I picks k (knowing m). \\ \hline
  ```
- Scan: three lines without rules, in italics: "*first* I picks n, / *then*
  II picks m (knowing n), / *finally* I picks k (knowing m)."
- Now: a borderless tabular, "first — player I picks $n$; then — player II picks
  $m$, knowing $n$; finally — player I picks $k$, knowing $n$ and $m$." In the
  following sentence, `Player $I$` becomes "Player I", with a roman numeral.
- Why:
  - The grid, the math-italic $I$ and the non-math "k", "m" are OCR artifacts.
  - "knowing $n$ and $m$" is a CLAR: player I chose $n$ and so knows it. The
    strategy argument uses both.

**1974-49 · CLAR · the referee's test**
- OCR: `operate each of them through exactly $m+k$ shifts to determine the winner.`
- Now: "simulate each of them for at most $m+k$ shifts, stopping a simulation
  upon halting, and check whether any first halt occurs on shift $m+k$."
- Why: a machine that has halted performs no further shifts, and an earlier halt
  does not count. The finite bounded simulation is what makes the winner
  decidable.

**1974-50 · CLAR · finite-game determinacy**
- OCR: `Now it is well known that a game of finite length is determined.`
- Now: "… that a finite-length, perfect-information win–lose game with no draws is
  determined."
- Why: finite length alone does not give a pure winning strategy. Simultaneous
  or imperfect-information games are counterexamples.

**1974-51 · CLAR · Theorem 2 for player I**
- OCR: `… Hence player II has no computable winning strategy.` (end of proof)
- Now: adds "Since player II has a winning strategy, player I has no winning
  strategy at all, and in particular no computable one."
- Why: the theorem claims both players; the proof as printed addresses only II.

### pp. 735–736, §8 Generalizations of the Busy Beaver problem

**1974-52 · ORIG · "before halting" missing from the restated SH**
- OCR: `We have defined $S H(n)$ to be the maximum possible number of shifts which an $n$-state (2-symbol) Turing machine can perform when started in state 1 on a blank tape.`
- Now: "… can perform before halting, when started in state 1 on a blank tape.
  Only machines that halt enter this maximum."
- Why: §7 defines SH "before halting". Without the restriction, non-halting
  machines make the maximum infinite.

**1974-53 · CLAR · SC counts active scans; H counts labelled tables**
- OCR: `… which an $n$-state Turing machine can scan in an active state before halting (…). Define $H(n)$ to be the number of different $n$-state Turing machines which halt …`
- Now: adds "The square entered by the final halting shift is not counted unless
  it was scanned earlier in an active state." It also reads "different labelled,
  fully specified $n$-state Turing machines".
- Why: with this reading $\Sigma(n)\le SC(n)\le SH(n)$ holds (§5.2 (f)). The
  labelled-table convention matches the count $(4n+4)^{2n}$ and Table 1's
  $H(1)=32$.

**1974-54 · CLAR · why $H$ is not computable**
- OCR: `For it is not difficult to show that if an algorithm existed for computing $H$, then the halting problem would be solvable.`
- Now: "Indeed, given $H(n)$, one can dovetail all $n$-state machines until exactly
  $H(n)$ of them have halted. These are all the halting machines; the rest never
  halt. Thus an algorithm for $H$ would solve the halting problem."
- Why: supplies the reduction.

**1974-55 · CLAR · the table is historical**
- OCR: `The known values of these functions appear in the following table.`
- Now: "The values and lower bounds reported in 1974 appear in Table 1."
- Why: the entries for $n\ge4$ are lower bounds, not values, and they are the
  1974 records. The edition does not update them (§6).

**1974-56 · OCR · Table 1, the SH(10) entry (and table layout)**
- OCR: a 5-row × 10-column grid. The critical cell is `$10^{4 \times 10^{44} \leqq}$`, with the inequality inside the exponent.
- Scan: $10^{4\times10^{44}}\leqq$, where the ≦ follows the power.
- Now: $SH(10)\geq10^{4\times10^{44}}$.
- Why: this is an OCR misplacement. The intended bound is
  $SH(10)\ge10^{4\times10^{44}}$.
- Layout (LAYOUT/CLAR):
  - The table is transposed: rows $n=1,\ldots,8,10$; columns $\Sigma$, SC, SH,
    $H$.
  - "$13\leqq$" (meaning $13\le\Sigma(4)$) is written "$\ge13$".
  - Blanks become em dashes.
  - The caption reads "Values and lower bounds reported in 1974 (not a current
    record table)", with a note: "An em dash means that no entry was supplied in
    the original table … The original table has no column for $n=9$."
  - All 36 data positions ($4\times9$) of the scan, including blanks, are
    preserved.
  - The values agree with the scan: $\Sigma$: 1, 4, 6, ≥13, ≥16, ≥35,
    ≥22,961, ≥9×10⁴¹, ≥10^(2×10⁴⁴); SC: 1, 4, 7, ≥14; SH: 1, 6, 21, ≥107, —,
    ≥436, ≥10⁶⁹³, —, ≥10^(4×10⁴⁴); $H$: 32, 9,784, 7,571,840.

**1974-57 · LAYOUT · "row 1"**
- OCR: `This is illustrated in row 1 by the very large scores`
- Now: "… in the $\Sigma(n)$ column …"
- Why: this follows the transposition in 1974-56.

**1974-58 · LAYOUT · multiplication dots in (4) [classified during consolidation]**
- OCR: `\text { (3) } S C(n)<\Sigma(3 n) \text { and }(4) S H(n) \leqq n \cdot S C(n) \cdot 2^{S C(n)}`
- Scan: "(3) $SC(n)<\Sigma(3n)$ and (4) $SH(n)\leqq n\cdot SC(n)\cdot2^{SC(n)}$."
- Now: an `align` display with (3) $\mathrm{SC}(n)<\Sigma(3n)$ and (4)
  $\mathrm{SH}(n)\le n\,\mathrm{SC}(n)\,2^{\mathrm{SC}(n)}$, in which the
  printed middle dots are replaced by thin spaces.
- Why: the product is the same. This is a typesetting change with no content
  effect.

**1974-59 · CLAR · the construction behind (3)**
- OCR: `Inequality (3) is derived from the fact that each $n$-state Turing machine may be simulated (on every other square of the tape) by a $3 n$-state Turing machine which records the number of squares scanned with ones.`
- Now: "Inequality (3) follows by simulating a halting $n$-state machine on every
  other tape square and marking the intervening squares with ones. The
  construction can be arranged with at most $3n$ active states to leave strictly
  more ones than the number of actively scanned squares of the original machine.
  Unused states may be added to obtain exactly $3n$ states. A detailed
  construction justifying both the strict inequality and the state bound is
  given in the editorial notes, `Papers/1974/jones1974_editorial_notes.md`
  (entry 1974-59), and is formalized in
  `Lean/Diophantine/Paper1974/Doubling.lean`."
- Why:
  - The printed sketch does not show why the result is *strict*, or why $3n$
    states suffice.
  - The original strict inequality is kept, not weakened.
  - The construction is given in §5.2 (g) of this document. It is formalized as
    `Jones1974.sc_lt_sigma` in `Lean/Diophantine/Paper1974/Doubling.lean`.
- Pointer: since 24 September 2026 the text names this entry and the Lean file
  (74-R4-08, 74-R4-11). An earlier revision of the edition said only "is given
  in the editorial notes", without naming a file.

**1974-60 · ORIG · "retraceable and therefore immune"**
- OCR: `The range of $H$ is retraceable and therefore immune but not hyperimmune.`
- Now: "The range of $H$ is retraceable and nonrecursive, hence immune. It is not
  hyperimmune, because its increasing enumeration $H(n)$ has the computable upper
  bound $(4n+4)^{2n}$."
- Why:
  - Retraceability alone does not imply immunity: every infinite recursive set is
    retraceable and not immune.
  - An infinite retraceable set is immune exactly when it is nonrecursive.
  - Non-hyperimmunity follows from the computable bound (2).

**1974-61 · CLAR · proof of retraceability and immunity (marked "Editorial proof detail")**
- OCR: nothing corresponds; the paragraph is added after "… is r.e. nonrecursive."
- Now:
  - An italic-labelled paragraph "*Editorial proof detail.*" writes
    $U_n=(4n+4)^{2n}$ and $L_n=4(4n+4)^{2n-1}$.
  - The immediate halters give $L_n\le H(n)$, and (2) gives $H(n)<U_n$.
  - For $n\ge2$, $L_n>U_{n-1}$, so these disjoint computable intervals determine
    $n$ from $H(n)$.
  - Dovetailing the $n$-state machines until $H(n)$ have halted determines which
    canonically padded $(n-1)$-state machines halt, hence $H(n-1)$ (partial
    computable retracing, with $H(1)\mapsto H(1)$).
  - An infinite r.e. subset would give $H$ computably, which proves immunity.
    The intervals also show that $H$ is strictly increasing.
- Why: the article asserts retraceability without the construction. Full proof
  in §5.2 (h).
- History: an earlier revision of this paragraph derived both bounds
  "$L_n\le H(n)<U_n$" from the immediate halters. The attribution was corrected
  (74-R4-09): the immediate halters give only the lower bound, and the strict
  upper bound is (2), which needs a non-halting table.

**1974-62 · CLAR · probability of a random machine halting**
- OCR: `Consider a Turing machine programmed by a monkey. The probability of such a random Turing machine halting when started on a blank tape might be expressed by the limit of the frequencies:`
- Now: "… For each fixed $n$, choose uniformly among the $(4n+4)^{2n}$ labelled
  transition tables. The probability of halting on a blank tape is then
  $H(n)/(4n+4)^{2n}$. One may ask whether these probabilities have a limit as $n$
  tends to infinity:"
- Why:
  - There is no uniform probability on the set of all finite tables; there is
    one for each $n$.
  - The original presupposes that the limit exists, which is not shown.
  - The display $\lim_{n\to\infty}H(n)/(4n+4)^{2n}$ is unchanged.

### p. 737, §8 (end) and references

**1974-63 · ORIG · 0.471 → 0.472; limit not established**
- OCR: `the first three values of this quotient are (approximately) $.500, .471$ and .451 . However, the exact value of the limit is unknown.`. The scan agrees: ".500, .471 and .451".
- Now: "… (approximately) $0.500$, $0.472$ and $0.451$, rounded to three decimal
  places. The existence and value of the displayed limit are not established
  here."
- Why:
  - $9784/20736=1223/2592=0.4718364\ldots$ rounds to $0.472$. The printed
    $.471$ is a truncation, while $.451$ ($59155/131072=0.451316\ldots$) and
    $.500$ are consistent with either convention.
  - The rounding convention is now stated.
  - "The exact value … is unknown" presupposed existence (1974-62).

**1974-64 · BIB · [9] "this Monthly"**
- OCR: `-, Hilbert's tenth problem is unsolvable, this Monthly, 80 (1973) 233-269.`
- Scan: "———, … this MONTHLY, …"
- Now: "M. Davis, Hilbert's tenth problem is unsolvable, American Mathematical
  Monthly, 80 (1973) 233–269."
- Why: the in-house "this Monthly" is expanded, since the edition is no longer
  printed in the Monthly. The journal is set in roman like every other entry
  (74-R4-10).

**1974-65 · BIB · [13] Gödel 1931, last page**
- OCR: `Monatsh. Math. und Physik, 38 (1931) 173-189.`. The scan agrees.
- Now: "173–198".
- Why: the printed range transposes the last two digits. The publisher's record
  (Springer, DOI 10.1007/BF01700692) gives 173–198.

**1974-66 · OCR · [18] Kleene, preliminary pagination**
- OCR: `1952, $\mathrm{x}+550 \mathrm{pp}$.`
- Scan: "1952, x + 550 pp."
- Now: "1952, x + 550 pp."
- Why: the OCR set the Roman numeral x as mathematics. The pagination is set as
  plain prose, with a single full stop.

**1974-67 · BIB · [23] "USSSR" (misprint in the original; reclassified)**
- OCR: `Mathematics of the USSSR -Izvestija`
- Scan: "Mathematics of the USSSR — Izvestija". The misprint is in the scan; this
  was checked at 600 dpi, and the PDF's own text layer also reads "USSSR".
- Now: "Mathematics of the USSR–Izvestija".
- Why: the journal is *Mathematics of the USSR – Izvestiya*.
- Classification corrected: this was first classified as an OCR typo, on the
  assumption that "the scan reads USSR". The scan shows that the extra S is
  printed, so the classification is an original misprint (BIB). The OCR's only
  own defect here is the spacing around the dash.

**1974-68 · BIB · [25] Miller, preliminary pagination**
- OCR: `vii + 106 pp.`. The scan agrees.
- Now: "viii + 106 pp."
- Why: the contemporary review by C. R. J. Clapham (*Bull. London Math. Soc.* 6
  (1974), 117–118, DOI 10.1112/blms/6.1.117) gives viii + 106.

**1974-69 · BIB · [26] Minsky, preliminary pagination**
- OCR: `xii + 317 pp.`. The scan agrees.
- Now: "xvii + 317 pp."
- Why: the review by H. Maurer (*Canad. Math. Bull.* 11 (1968), 342–343, DOI
  10.1017/S0008439500029350) gives xvii + 317.

**1974-70 · BIB · [27] "Mathematicheskii"**
- OCR: `Mathematicheskii Institut`. The scan agrees.
- Now: "Matematicheskii Institut".
- Why: this is the standard transliteration of *Математический*. The printed
  form mixes English "th" into the Russian word.
- Classification: this was first listed among the global orthographic
  normalizations. The scan shows the form is printed, so it is recorded here as
  a correction of the original.

**1974-71 · BIB · [37] R. M. Robinson, first page**
- OCR: `Invent. Math., 12 (1971) 117-209.`. The scan agrees.
- Now: "177–209".
- Why: the publisher's record (Springer, DOI 10.1007/BF01418780) gives 177–209.

**1974-72 · OCR · [38] "Recarsive"**
- OCR: `Theory of Recarsive Functions`
- Scan: "Recursive".
- Now: "Recursive".

**1974-73 · BIB · [38] Rogers, preliminary pagination**
- OCR: `ix + 482 pp.`. The scan agrees.
- Now: "xix + 482 pp."
- Why: the library record of the 1967 McGraw-Hill edition gives xix + 482 (KIT
  Library, record 509131).

**1974-74 · BIB · [40] Tarski–Mostowski–Robinson, preliminary pagination**
- OCR: `xi + 98 pp.`. The scan agrees.
- Now: "ix + 98 pp."
- Why: the bibliographic description of the 1953 North-Holland edition, and of
  the unabridged Dover reprint, gives ix + 98. See, for example, the digitized
  copy at archive.org, "undecidabletheor0000tars".

## 5. Editorial additions

### 5.1 Inventory

The reconstruction adds the following to the printed text. Apart from the
three items flagged in place (the Risch footnote, the table note and the
"Editorial proof detail"), additions are integrated silently. The edition
notice warns that "added explanations should not be mistaken for verbatim
wording of the original".

- **Flagged in place:**
  - the footnote "Editorial qualification: compare R. H. Risch …" (1974-15);
  - the explanatory note under Table 1 (1974-56);
  - the paragraph "*Editorial proof detail*" (1974-61).
- **Stated hypotheses and domains:**
  - effective coding (1974-08);
  - total functions on $\mathbb N\ni0$ (1974-22);
  - active states $n\ge1$ (1974-23, 1974-33);
  - labelled complete tables (1974-35, 1974-53);
  - clean unary input/output (1974-27, 1974-28);
  - $x\ge1$ for the printers (1974-40);
  - the blank-tape halting problem (1974-45);
  - "before halting" (1974-52);
  - active scans (1974-53);
  - the per-$n$ uniform distribution (1974-62).
- **Proof completions:**
  - the nonempty maximum (1974-36);
  - halt redirection for card $n+1$ (1974-37);
  - completed printer cards and the general $M^{(x)}$ (1974-41);
  - the composition mechanism (1974-42);
  - the strict majorant (1974-43);
  - the referee test (1974-49);
  - Theorem 2 for player I (1974-51);
  - $H$ not computable (1974-54);
  - the construction for (3) (1974-59);
  - retraceability and immunity (1974-60, 1974-61).
- **Explanations:**
  - the reading of the trace (1974-26);
  - the historical status of the table (1974-55, 1974-56);
  - the rounding convention (1974-63).
- **Historical dating:** 1974-11, 1974-20.
- **Mathematical and historical qualifications of §§1–2:** 1974-01 … 1974-05,
  1974-10, 1974-12, 1974-14 … 1974-16, 1974-18, 1974-19, 1974-30, 1974-32,
  1974-46, 1974-47, 1974-50.

### 5.2 Supporting arguments referred to by the edition

**(a) Complex solvability (1974-19).** For $P\in\mathbb C[x_1,\ldots,x_r]$ with
$r\ge1$:

$$\exists z\in\mathbb C^r\ \ P(z)=0 \iff P\equiv0 \text{ or } P \text{ is nonconstant}.$$

- If $P$ has positive degree in $x_j$, specialise the other variables so that
  the leading coefficient in $x_j$ stays nonzero. This is possible because
  $\mathbb C$ is infinite.
- Then apply the fundamental theorem of algebra.
- For integer coefficients, the three cases (zero, nonzero constant,
  nonconstant) are decided by inspection.

**(b) No printer $M^{(0)}$ (1974-40).**

- A one-state machine on the blank tape either halts at its first shift or
  re-enters state 1 on a fresh blank square.
- If it halts at the first shift, the head has moved off the only square it
  could have written.
- Otherwise it moves in one fixed direction over zeros forever.
- In the printer family itself, the last-state card (0: 1,R,same; 1: 1,L,halt)
  never meets a one when started on a blank tape, so the machine never halts.
- For $x\ge1$, $M^{(x)}$ uses $x+1$ states and $x+2$ shifts. It halts on the
  leftmost of $x+1$ ones.

**(c) Clean composition (1974-28, 1974-42).**

- The input is exactly $x+1$ consecutive ones on a blank tape, scanned at the
  leftmost; the output has the same form with $f(x)+1$ ones.
- Rename the active states of the stages into disjoint blocks and redirect every
  halt of a stage to the first state of the next stage. The redirected
  transition still performs its move, which leaves the head on the next input.
- $M[T[M^{(x)}]]$ therefore has $(x+1)+5+c=x+6+c$ states and prints
  $f(2x)+1$ ones.
- Examples 1 and 2 satisfy the clean convention: they erase their scratch work
  and halt on the leftmost output one.

**(d) Majorant and growth (1974-43, and "$f(\Sigma(n))<\Sigma(n+1)$ infinitely often", §6).**

- $\hat f(n)=n+\sum_{i\le n}f(i)$ satisfies $\hat f(n)\ge f(n)$ and
  $\hat f(n+1)-\hat f(n)=1+f(n+1)>0$.
- Suppose instead that $\Sigma(n+1)\le f(\Sigma(n))$ for all $n\ge N$. Put
  $h(t)=\max\{t+1,f(0),\ldots,f(t)\}$, which is computable and non-decreasing.
- Starting from a hard-coded $B_N\ge\Sigma(N)$, the iteration $B_{n+1}=h(B_n)$
  gives a computable eventual upper bound for $\Sigma$. This contradicts
  Corollary 1.

**(e) The game (1974-48 … 1974-51).**

- For fixed $n,m,k$, the referee runs finitely many simulations of at most
  $m+k$ shifts each, and accepts only a *first* halt at shift $m+k$.
- With $k\ge1$, player I can win against $m$ exactly when $m<SH(n)$: take
  $k=SH(n)-m$ and a machine attaining $SH(n)$.
- Hence $f$ wins for II if and only if $SH(n)\le f(n)$ for all $n$. $SH$ is such
  a strategy, and no computable $f$ is, since eventually
  $f(n)<\Sigma(n)\le SH(n)$.
- Since II wins, I has no winning strategy.

**(f) The inequalities (1) and (4).**

- A halting run's final ones lie on actively scanned squares, and each active
  scan costs a shift. This gives $\Sigma(n)\le SC(n)\le SH(n)$.
- For (4), let a halting run actively visit $k$ squares. These squares form an
  interval.
- The pre-transition configurations number at most $n\cdot k\cdot2^k$. A repeated
  configuration would force a loop, so $SH(n)\le n\,SC(n)\,2^{SC(n)}$.

**(g) The strict $3n$-state bound $SC(n)<\Sigma(3n)$ (1974-59).**

- Let $M$ halt with $k$ actively scanned squares. Virtual square $i$ is held at
  physical square $2i$, and odd squares mark crossed edges.
- The simulating machine has $n$ main states $A_q$. For each distinct pair
  $(q',d)$ occurring as target and direction of a *nonhalting* rule, it has one
  helper $B_{q',d}$. At least one of the $2n$ rules halts, so there are at most
  $2n-1$ pairs. There is one final state $Z$.
- For a nonhalting rule $(q,b)\mapsto(w,d,q')$:
  - $A_q$ writes $w$, moves $d$ and enters $B_{q',d}$;
  - $B_{q',d}$ writes $1$ on the edge square, moves $d$ again and enters $A_{q'}$.
- For a halting rule, $A_q$ writes $1$, moves and enters $Z$. $Z$ runs right over
  ones, writes $1$ on the first $0$ and halts.
- The $k-1$ internal edges of the visited interval have all been crossed, the
  last data square holds $1$, and $Z$ adds one more. The machine therefore
  leaves at least $k+1$ ones, using at most $n+(2n-1)+1=3n$ states. It is
  padded to exactly $3n$ with unused states.
- With $k=SC(n)$ this gives $SC(n)<\Sigma(3n)$.

**(h) Retraceability and immunity of $\operatorname{ran}H$ (1974-60, 1974-61).**

- Each entry of a table has $4n+4$ values. Fixing the initial blank-symbol entry
  to one of its 4 halting choices gives
  $L_n=4(4n+4)^{2n-1}\le H(n)<U_n=(4n+4)^{2n}$, the upper bound by (2), since
  the table in which every entry moves right into state 1 never halts.
- For $n\ge2$, $L_n/U_{n-1}=16(n+1)(1+1/n)^{2n-2}>1$. So the intervals
  $[L_n,U_n)$ are disjoint and ordered. They determine $n$ from $H(n)$, and $H$
  is strictly increasing.
- Given $h=H(n)$, dovetail all $n$-state tables from the blank tape until $h$
  have halted. The halting set is then complete.
- Embed each $(n-1)$-state table as an $n$-state table with one fixed unreachable
  extra state. The number of halting embeddings is $H(n-1)$. For $n=1$, return
  $h$. This is a partial computable retracing function on the range.
- If an infinite r.e. $A\subseteq\operatorname{ran}H$ existed:
  - for given $n$, wait for $a\in A$ with $a>U_n$ and retrace to index $n$;
  - this computes $H(n)$, which is impossible, so the range is immune;
  - the computable majorant $U_n$ shows it is not hyperimmune.
- The proof uses the labelled, complete-table convention. Counting up to state
  renaming, or requiring reachability, would need a separate argument.

**(i) Frequencies (1974-63).**

$$\frac{32}{64}=\frac12,\qquad \frac{9784}{20736}=\frac{1223}{2592}=0.47184,\qquad \frac{7571840}{16777216}=\frac{59155}{131072}=0.45132,$$

rounded to three places these are $0.500$, $0.472$ and $0.451$. Nothing here
proves that the limit exists.

## 6. Readings examined and retained

- **Novikov–Boone dates (p. 726): reverted, no net discrepancy (item 1974-A).**
  - The printed text reads "During the period 1954–56, P.S. Novikov and W. W.
    Boone independently proved …".
  - An earlier revision of this edition replaced the dates with "In the
    mid-1950s", arguing that Boone's series ran to 1957.
  - That change was reverted and the printed wording restored (74-R4-01). The
    range is the author's historical statement and is not wrong: Novikov 1955,
    and Boone's series 1954–57 (reference [3]). The replacement should not be
    re-proposed.
  - The only remaining difference is the initials spacing "P. S." (§3).
- **Table 1 is not updated.** All 36 positions agree with the scan. The bounds
  are the 1974 records and are not typos, although most have since been
  superseded. The blank cells and the missing $n=9$ column are explained in the
  table note, not filled.
- **Retained claims, checked by hand:**
  - the strict inequality (3), which is kept rather than weakened (§5.2 (g));
  - (4), and the $n\ge12+2c$ arithmetic of Theorem 1 ((i), (ii));
  - "$\Sigma$ itself is increasing", and $\Sigma(n)<\Sigma(n+1)$ (with "move
    right (or left)" kept as printed);
  - $f(\Sigma(n))<\Sigma(n+1)$ infinitely often, and $\Sigma(n)!<\Sigma(n+1)$
    (§5.2 (d));
  - the equal degree $0'$ of the four functions;
  - the hyperimmunity of $\operatorname{ran}\Sigma$;
  - that $\{(m,n):m\le H(n)\}$ is r.e. and nonrecursive.
- **Retained numbers:**
  - "25,600,000,000 different Turing machines with 4 states" $=20^8$;
  - Example 1 on the blank tape takes 6 shifts and leaves 4 ones, and
    $\Sigma(2)=4$;
  - "the machine of example 2 loops forever": on the blank tape it enters state 4
    on a blank and moves left forever.
- **Retained theorem hypotheses.** Theorem 1's "increasing" (non-decreasing
  suffices) and Corollary 1 are kept as printed. The edition adds only the
  majorant $n+\sum f(i)$ (1974-43). The Lean formalization proves Corollary 1
  without Kleene's closure theorem (bound $17+2c$), but the article's route is
  kept.
- **Unchanged "21 variables" ([24]).** It agrees with the addendum in the 1976
  article of this corpus.
- **References [22] and [1], [24].** "Dokl. Acad." in [22], against "Dokl. Akad."
  in [1] and [24], is left as printed.
- **[22] page range.** 354–357 agrees with the corpus-wide decision on the
  354–357 / 354–358 question: the JSL Reviews record of the translation gives
  354–357.
- **Uncited references.** [3], [36] and [38] are cited nowhere in the text, as in
  the original. Nothing is dropped or renumbered.
- **[8] and [12].** The paginations "xxv + 210" and "v + 69" were not
  questioned.
- **No further formula change.** Complete readings of the mathematical text
  found no further formula change and no mathematical error beyond the entries
  above.
- **Number diff and spelling check.**
  - Every multi-digit number of the OCR was compared with the edition. The only
    differences are 1974-63, 1974-65 and 1974-71, plus edition metadata.
  - A dictionary check of all prose words found no misspelling. Only names and
    technical terms (hyperimmune, retraceable, nonrecursive) were flagged.

## 7. Verification summary

- **Machines and counts.** `Papers/verification/round4_1974_checks.py` writes
  `round4_1974_results.json`. It is pure Python and runs in under a minute.
  - Example 1: 6 shifts and 4 ones on the blank tape. From a nonempty block it
    adds 2 in 4 shifts and halts on the leftmost one.
  - Example 2 computes $2x$ for $x=0..8$ and loops on the blank tape.
  - $M^{(x)}$ was checked for $x=1..6$.
  - $T[M^{(x)}]$ prints $2x+1$ ones with $x+6$ states.
  - Card $n+1$ adds exactly one 1.
  - Exhaustive enumeration of all labelled 1- and 2-state tables gives 64 and
    20,736 tables; $H=32$ and $9784$; $\Sigma=1,4$; SC$=1,4$; SH$=1,6$; and
    32 and 6,912 immediate halts ($=L_n$).
  - $L_n>U_{n-1}$ holds for small $n$.
- **Further checks.** The following were also run:
  - 402 unary, printer and composition cases for $x\le100$;
  - the strict $3n$-state construction on every halting 1- and 2-state table
    ($32+9784$ tables);
  - a C++ enumeration of all $16{,}777{,}216$ labelled 3-state tables with cutoff
    21 shifts, giving $H(3)=7{,}571{,}840$, $\Sigma(3)=6$, SC$(3)=7$ and SH$(3)=21$.
  - These programs are `Papers/verification/jones1974_verify_machines.py`
    and `jones1974_verify_counts.cpp`; both were run on 24 September 2026
    and pass. `round4_1974_checks.py` takes $H(3)$ from the C++ result.
  - Caveat: an enumeration with a cutoff certifies witnessed halts only.
    Identifying the count with $H(3)$ uses the known value SH$(3)=21$.
- **Lean** (`Lean/Diophantine/Paper1974/`, summarized in `Lean/STATUS.md`):
  - Theorem 1 (`theorem_1`), Corollary 1 (`corollary_1`), and the
    non-computability of $\Sigma$, SC and SH;
  - Example 2 (`doubler_computes`) and the printers for $x\ge1$
    (`printer_prints`);
  - $\Sigma(n)<\Sigma(n+1)$ (`sigma_lt_succ`) and (1);
  - (2) (`H_lt`, `card_machine`) and (3) by the construction of §5.2 (g)
    (`sc_lt_sigma`, `Doubling.lean`);
  - (4) (`SH_le`), $L_n\le H(n)$, $U_n<L_{n+1}$ and $H$ strictly increasing
    (`L_le_H`, `U_lt_L`, `H_strictMono`);
  - Theorem 2 (`winningII_iff`, `SH_winning`, `no_computable_winningII`,
    `no_winningI`);
  - Table 1's row $n=1$ exactly, and the lower bounds for $n=2..6$ by explicit
    kernel-checked machines (`TableBounds.lean`).
- **Not formalized:** the computability claims about $H$ (dovetailing,
  retraceability, immunity), the degrees $0'$, hyperimmunity, the growth
  statement, and the upper halves of rows $n=2,3$.

The Lean formalization found no error in the printed statements beyond those
already registered here.
