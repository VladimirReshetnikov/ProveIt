# Editorial notes: *Diophantine Representation of the Set of Prime Numbers* (1976)

James P. Jones, Daihachiro Sato, Hideo Wada and Douglas Wiens,
*The American Mathematical Monthly* **83**, no. 6 (June–July 1976), 449–464.

## 1. Scope of this document

This file accounts for every discrepancy between three objects:

- **The scan**: `original/1976/jones1976.pdf`, the 16-page JSTOR copy of the printed article
  (journal pp. 449–464). It is the authority for what the authors printed.
- **The naive OCR reading**: `original/1976/jones1976.tex`, the Mathpix transcription of the
  scan, taken as is. It contains transcription defects and faithfully copies the misprints
  in the scan.
- **The reconstruction**: `Papers/1976/jones1976_corrected.tex` and its PDF. It gives the
  intended mathematical content, with transcription defects repaired, original errors
  corrected, and editorial clarifications and proof completions added.

The edition was first produced on 13 September 2026 and has been revised continuously
since; the reconstruction was read twice in full against the scan, and the article is
formalized in Lean (§7). This document describes the current state of the source as last
revised on 24 September 2026, and it is self-contained. Individual revisions and checks are
also listed, with dates, in `Papers/EDITORIAL_NOTES.md`; entries below cite rows of that log
by their IDs (such as `76-R4-13`, in a "Log" field) where a revision date matters.

Page numbers below are those of the original printing (449–464). The reconstruction shows
them as bracketed margin numbers (§3).

## 2. Classifications

| Class | Meaning |
|---|---|
| **OCR** | Transcription defect: the scan is right, the OCR is wrong; the reconstruction follows the scan. |
| **ORIG** | Error in the printed original (mathematical error, false or unqualified claim, omission, wrong-direction label), corrected. |
| **CLAR** | Editorial clarification, stated hypothesis or proof completion; the original is not wrong, but it is incomplete or ambiguous. |
| **TYPO** | Typographical, grammatical or cross-reference slip in the original, with no mathematical content. |
| **BIB** | Bibliographic correction or completion. |
| **EDN** | Edition apparatus: notices, pagination marks, metadata. |
| **LAYOUT** | Reflow or typesetting change with no content change. |

**How CLAR changes are marked in this edition.** Only three insertions carry a label in the
text: the note after (4), headed *Original footnote, clarified* (1976-05); the paragraph
headed *Editorial clarification* before Theorem 4.2 (1976-58); and the paragraph headed
*Editorial verification note* after Theorem 5 (1976-12). Every other CLAR, ORIG, TYPO and
BIB change is built into the text without a mark. The edition notice sends the reader to
the editorial notes, and this document is the record of those changes. Readers who need
the authors' exact wording should use the scan together with the "OCR"/"Scan" fields
below.

## 3. Systematic differences (described once)

These account for most of the raw differences between the OCR file and the
reconstruction. They are not repeated in the register.

- **Rebuilt LaTeX source.** The Mathpix preamble and footnote macros
  are replaced by a standard article preamble (`amsmath`, `newtx`, `hyperref`, …). The title
  block is set in title case, with the authors in small capitals and a journal line
  (*The American Mathematical Monthly* 83, no. 6 (1976), 449–464). The OCR puts the
  introduction inside a spurious `enumerate` environment, which is removed. Plain-text
  headings (`2. Proof of Theorem 1.` …) become `\section`s, with the same numbers
  1–4. Statement heads (small capitals THEOREM/LEMMA in the scan) are set with the
  `\statement` macro in bold. Proof heads are in italics.
- **Macros.** The macros are `\dotminus` for proper subtraction $\mathbin{\dot{-}}$ (the OCR
  loses the dot; see 1976-10 and 1976-11), `\Nzero` for $\mathbb Z_{\ge0}$, `\statement`,
  and `\ednote` for the one *Editorial clarification* paragraph. Citations `[n]` become
  `\cite{refn}` and render with the same numbers.
- **Reflow and display structure.** Paragraphs and lines are reflowed,
  and the OCR's forced line breaks (`\\`, `\\[0pt]`) are removed. The scan's two-column
  condition lists (Lemma 2.5, Corollary 2.6, Lemmas 2.11 and 3.8, Theorems 2.12 and 3.9)
  and the OCR's `itemize` lists become single-column `align*` lists in numerical order.
  Delimiter sizing (`\left`/`\right`, `\bigl`), brace style (`x^{2}` for `x^2`) and similar
  markup are normalized. Proof labels "Proof of Sufficiency"/"Proof of Necessity" in §3 are
  lower-cased to "Proof of sufficiency/necessity" (LAYOUT).
- **Glyph normalization.** The scan's $\leqq$/$\geqq$ (OCR `\leqq`, `\geqq`)
  are printed as $\le$/$\ge$, and the two epsilon glyphs are unified as $\varepsilon$
  (1976-39).
- **Copyediting of compounds.** The edition hyphenates "prime representing"
  as "prime-representing" (all 11 occurrences), "integer valued" as "integer-valued", and
  "12 variable polynomial" as "12-variable polynomial". It writes "non-negative" (p. 462)
  as "nonnegative".
- **Dashes** (log: 76-R4-10). The scan uses en dashes in ranges. The OCR has
  hyphens, and the edition uses `--`: I–VIII, (1)–(14), (I)–(XXI), (XV)–(XX), (VI)–(XIII),
  (VII)–(XIII), and all bibliographic page ranges. The last OCR hyphen, in "conditions
  I-VI" in the proof of Lemma 2.11, became I–VI on 24 September 2026 (76-R4-14).
- **Numbering.** All theorem, lemma, equation and condition numbers of the scan are kept,
  including the scan's own gaps: there is no (2) in §1, and §4 runs (1)–(5), (8), (9).
  Local display numbers restart inside proofs as they do in the scan. The OCR's lost or
  merged labels are dealt with in the register (1976-25, 1976-36, 1976-38).
- **Edition apparatus (EDN).** The following have no counterpart in the scan: the header
  comments of the source; the boxed notice *About this edition*; the running heads
  "Jones–Sato–Wada–Wiens / Corrected edition"; and the PDF metadata. The header comments
  read "Continuously revised edition; last source revision 24 September 2026" and name
  `../EDITORIAL_NOTES.md` as the dated log of revisions and checks. The notice describes a
  continuously revised edition, sends the reader to this document for every discrepancy
  and its justification, says that a dated log of revisions and checks is
  `Papers/EDITORIAL_NOTES.md`, and explains the margin numbers. The journal running heads
  and page numbers, and the JSTOR download footer on every scan page, are left out.
- **Original pagination marks** (EDN). `\origpage{n}` puts a bold `[n]` in
  the margin on the line where journal page *n* begins. There are 16 marks, [449] to [464],
  accurate to the line. Most were placed by matching the first words of each scan page.
  The breaks inside displays or statements (pp. 453, 455, 457, 459, 463) were placed by
  hand from the scan. The mark for p. 463 sits at the corresponding step of the rewritten
  proof of Theorem 4.2 ("Analytic continuation gives $W=Q$ …").
- **Footnote.** The scan's single footnote (dagger, p. 450) becomes a small paragraph after
  (4); see 1976-05.
- **Figures.** The article has none.
- **Bibliography.** The OCR's `enumerate` list becomes
  `thebibliography` with the same 20 numbers. The repeated-author rules ("———") are
  expanded to names: [4] Martin Davis; [9], [10] Yuri Matijasevič; [11] Yuri Matijasevič
  (and Julia Robinson); [15], [16] Julia Robinson. "this MONTHLY" in [2], [5] and [13] is
  written as *The American Mathematical Monthly* ([3] is entry 1976-62). Page ranges get en
  dashes. The actual corrections are 1976-62 to 1976-65. The affiliations are kept as
  printed.

## 4. Discrepancy register

Entries are ordered by original page and then by position on the page. "OCR" quotes
`original/1976/jones1976.tex`, "Scan" describes the printed page when it differs from the
OCR, and "Now" is the reconstruction.

### p. 449 (Introduction, Theorem 1)

**1976-01 · Theorem 1, display (1) · OCR**
(See also §6 on the `P(a,b,…,z)=` prefix.)
OCR: four of the five display lines begin in the middle of a term. The lines read
`\left.6+1)^{3} \cdot(k+2) \cdot(n+1)^{2}+1-f^{2}\right]^{2}`,
`\left.{ }^{2} y^{4}\left(a^{2}-1\right)+1-u^{2}\right]^{2}`,
`\left.-1) l^{2}+1-m^{2}\right]^{2}` and
`\left.\left.y(a-p-1)+s\left(2 a p+2 a-p^{2}-2 p-2\right)-x\right]^{2}`.
Scan and Now: the fourteen squared residuals are complete, including
$-[16(k+1)^3(k+2)(n+1)^2+1-f^2]^2$, $-[16r^2y^4(a^2-1)+1-u^2]^2$,
$-[(a^2-1)l^2+1-m^2]^2$ and $-[q+y(a-p-1)+s(2ap+2a-p^2-2p-2)-x]^2$.
Why: the scan. As an independent check, (1) equals $(k+2)\{1-\sum_i E_i^2\}$ exactly, where
the $E_i$ are the fourteen equations of Theorem 2.12 with $k$ replaced by $k+1$. Read in
order, the residuals of (1) match equations (1, 2, 4, 3, 5, 6, 7, 8, 11, 9, 10, 12, 13, 14)
up to sign. The polynomial has total degree 25, uses all 26 variables, and has 917 nonzero
monomials when expanded. The check is a symbolic identity, and it was done twice: once
by computer algebra, and once term by term against the scan.

**1976-02 · display (1), multiplication dots · LAYOUT**
OCR and scan: $(gk+2g+k+1)\cdot(h+j)$, $16(k+1)^3\cdot(k+2)\cdot(n+1)^2$,
$e^3\cdot(e+2)(a+1)^2$ and $(\ldots-1)\cdot(n+4dy)^2$.
Now: plain juxtaposition in (1). The displays of Theorem 2.12 keep their dots.
Why: typographic only. The change was made when the source was rebuilt.

**1976-03 · pp. 449 and 450, "Theorem 1 and 2" · TYPO**
OCR and scan: "The proofs of Theorem 1 and 2 are both based …"; "Hence Theorem 1 and 2
actually imply …". Now: "Theorems 1 and 2" in both places. Why: grammar.

### p. 450 (Putnam's device, Theorem 3, formula (5))

**1976-04 · display (4) · OCR**
OCR: `(k+2)\left\{1-M\left(k, x_{1}, \cdots, x_{n}\right)\right\}^{+}`.
Scan: $(k+2)\{1-M(k,x_1,\cdots,x_n)\}.^{\dagger}$, where the dagger is a footnote mark.
Now: $(k+2)\{1-M(k,x_1,\cdots,x_n)\}$ with no superscript.
Why: the OCR's "$+$" would read as a positive part and change the construction.

**1976-05 · footnote to (4) · CLAR** (with an OCR placement defect)
Log: 76-R4-11 (typesetting of the note only).
OCR: the footnote text is displaced into the proof of Theorem 4 (p. 451 in the OCR stream):
`\footnotetext{${ }^{\dagger}$ Note the apparent paradox. The polynomial $P$ factors! However, the factors are improper, $P=P \cdot 1$.}`
Scan: the same text at the foot of p. 450.
Now: a small-type paragraph directly after (4), labelled *Original footnote, clarified.*:
"The polynomial $P$ factors. At every substitution where $P$ is positive, however, $M=0$
and the factors have values $P$ and $1$; this is not a polynomial identity asserting
$1-M\equiv1$." The dagger mark is dropped. The authors' wording (quoted above from the OCR,
which matches the scan) is **not** reproduced verbatim.
Why: $P=P\cdot1$ is true only at the substitutions where $P>0$. The factor $1-M$ is not
identically 1, so read as an identity the original remark is misleading. The
`\normalsize` is issued only after the end of the paragraph, so that the note gets
footnote-size line spacing (an earlier revision issued it too early; the fix changed no
text).

**1976-06 · "no polynomial can represent only primes" · ORIG**
OCR and scan: "the theorem that no polynomial can represent only primes."
Now: "the theorem that no nonconstant polynomial can take only prime values."
Why: a constant polynomial such as $2$ contradicts the unqualified statement. Theorem 4.1,
which the sentence announces, concludes "must be constant".

**1976-07 · "transcendental functions are necessary" · CLAR**
OCR and scan: "To overcome the inexactness of the polynomial representation, it is necessary
to use exponential functions or other transcendental functions."
Now: "… one must leave the class of polynomials and single-branch analytic algebraic
functions; a discrete zero-test provides one way to do so."
Why: the next paragraph offers proper subtraction, absolute value, remainder, signum and
integer part as alternatives to $0^x$. None of these is transcendental; they are piecewise
algebraic. The article excludes only single analytic algebraic branches (§4 and 1976-58).

**1976-08 · Theorem 3 · CLAR**
OCR and scan: "in which $M(k,x_1,\cdots,x_n)$ is a polynomial and $n\leqq 11$."
Now: "… is a nonnegative integer-valued polynomial, $n\le11$, and all variables range over
$\mathbb Z_{\ge0}$."
Why: $0^M$ is undefined for negative $M$, and the domain was left implicit. For the
11-unknown system of §3, the relation-combined $M$ is not a sum of squares, so its square
is used as the exponent. This adds no variable and gives $0^{M^2}$ with $0^0=1$. Lean:
`JSWW1976.PrimeZeroTest.theorem_3` (successful tests return $k+2$, the others return 2).

**1976-09 · "(but no algebraic function)" · CLAR**
OCR and scan: "… signum function or integer part function (but no algebraic function)."
Now: "(but no single analytic algebraic branch; see the convention before Theorem 4.2)".
Why: $|y-x|$ and $y\mathbin{\dot{-}}x=(|y-x|+y-x)/2$ are algebraic piecewise. The
impossibility result of §4 applies to a fixed analytic branch (1976-58).

**1976-10 · proper subtraction: definition and the six zero-tests · OCR**
OCR: "Define $y-x$ to be $y-x$ for $y \geqq x$ and 0 for $y<x$. Then $y-x=(|y-x|+y-x)/2$",
and `0^{x}=1-x=\frac{|1-x|+1-x}{2}=\ldots`.
Scan: the operator in "$y\mathbin{\dot{-}}x$" (twice) and in "$1\mathbin{\dot{-}}x$" is the
dotted minus. Now: $y\mathbin{\dot{-}}x$ is defined as $y-x$ for $y\ge x$ and $0$ for
$y<x$, $y\mathbin{\dot{-}}x=(|y-x|+y-x)/2$, and $0^x=1\mathbin{\dot{-}}x=\ldots$. The
right-hand sides keep ordinary subtraction.
Why: without the dot the definition is circular and the identities are false. As a check,
the six zero-tests agree for $x=0,\ldots,1000$.

**1976-11 · formula (5) for the $n$th prime · OCR**
Log: 76-R4-05.
OCR: `p_{n}=\sum_{i=0}^{n^{2}}\left(1-\left(\left(\sum_{j=0}^{i} r\left((j-1)!^{2}, j\right)\right)-n\right)\right) .`
Scan: all three minus signs are dotted.
Now: $p_n=\sum_{i=0}^{n^2}\Bigl(1\mathbin{\dot{-}}\Bigl(\Bigl(\sum_{j=0}^{i}r\bigl(((j\mathbin{\dot{-}}1)!)^2,j\bigr)\Bigr)\mathbin{\dot{-}}n\Bigr)\Bigr)$,
with the factorial grouping $((j\mathbin{\dot{-}}1)!)^2$ written out.
History: an earlier revision of this edition replaced the printed outer parentheses by
square brackets and added ", $n\ge1$", without recording either change. Both were reverted
and the printed form restored, because under the article's own convention square brackets
denote the integer part; they should not be re-proposed.
Why and checks: at $j=0$ the term is $r(((0\mathbin{\dot{-}}1)!)^2,0)=r(1,0)=1$, using
$0!=1$ and the convention $r(y,0)=y$. At $j=1$ it is $0$. For $j\ge2$ it is $1$ exactly when
$j$ is prime (Wilson). So the inner sum is $1+\pi(i)$, and the summand is $1$ exactly when
$\pi(i)<n$. The outer truncations matter: with ordinary subtraction the formula fails. The
formula agrees with a sieve for $n=1,\ldots,100$ (ending at $p_{100}=541$), and the
printed form was checked separately for $n=1,\ldots,40$.

### p. 451 (Theorems 4 and 5; §2 opening)

**1976-12 · remark after Theorem 5 · CLAR**
Log: 76-R4-12, 76-R4-13.
OCR and scan: "The number is easily calculated from the equations of Theorem 2.12."
Now: "The number is calculated from the equations of Theorem 2.12. This is an
arithmetic-operation bound for checking supplied witnesses, not a bound on their bit
lengths, on the cost of finding them, or on bit-level running time." A labelled paragraph
follows, *Editorial verification note*. It says that an explicit certificate with 40
additions and 47 multiplications exists and has been checked symbolically against Theorem
2.12 and the prime polynomial. Intermediate integers are supplied; $t=a-b$ is checked by the
one addition $t+b=a$; equality and domain checks are not counted; the candidate $N$ is
compared with the already computed $k+1$. It verifies an upper bound of 87, not optimality
and not the authors' evaluation order.
Why: a "proof of primality" here is a certificate, that is, a witness tuple for Theorem
2.12 that is checked by arithmetic. The count measures that check and nothing else. The
certificate itself is summarized in §5.2.
Pointer: the note names `Papers/verification/jones1976_primality87.md` and
`Lean/Diophantine/Paper1976/PrimalityCertificate.lean` (since 24 September 2026). §5.2 of
this document summarizes the certificate.

**1976-13 · Lucas recurrence for $\chi_a$ · OCR**
OCR: `\chi_{a}(n+2)=2 a_{\chi_{a}}(n+1)-\chi_{a}(n)`. Scan and Now:
$\chi_a(n+2)=2a\chi_a(n+1)-\chi_a(n)$.
Why: the OCR made the sequence a subscript of $a$.

**1976-14 · Lemma 2.2 · CLAR**
OCR and scan: $\psi_a(n)\equiv n\ (\mathrm{mod}\ a-1)$.
Now: "$\psi_a(n)\equiv n\pmod{a-1}$ for $a\ge2$; for $a=1$, the corresponding identity is
$\psi_1(n)=n$."
Why: at $a=1$ the modulus is 0. The recurrence gives $\psi_1(n)=n$, so the statement stays
true without relying on a modulus-zero convention. Every later use has $a\ge2$.

**1976-15 · Lemma 2.3, "satisfy 2.3" · TYPO**
Log: 76-R4-09.
OCR and scan: "it is possible to satisfy 2.3 with $n$ such that $t\mid n+1$".
Now: "satisfy (2.3)". Why: the condition is tagged (2.3) and cited that way everywhere else.

### p. 452 (Lemmas 2.3–2.8)

**1976-16 · Lemma 2.3, proof of the converse · CLAR**
OCR and scan: "The converse follows easily from the following well-known fact about Pell
equations: When $A\neq\square$, the Pell equation $Ay^2+1=x^2$ always has nontrivial
solutions, (cf. [11] §2)."
Now: put $D=e(e+2)$, which is positive and not a square because $e^2<D<(e+1)^2$. The Pell
equation $D(et)^2v^2+1=X^2$ has a nontrivial solution, and $n+1=tv$ gives (2.3) with
$t\mid n+1$, since $e^3(e+2)(tv)^2=D(et)^2v^2$. Powers of a solution give arbitrarily large
$n$ (cf. [11] §2).
Why: the fact quoted in the original does not by itself give the divisibility
$t\mid n+1$. Applying it to the coefficient $D(et)^2$ does. Lean:
`JSWW1976.lemma_2_3_converse`.

**1976-17 · Lemma 2.4, the zero modulus · CLAR**
Now adds: "When $(a,p)=(1,1)$, the modulus is zero and the assertion is understood as the
exact equality $\chi_1(n)=1$. In all other cases the modulus is nonzero."
Why: $2ap-p^2-1=(a^2-1)-(a-p)^2$ vanishes for integers $a\ge1$, $p\ge0$ only when
$a^2-1$ is a square, that is $a=1$, and then $p=1$. In that case both sides equal 1. No
construction uses a zero modulus. The lemma was checked for $1\le a\le10$, $0\le p\le15$,
$0\le n\le12$, and again, independently, on a smaller range. Lean:
`Diophantine.χ_modEq_pow` and `pow_add_ψ_le_χ`.

**1976-18 · wording of hypotheses (pp. 452 and 456) · LAYOUT**
OCR and scan: Lemma 2.5 and Corollary 2.6 read "For any numbers $a,n$ and $y$, $(1\leqq n)$
and $(2\leqq a)$, in order that …". Lemma 3.2 reads "For $0<n<M$ and $0\leqq x$,
$(1-\frac nM)<\ldots$". Lemmas 3.5 and 3.6 end with "(for $a\geqq1$)".
Now: "For numbers $a,n,y$ with $n\ge1$ and $a\ge2$, in order that …"; "For $0<n<M$ and
$x\ge0$, $1-\frac nM<\ldots$"; "For $a\ge1$, …" at the start. Why: readability; the content
is the same.

**1976-19 · Lemma 2.5, which direction differs from Davis · ORIG**
OCR and scan: "In this connection the proof of sufficiency is slightly different from that
given in [3]. We need not use the Chinese Remainder Theorem."
Now: "In the direction that constructs the witnesses, the proof is slightly different from
that given in [3]: equation V supplies $b$ directly, so the Chinese Remainder Theorem is
unnecessary."
Why: the lemma says "it is necessary and sufficient that there exist numbers". Davis uses
the Chinese Remainder Theorem to *construct* witnesses, which is the necessity direction
here. Equation V defines $b$ explicitly. The printed label names the wrong direction.

**1976-20 · Lemma 2.7 · CLAR**
OCR and scan: "If $0\leqq\alpha<1/q$, then $1-q\alpha\leqq(1-\alpha)^q$."
Now: "If $q\ge1$ is an integer and $0\le\alpha<1/q$, …".
Why: $1/q$ must be defined, and Bernoulli's inequality is used with integer exponents.

**1976-21 · missing sentence periods (pp. 452, 454) · TYPO**
Scan: "LEMMA 2.8 If $0\leqq\alpha\leqq\frac12$ …" has no period after the label. In the
proof of Lemma 2.11, "Suppose $1\leqq k$ and $f=k$! By Lemma 2.3 …" has no full stop after
the factorial sign (OCR: `f=k$ !`).
Now: "Lemma 2.8." and "$f=k!$." Why: punctuation only.

### p. 453 (Lemma 2.10)

**1976-22 · stray period · TYPO**
OCR and scan: "Proof. Using the Binomial Theorem we have ." Now: "… we have".

**1976-23 · derivation of (iv), first comparison · ORIG**
OCR and scan: $\frac{(n+1)^k}{\binom nk}<\frac{k!}{(n+1-k)^k/(n+1)^k}$.
Now: the first "$<$" is "$\le$".
Why: $\binom nk\ge(n+1-k)^k/k!$, with equality at $k=1$, where both sides are $(n+1)/n$.
For example, $n=2$, $k=1$ gives $3/2=3/2$. The next comparison in the chain is still strict,
so (iv) and the lemma are unaffected.

### p. 454 (Lemma 2.11, Theorem 2.12)

**1976-24 · Lemma 2.11, sufficiency · CLAR**
Now adds before "By II and VI": "By III and Lemma 2.3, $(2k)^k\le n$; by IV, $n^k<p$. Thus
Lemma 2.10 applies."
Why: the proof uses Lemma 2.10 without checking its hypotheses. Lemma 2.3 with $e=2k$ gives
$n\ge 2k-1+(2k)^{2k-2}\ge(2k)^k$, including at $k=1$, and $p=(n+1)^k>n^k$.

**1976-25 · labels (1′)–(4′) · OCR**
OCR: `2 \leqq n, \quad \text { and also }\left(2^{\prime}\right) \quad k<n . \tag{$\prime$}`
(label (1′) lost), and `… \leqq a, \quad \text { and also (4') } \quad n<a \text {. } \tag{3'}`.
Scan: "(1′) $2\leqq n$, and also (2′) $k<n$." and "(3′) … $\leqq a$, and also (4′) $n<a$."
Now: one display "$2\le n,\ k<n$" tagged (1′,2′), then (3′) and, after "Also,", (4′)
$n<a$ in its own display. Why: all four labels are cited later.

**1976-26 · spacing in "$p<a,\ (n+1)^k<a$" · LAYOUT**
Log: 76-R4-08, where the change is recorded as TYPO; since the scan has the space, it is
classified here as LAYOUT. The OCR lost the space, which the scan has. The edition restores
it, as in the two sibling displays.

### p. 455 (Theorem 2.12, continued; Lemma 3.1)

**1976-27 · "$p\neq0$" in the modulus comparison · CLAR**
OCR and scan: "From (1′), (2′), (3′) and the fact that $p\neq0$ (which follows from (5′)),
it follows that $z<a$, $p^{k+1}<a$ and $a<2ap-p^2-1$."
Now: "… the fact that $p\ge3$ (which follows from (5′)) …".
Why: $p\neq0$ alone does not give $a<2ap-p^2-1$ (at $p=1$ this needs $a>2$). What (5′)
actually gives is $p=(n+1)^k\ge3$, because $n\ge2$ and $k\ge1$. Then
$a(2p-1)-p^2-1>p(2p-1)-p^2-1=p^2-p-1>0$, using $a>p$.

**1976-28 · necessity of Theorem 2.12, missing witness $z$ · ORIG**
OCR and scan: "According to Lemma 2.11 numbers $f,h,j,n,p,q$ and $w$ may be chosen …".
Now: "… $f,h,j,n,p,q,w$ and $z$ …". Why: equations (1), (2) and (8′) involve $z$, and $z$
is one of the witnesses of Lemma 2.11.

**1976-29 · Lemma 3.1 · CLAR**
OCR and scan: "For $0<2q<\beta$, $\left(\frac\beta{\beta-1}\right)^q\leqq1+\frac{2q}\beta$."
Now: "For an integer $q\ge1$ and real $\beta>2q$, …". Why: the proof uses Lemmas 2.7 and 2.8,
which need an integer exponent.

### p. 456 (Lemmas 3.2–3.8, Theorem 3.9)

**1976-30 · Lemma 3.4 · CLAR**
Now begins "For $k\ge1$," so that $k!$, $\binom nk$ and the estimate are in their intended
range.

**1976-31 · Lemma 3.8, order of (A1)–(A7) · OCR**
OCR: `(A1) … (A5) … (A2) … (A6) … (A3) … (A7) … (A4)`, which interleaves the scan's two
columns. Scan and Now: (A1)–(A7) in order. No condition is lost or changed.

**1976-32 · Lemma 3.8, auxiliary parameter and quantification · CLAR**
OCR: `Then $\psi_{\mathbf{A}}(B)=C$ if and only if the following system of conditions can be satisfied.`
and `(A3) $E=2(i+1) D(k+1) C^{2}$`. Scan: $\psi_A(B)$ (the bold A is OCR noise), and
(A3) with $(k+1)$.
Now: "For any fixed auxiliary parameter $\kappa\ge0$, $\psi_A(B)=C$ if and only if the
following system can be satisfied in nonnegative integers $i,j,D,E,F,G,H,I$." (A3) reads
$E=2(i+1)D(\kappa+1)C^2$.
Why: the $k$ in (A3) is a free parameter of the Matijasevič–Robinson lemma. It has nothing
to do with the primality parameter $k$ of Theorem 3.9, where it is set to 0 (compare (IX)
with (A3)). Renaming it and quantifying the unknowns removes the clash. Lean:
`JSWW1976.lemma_3_8` (both directions, `MR.lean`).

**1976-33 · Theorem 3.9, statement · CLAR**
OCR and scan: "… the following system of equations has a solution in nonnegative integers:"
Now: "… the following system of conditions has a solution in nonnegative integers (the
rational expression in (XIV) must be defined):".
Why: the system contains square predicates, a divisibility and a strict rational inequality,
not only equations. The denominators in (XIV) must be nonzero; otherwise spurious
solutions can appear. For example, under the convention $x/0=0$, (XIV) would read
$(S+1)^2<\frac14$. Lean states these as explicit side conditions (`Sys39`).

### p. 457 (proof of Theorem 3.9, sufficiency)

**1976-34 · display (1) · ORIG** (also an OCR defect)
OCR: `\beta-k!\left\lvert\,<\frac{1}{2} .\right.`. Scan: "$\beta-k!|<\frac12$". The opening
absolute-value bar is missing in the print.
Now: $|\beta-k!|<\frac12$. Why: the argument proves, and (22) restates, the two-sided bound.

**1976-35 · "Lemma 3.7" (pp. 457 and 461) · TYPO**
Log: 76-R4-01 and 76-R4-07.
OCR and scan: "From (I) we have, by Lemmas 2.3 and 3.7," (p. 457) and "The only assumptions
used … were Lemmas 2.7, 2.8, 3.1-3.7, equations (I)-(XIII)" (p. 461).
Now: "by Lemma 2.3 and Definition 3.7" and "Lemmas 2.7, 2.8, 3.1–3.6, Definition 3.7,
equations (I)–(XIII)". Why: 3.7 is the definition of $U(x,y)$, not a lemma.

**1976-36 · merged labels (4)/(5) (p. 457) and (iii)/(iv) (p. 461) · LAYOUT**
OCR: `M \geqq 32 n x, \quad \text { and } \quad \text { (5) } \quad M>2 n, M>160 \cdot 10^{10} . \tag{4}`
and `0<\sigma-(w+1) x \quad \text { and } \quad \text { (iv) } \sigma-(w+1) x<x . \tag{iii}`.
Scan: "(4) $M\geqq32nx$, and (5) $M>2n$, $M>160\cdot10^{10}$." and "(iii) … and (iv) …".
Now: separate displays (4) and (5), joined by "In particular," instead of "and", and
separate displays (iii) and (iv). No content change. The bound (5) follows from (4),
because $n\ge5$ and $x>(2n)^{2n}>10^{10}$.

**1976-37 · Lemma 3.8 applied "with $\kappa=0$" (pp. 457 and 461) · CLAR**
OCR and scan: "So by Lemma 3.8, (VII)–(XIII) imply that" and "Then (VI)–(XIII) may be
satisfied by Lemma 3.8."
Now: both read "by Lemma 3.8 with $\kappa=0$". Why: (IX) is (A3) with $\kappa=0$ (1976-32).

### p. 458

**1976-38 · display (10) · OCR**
OCR: `Thus $p^{\prime}=l^{\prime}=0, K=\psi_{M}(n-k+1) \quad$ and $\quad L=\psi_{M x}(k+1)$.` with
no tag. Scan: the line is display (10).
Now: "Thus" followed by a display tagged (10): $p'=l'=0,\ K=\psi_M(n-k+1),\ L=\psi_{Mx}(k+1)$.
Why: (10) is cited in Case 2, before (19), and in the lower bound for $\beta$.

**1976-39 · Case 1, $\epsilon_1$ · OCR**
OCR: `\epsilon_{1}` at its first occurrence and `\varepsilon_{1}` afterwards. Now: $\varepsilon_1$ throughout.

**1976-40 · justifications of (12) and (13) · LAYOUT**
OCR and scan: (12) ends "…$\pm\varepsilon_1+\varepsilon_2$, where $0<\varepsilon_2<\frac18$,
by Lemma 3.3. And" and (13) ends "(mod $x$), by Lemma 3.3."
Now: (12) contains "$0<\varepsilon_2<\frac18$" inside the display, (13) is bare, and the
text continues "Here both statements follow from Lemma 3.3." The content is the same;
the prose is moved out of the displays.

### p. 459

**1976-41 · (18), "by (17)" · OCR**
OCR: `… <2, \text { by } \tag{18}`. Scan and Now: "… $<2$, by (17)."

**1976-42 · Case 2, "using (18), (16) and (10)" · OCR**
Log: 76-R4-06. OCR: `using (18) (16) and (10)`. The scan has the comma after
(18), and the edition restores it.

### p. 460

**1976-43 · estimate (20)(i) · ORIG**
OCR and scan: "(since $10k!k!2\varepsilon<5(k!)^2\leqq5k^{2k}\leqq n<n(n-1)\cdots(n-k+1)$)".
Now: "… $\le n\le n(n-1)\cdots(n-k+1)$". Why: at $k=1$ the falling factorial equals $n$
(the boundary case is $5=5$). The earlier strict inequality keeps (i) strict.

**1976-44 · after (i)–(iv): the case $k=1$ and the assumptions used · ORIG**
OCR and scan: "(These inequalities are derived using only (2) and (3).) Thus (20) holds"
(no final period).
Now: "For $k=1$, estimate (iv) is immediate because its numerator is zero. The estimates use
(2)–(4) and $0\le\varepsilon<1/4$ from (19). Thus (20) holds."
Why: the parenthetical in (iv) assumes $k\ge2$, so $k=1$ was not covered. The dependency
claim is also wrong: (ii) and (iii) need (4) ($Mx>10n$), and (i) needs $\varepsilon<\frac14$
from (19).

**1976-45 · lower bound for $\beta$, the reciprocal factor · OCR**
OCR: `\left(1+\frac{\varepsilon}{\binom{n}{k}^{-1}} \geqq \frac{n^{k}}{\binom{n}{k}}\ldots\right.`, which
attaches the exponent $-1$ to the binomial coefficient and breaks the chain.
Scan and Now: $\frac{n^k}{\binom nk}\bigl(1-\frac1{2Mnx}\bigr)^k\bigl(1+\frac{\varepsilon}{\binom nk}\bigr)^{-1}\ge\frac{n^k}{\binom nk}\bigl(1-\frac1{2Mnx}\bigr)^k\bigl(1-\frac{\varepsilon}{\binom nk}\bigr)$.
The edition sets the chain on separate lines.

**1976-46 · justification of the lower bound · CLAR**
OCR and scan: "… by Lemmas 2.7 and 2.8."
Now: "by Lemma 2.7 and the elementary inequality $(1+t)^{-1}\ge1-t$ for $t\ge0$."
Why: Lemma 2.8 is the upper bound $(1-\alpha)^{-1}\le1+2\alpha$. The step needs
$(1+t)^{-1}\ge1-t$, and Lemma 2.7 supplies $(1-\frac1{2Mnx})^k\ge1-\frac k{2Mnx}$.

**1976-47 · (21)(ii), notation · LAYOUT**
OCR and scan: an `itemize` item "(ii) … (since $4\varepsilon k!k!(n-k)!<k!k!(n-k)!\leqq k^{2k}(n-k)!\leqq n(n-k)!\leqq n!$)".
Now: display (ii), then "since $4\varepsilon(k!)^2(n-k)!<(k!)^2(n-k)!\le k^{2k}(n-k)!\le n(n-k)!\le n!$."
Why: $k!k!=(k!)^2$, so the content is the same (the notation of (20)(i) is left as printed).

### p. 461 (necessity, (23), elimination)

**1976-48 · what (XIV) was used for · ORIG**
OCR and scan: "The condition (XIV) was used only to show (i)."
Now: "In the sufficiency proof, (XIV) was used to force (i) and the needed positivity and
case selection. In the present construction these properties will instead be established
directly."
Why: the sufficiency proof also uses (XIV) to get $\beta>\frac12$, hence
$\sigma-(w+1)x>0$, and to exclude Case 2 and $r'>0$. The necessity argument is valid
because (iii) and (iv) are then derived independently.

**1976-49 · display (23), the omitted $+1$ · ORIG**
OCR and scan: $M=16nx(w+2)=16n\bigl(\bigl[\frac{(x+1)^n}{x^k}\bigr]-\binom nk+x\bigr)>\ldots$
Now: $M=16nx(w+2)+1=16n\bigl(\bigl[\frac{(x+1)^n}{x^k}\bigr]-\binom nk+x\bigr)+1>16n\bigl(\frac{(x+1)^n}{x^k}-\frac18-\binom nk+x\bigr)>16n\frac{(x+1)^n}{x^k}$.
Why: (III) defines $M=16nx(w+2)+1$. The definition of $w$ gives
$x(w+2)=[(x+1)^n/x^k]-\binom nk+x$. The strict bounds that follow still hold.

**1976-50 · "eliminate from" · TYPO**
OCR and scan: "The unknowns $M,A,\ldots,S$ eliminate from (I)–(XXI) by substitution."
Now: "… can be eliminated from …".

**1976-51 · clearing the denominators of (XIV) · CLAR**
Now adds, after "one inequality": put $\mathcal D=(C-(w+1)xKL)(C-R)^2$ and
$\mathcal N=RKC^2$. With the other conditions in force, (XIV) is equivalent to
$4(\mathcal N-(S+1)\mathcal D)^2<\mathcal D^2$. This strict inequality itself excludes
$\mathcal D=0$, and $C,K,L,R>0$. $\mathcal D$ and $\mathcal N$ are abbreviations, not
unknowns.
Why: $\beta=\mathcal N/\mathcal D$, and relation combining needs a polynomial condition. A
naive clearing of denominators could admit the undefined cases. The count of ten unknowns
is unchanged. The identities were checked by computer algebra (§7). Lean: `JSWW1976.beta_defined_iff_margin`
and `theorem_3_9_reduced` (`Theorem39Elimination.lean`).

### p. 462 (end of §3, start of §4)

**1976-52 · status of (24) · CLAR**
OCR and scan: "our first two square conditions, (I) and (II), may be combined into one square
condition".
Now: "may, for the purpose of the construction, be replaced by the single square
condition". Why: (24) is not pointwise equivalent to (I)∧(II). It supplies the same growth,
and that is all the proof uses.

**1976-53 · (24): coprimality and growth · CLAR**
OCR and scan: "Observe that the first factor of (24) is prime to the second. This gives a
polynomial $M_5$ …".
Now: "relatively prime", followed by a proof. With $T=U(2k,n)$ the second factor is
$16T(T-1)(n+1)^2(x+1)^2+1\equiv1\pmod T$, so both factors are squares. The first gives the
bound on $n$. For the second, write $2(n+1)(x+1)=\psi_{2T-1}(j)$. Lemma 2.2 gives
$2(n+1)\mid j$ because $2(n+1)\mid2(T-1)$. Then $j\ge2(n+1)$, and Lemma 2.1 gives
$2(n+1)(x+1)\ge(4T-3)^{2n+1}$, which is far more than $x>(2n)^{2n}$. Conversely, Pell
solutions whose second coordinate is divisible by $2(n+1)$ give arbitrarily large
admissible $x$. So the proof of Theorem 3.9 still applies, and pointwise
$U(2n,x)=\square$ is not needed.
Why: the original gives no reason why replacing (II) keeps the proof valid. Lean:
`fiveSquareRadicand_growth` and `theorem_3_9_five_square` (`FiveSquareGrowth.lean`,
`FiveSquareCriterion.lean`).

**1976-54 · "Matijasević" · TYPO**
Scan (and OCR): "(Recently Yuri Matijasević has announced …)", printed with an acute ć.
Everywhere else the article prints č. Now: "Matijasevič".

**1976-55 · "is of course." · TYPO**
Scan (and OCR): "The oldest result of this type is of course." This sentence is cut short
and is followed directly by Theorem 4.1.
Now: "The oldest result of this type is the following."

**1976-56 · Theorem 4.1, the multiplier $l$ · CLAR**
OCR and scan: "Let $l$ be any multiple of the denominators of these coefficients of $P$."
Now: "Let $l$ be a positive common multiple of the denominators of the coefficients of $P$."
Why: $0$ is also "a multiple". With $l=0$ the points $1+n_ilp$ collapse to one point,
and the argument needs an infinite (Zariski-dense) grid.

**1976-57 · Theorem 4.1, sign of the $n_i$ · ORIG**
OCR and scan: "if $n_1,n_2,\cdots,n_k$ are integers". Now: "are nonnegative integers".
Why: the hypothesis is about nonnegative arguments only, and a negative $n_i$ can make
$1+n_ilp$ negative. Lean (`theorem_4_1`) uses the origin as base point instead of
$(1,\ldots,1)$ and cancels $l$ in the integers. That is a change of proof only; the text
needs no further change.

**1976-58 · Theorem 4.2: statement, hypothesis and proof (pp. 462–463) · ORIG** (with OCR defects)
(The *Editorial clarification* paragraph before Theorem 4.2 belongs to this entry.)
OCR and scan, statement: "An integer valued algebraic function $W(z_1,z_2,\cdots,z_k)$ is a
polynomial." Proof (condensed): a Puiseux expansion at infinity is "the Laurent series
expansion of $W=W(t^{-1/h})$, where $h$ is the order of the branch point at infinity and
$t=1/z$ is the local parameter"; (1) $W(z)=\sum a_lz^{\alpha-l\delta}$; (2)
$\Delta^rW(n)=\int_0^1\cdots\int_0^1W^{(r)}(n+x_1+\cdots+x_r)\,dx_1\cdots dx_r$; "Since
$\delta$ is positive, $W^{(r)}(z)\to0$ … for all sufficiently large $r$"; so $\Delta^rW(n)=0$
for large $n$; "since a nonzero algebraic function cannot have infinitely many zeroes, …
$\Delta^rW(z)=0$. This implies that $W(z)$ is a polynomial". For several variables: a
polynomial $P(z_i)$ "whose degree is independent of the $n_i$'s" bounds $|W|$ on slices,
giving (4) $\partial^{d_i}W/\partial z_i^{d_i}=0$ on slices, and hence (5) everywhere.
"Now an algebraic function has at most a finite number of branch points. Hence infinitely
many $k$-tuples are not branch points …", followed by a Taylor series and "degree
$\leqq d_1+d_2+\cdots+d_k$".
OCR defects: `\Delta^{\prime} W(n)` for $\Delta^rW(n)$ in (2) and `\Delta^{\prime} W(z)=0` later;
`\partial^{d} W` and `\partial z_{i^{i}}^{d_{i}}` for $\partial^{d_i}W/\partial z_i^{d_i}$ in (4).
Now: a paragraph headed *Editorial clarification* comes first. In Theorem 4.2 and
Corollary 4.3, an algebraic function means a fixed analytic branch on a connected complex
neighborhood of the nonnegative real orthant, not values chosen by switching branches;
$|z-1|$ is not such a branch across $z=1$. The statement reads: "An algebraic function
$W(z_1,\ldots,z_k)$, analytic on a connected complex neighborhood of $[0,\infty)^k$ and
integer-valued on $\mathbb Z_{\ge0}^k$, is a polynomial." The proof is rewritten:
the local coordinate is $t=z^{-1/h}$, so $z=t^{-h}$; a fixed $r>\max(\alpha,0)$ is chosen and
termwise differentiation gives $W^{(r)}\to0$; the integer values of $\Delta^rW(n)$ vanish
for large $n$; Newton interpolation gives a polynomial $Q$ of degree $<r$ with $Q(n)=W(n)$
eventually; $W-Q$ is algebraic with infinitely many zeros, so it vanishes, and analytic
continuation finishes the case $k=1$. For several variables, the slice degrees are bounded
uniformly by the degree of a polynomial relation for $W$ (a degenerate specialization is
handled by a first nonzero transverse coefficient). $\partial^{d_i}W/\partial z_i^{d_i}$
is algebraic, and if it were nonzero, a defining polynomial with nonzero constant
coefficient would vanish on $\mathbb Z_{\ge0}^k$, which is impossible. So (5) holds, the
Taylor series at an ordinary point terminates, and the total degree is at most
$\sum_i(d_i-1)$.
Why: (a) calling $t=1/z$ the local parameter while substituting $t^{-1/h}$ is inconsistent.
(b) "$W^{(r)}\to0$ for all large $r$" needs $r>\alpha$. (c) Even $\Delta^rW\equiv0$ does not
by itself make an analytic function a polynomial: $z+\sin2\pi z$ has $\Delta^2\equiv0$.
Algebraicity has to be used, and the rewritten proof does so through Newton interpolation
and the zeros of $W-Q$. (d) The claim that an algebraic
function of several variables has finitely many branch points is false: $w^2=z_1$ branches
along the whole hyperplane $z_1=0$. (e) Without a fixed analytic branch the statement is
ambiguous: piecewise choices of roots, such as $|z-1|=\sqrt{(z-1)^2}$, are integer-valued
without being polynomials. The rewritten proof was read step by step and no gap was found.
Theorem 4.2 has not been formalized in Lean.

### p. 463 (Corollary 4.3, Theorem 4.4)

**1976-59 · Corollary 4.3 · CLAR**
OCR and scan: "An algebraic function $W(z_1,z_2,\cdots,z_k)$, which takes only prime values at
nonnegative integers, is constant."
Now: "… satisfying the analytic-branch hypothesis of Theorem 4.2, and taking only prime
values at nonnegative integer arguments, is constant." Why: the convention of 1976-58.

**1976-60 · Theorem 4.4, reduction to one variable · CLAR**
OCR and scan: "It suffices to prove the theorem for the case of a function of a single
variable. (For if $F(x_1,\cdots,x_n)$ is constant in each variable separately, then
$F(x_1,\cdots,x_n)$ is constant.) Hence we may suppose $n=1$."
Now: "First consider the case $n=1$. The passage to several variables is justified below."
The end of the proof adds: applying the one-variable result on every integer coordinate line
gives one constant on the grid $\mathbb Z_{\ge0}^n$, and the dominant-term argument (which
also works with real polynomial coefficients) extends this equality along the first real
coordinate, then the second, and so on.
Why: the prime-value hypothesis is available only at integer points. So "constant in each
variable separately" has to be established first on the grid and then extended to real
arguments.

**1976-61 · Theorem 4.4, why (9) holds identically · CLAR**
OCR and scan: "It is not difficult to show that equation (9) must then hold identically. This
completes the proof of the Theorem."
Now: write $F(x)-p=\sum_jA_j(x)e^{B_j(x)}$ with real polynomials $A_j,B_j$, grouping
exponents that differ by constants. If the sum is not identically zero, the term with the
eventually largest $B_j$ dominates, and its coefficient has an eventually fixed sign, so
$F-p$ has no arbitrarily large real zeros. This contradicts (9). "This completes the proof."
Why: the general principle suggested ("infinitely many zeros implies identically zero") is
false for entire functions ($\sin\pi x$). The argument has to use the special form
$\sum P_ia_i^{Q_i}$. Lean: `JSWW1976.theorem_4_4`, `theorem_4_4_real`
(`ExpPrimeConstant.lean`).

### p. 464 (References)

**1976-62 · [3] · TYPO**
OCR and scan: "this' MONTHLY, 80 (1973) 233–269". Now: "The American Mathematical
Monthly, 80 (1973) 233–269".

**1976-63 · [7], missing pages · BIB**
OCR and scan: "Canadian Math. Bull., 18 (1975) no. 3." Now: "… 18 (1975), no. 3, 433–434."
Why: the publisher's record for DOI 10.4153/CMB-1975-081-7. The pages are added, not
corrected.

**1976-64 · [8], last page of the English translation · BIB**
Log: 76-R4-02.
OCR and scan: "English translation: Soviet Math., Doklady, 11 (1970) 354-358." Now: "354–357".
Why: the *Journal of Symbolic Logic* Reviews entry for the paper records "Soviet
mathematics, vol. 11 no. 2 (1970), pp. 354–357", with errata in vol. 11 no. 6, p. vi.
Matiyasevich's publication list and the 1974, 1982 and 1984 articles of this corpus agree.
The 1976, 1978 and 1980 originals print 358. The editions of all three now print 357, so
the reference is consistent across the corpus. (An earlier revision of this edition kept
358 while the 1978 and 1980 editions already had 357; that inconsistency is resolved.)

**1976-65 · [16], editor's name · BIB**
OCR and scan: "W.J. Leveque". Now: "W. J. LeVeque" (the editor's usual spelling).

## 5. Editorial additions

### 5.1 Index

The reconstruction adds the following to the original. Each item is explained in the
entry cited.

- **Stated hypotheses and domains:** Theorem 3 (1976-08); Lemma 2.2 at $a=1$ (1976-14); the
  zero modulus in Lemma 2.4 (1976-17); Lemmas 2.7, 3.1, 3.4 (1976-20, 1976-29, 1976-30);
  Lemma 3.8's parameter $\kappa$ and unknowns (1976-32); definedness in Theorem 3.9
  (1976-33); the analytic-branch hypothesis of Theorem 4.2 and Corollary 4.3 (1976-58,
  1976-59).
- **Proof completions:** the converse of Lemma 2.3 (1976-16); the hypotheses of Lemma 2.10
  in Lemma 2.11 (1976-24); $p\ge3$ (1976-27); the case $k=1$ of (20) (1976-44); the
  reciprocal inequality (1976-46); denominator clearing (1976-51); coprimality and growth
  for (24) (1976-53); the proof of Theorem 4.2 (1976-58); the several-variable passage and
  the identity step in Theorem 4.4 (1976-60, 1976-61).
- **Clarifications of wording:** the footnote to (4) (1976-05); "transcendental" (1976-07);
  "no algebraic function" (1976-09); the certificate reading of Theorem 5 (1976-12); the
  status of (24) (1976-52); the multiplier $l$ (1976-56).
- **Labelled editorial text in the article:** *Original footnote, clarified* (1976-05),
  *Editorial verification note* (1976-12, §5.2), and *Editorial clarification* before
  Theorem 4.2 (1976-58).

### 5.2 The 87-operation claim of Theorem 5

**What the article claims.** "If $p$ is a prime number, then there is a proof that $p$ is
prime consisting of only 87 additions and multiplications", and the number "is easily
calculated from the equations of Theorem 2.12" (p. 451). The edition reconstructs the figure
as an explicit certificate, which is summarized below and proved correct in Lean.

**Counting convention.** The inputs are the 26 letters $a,\ldots,z$ (nonnegative)
with $k\ge1$ and candidate $N=k+1$. The certificate supplies $k$ and every intermediate
integer; intermediates may be negative. An addition, or a multiplication (a squaring or a
multiplication by a numeral included), checks one assignment and counts as one operation.
A subtraction assignment $t=a-b$ is checked by the single addition $t+b=a$. Neither $-b$
nor a free negation is computed, so only addition and multiplication are used. Equality
tests, domain tests, numerals and reading the certificate are not counted. The candidate is
checked by the equality $N=\mathtt{kp1}$ with the already computed $\mathtt{kp1}=k+1$, so
recovering $k$ costs nothing. Each checked assignment has a unique integer solution. By
induction along the acyclic schedule, every intermediate therefore has its intended value,
and the final comparisons enforce exactly the fourteen equations of Theorem 2.12.

**The identities that make 87 reachable:**
$16k^3(k+1)(n+1)^2=k(k+1)[4k(n+1)]^2$, $e^3(e+2)(a+1)^2=e(e+2)[e(a+1)]^2$,
$16(a^2-1)r^2y^4=(a^2-1)[4ry^2]^2$, and $2av-v^2-1=(a^2-1)-(a-v)^2$ for $v=n+1$, $p+1$,
$p$. The last identity lets equations (12)–(14) reuse $A=a^2-1$ and the differences
$a-n-1$, $a-p-1$ and $a-p$, which are needed anyway.

**Schedule by equation block of Theorem 2.12** (new operations per block, in order):

| Eq. | Ops | Intermediates computed (names as in the certificate) |
|---:|---:|---|
| (1) | 3 | `hj=h+j`, `wz=w*z`, `rhs1=wz+hj` |
| (2) | 5 | `gk=g*k`, `gkg=gk+g`, `gkgk=gkg+k`, `zprod=gkgk*hj`, `rhs2=zprod+h` |
| (3) | 9 | `kp1=k+1`, `np1=n+1`, `fourk=4*k`, `fourkn=fourk*np1`, `fourkn2=fourkn^2`, `kkp1=k*kp1`, `fprod=kkp1*fourkn2`, `rhs3=fprod+1`, `lhs3=f*f` |
| (4) | 4 | `twon=2*n`, `pq=p+q`, `pqz=pq+z`, `rhs4=pqz+twon` |
| (5) | 8 | `ap1=a+1`, `ep2=e+2`, `eap1=e*ap1`, `eap12=eap1^2`, `eep2=e*ep2`, `oprod=eep2*eap12`, `rhs5=oprod+1`, `lhs5=o*o` |
| (6) | 6 | `a2=a*a`, `A=a2-1`, `y2=y*y`, `xprod=A*y2`, `rhs6=xprod+1`, `lhs6=x*x` |
| (7) | 6 | `ry2=r*y2`, `fourry2=4*ry2`, `fourry22=fourry2^2`, `uprod=A*fourry22`, `rhs7=uprod+1`, `u2=u*u` |
| (8) | 14 | `cu=c*u`, `xcu=x+cu`, `lhs8=xcu^2`, `u2a=u2-a`, `u2u2a=u2*u2a`, `G=a+u2u2a`, `G2=G*G`, `G2m1=G2-1`, `dy=d*y`, `fourdy=4*dy`, `nfourdy=n+fourdy`, `nfourdy2=nfourdy^2`, `gprod=G2m1*nfourdy2`, `rhs8=gprod+1` |
| (9) | 4 | `l2=l*l`, `mprod=A*l2`, `rhs9=mprod+1`, `lhs9=m*m` |
| (10) | 3 | `am1=a-1`, `iam1=i*am1`, `rhs10=k+iam1` |
| (11) | 2 | `nl=n+l`, `rhs11=nl+v` |
| (12) | 7 | `an=a-np1`, `an2=an^2`, `Dn=A-an2`, `bDn=b*Dn`, `lan=l*an`, `pla=p+lan`, `rhs12=pla+bDn` |
| (13) | 8 | `ap=a-p`, `app=ap-1`, `app2=app^2`, `Dpp=A-app2`, `sDpp=s*Dpp`, `yapp=y*app`, `qyapp=q+yapp`, `rhs13=qyapp+sDpp` |
| (14) | 8 | `ap2=ap^2`, `Dp=A-ap2`, `tDp=t*Dp`, `pl=p*l`, `plap=pl*ap`, `zplap=z+plap`, `rhs14=zplap+tDp`, `lhs14=p*m` |

The total is 87. Written as a straight-line program this is 30 additions, 10 subtractions
and 47 multiplications. Under the certificate convention it is **40 additions and 47
multiplications**. The final equality tests are `q=rhs1`, `z=rhs2`, `lhs3=rhs3`, `e=rhs4`,
`lhs5=rhs5`, `lhs6=rhs6`, `u2=rhs7`, `lhs8=rhs8`, `lhs9=rhs9`, `l=rhs10`, `y=rhs11`,
`m=rhs12`, `x=rhs13`, `lhs14=rhs14` and `N=kp1`. The counts are shared across blocks, so a
block's figure is not the cost of that equation alone. The complete instruction list, with
operands, is in `Lean/Diophantine/Paper1976/PrimalityCertificate.lean` (`schedule`).

**Checks.** A program (`jones1976_verify_87_operations.py`, §7) reads the fourteen
equations directly from the TeX source.
It confirms that each circuit residual equals the source residual exactly. The signs are
$(1,1,-1,1,-1,1,1,1,1,1,-1,1,1,1)$; equations (3), (5) and (11) are printed with the
computed side on the right. It also matches the circuit with the degree-25 polynomial (1)
after $k\mapsto k+1$, in the residual order of 1976-01. Lean proves that a valid
certificate exists if and only if the candidate is prime, including the prime 2, and that
the counts are 40 and 47 (`JSWW1976.theorem_5`, `PrimalityCertificate.prime_iff_certificate`,
`check_counts`). All 87 instructions and 14 comparisons of the Lean schedule match the data
generated by the program (`jones1976_primality87.json`).

**Where the authors' 87 comes from.** Count every indicated $+$, $-$ and $\times$
sign in the fourteen printed equations of Theorem 2.12 once, and do not count
exponentiation. This gives exactly 87: 35 additions, 17 subtractions and 35
multiplications, with 24 powers not counted. The per-equation counts are
$(3,6,7,4,5,3,5,11,3,3,2,12,12,11)$. The same rule reproduces the 100 of the 1980 and 1982
papers (`Papers/verification/round4_1980_operation_count.py` and its `.json`). So "easily
calculated" most likely meant this count of signs. For this article the sign count and the
verified straight-line bound happen to agree.

**Not claimed.** The reconstruction does not claim that 87 is minimal or that this is the
authors' evaluation order. The count says nothing about bit complexity or the size of the
witnesses, and it gives no way of finding the witnesses.

## 6. Readings examined and retained, and changes reverted

**Changes made in an earlier revision and reverted (no net discrepancy).** These should
not be re-proposed.
- *Integer-part notation* (log: 76-R4-03). The scan defines "$[x]$ denotes the greatest
  integer $\leqq x$" (p. 451) and uses $[\;]$ throughout. An earlier revision of this
  edition silently switched the definition and displays (12) and (23) to $\lfloor\;\rfloor$,
  while Lemma 3.3 and the necessity proof kept $[\;]$. The printed $[x]$ is back everywhere.
- *Name prefix of (1)* (log: 76-R4-04). An earlier revision began display (1) with
  `P(a,b,\ldots,z)=`, which the scan does not print, without recording the change. It was
  removed. The following text names the polynomial anyway.
- *Brackets and "$n\ge1$" in (5)* (log: 76-R4-05). This is folded into 1976-11: the
  printed outer parentheses are back and the unrecorded qualifier has been removed.

**Original readings confirmed as correct (no change).**
- "Our construction here yields a polynomial in 19 variables and degree 29" (p. 449) is the
  printed wording. It refers to an intermediate elimination, not to (1).
- The example value $-76$ is printed in the original, and it is attained. Two independent
  witnesses were checked:
  $a=c=d=e=g=k=l=m=n=q=r=s=0$, $b=h=i=j=o=p=t=u=v=w=x=y=z=1$, $f=6$; and
  $a=b=c=d=0$, $e=1$, $f=6$, $g=0$, $h=2$, $i=1$, $j=k=l=0$, $m=1$, $n=0$, $o=2$, $p=1$,
  $q=r=s=t=0$, $u=1$, $v=w=0$, $x=1$, $y=0$, $z=4$.
- $M>160\cdot10^{10}$ in (5) of §3 is printed and true (1976-36).
- The gaps in the equation numbering (no (2) in §1, no (6)–(7) in §4) are in the scan.
  References [5] and [15] are not cited in the scan either.
- Formula (5) as printed is correct. The $j=0$ term contributes 1, and that is what makes
  $\mathbin{\dot{-}}n$ right (1976-11).
- Lemma 2.3: the step $(a-2)(a-1)+(a-1)^{a-2}<(2a-1)^{a-2}$ holds for $a\ge3$. The case
  $a=2$ is excluded by $e\ge2$. The least $n$ with $e^3(e+2)(n+1)^2+1=\square$ is 2, 20,
  244, 4060, 87814 for $e=2,\ldots,6$, which respects the stated bound.
- Lemma 2.10 (i)–(iv), including $2k^2k!\le(2k)^k$ (equality at $k=1,2$). Lemma 2.11 in
  both directions ($h,j\ge0$). Theorem 2.12: the nine modulus inequalities, the three uses
  of Lemma 2.4 with $(P,N)=(n+1,k),(p+1,n),(p,k)$, and $p^k<a$ in the necessity proof.
- Lemma 3.4's hint "as in the proof of Lemma 2.10, condition (iv)" is right, because only
  $k-1$ factors are nontrivial. Lemma 3.8 and system (I)–(XXI) are identical to the scan.
- Counts at the end of §3: 10 unknowns $+1=11$, a 12-variable $P$, and degree
  $2\cdot6848+1=13697$. They are consistent.
- The second factor of (24) is $\equiv1\pmod T$, and $2(n+1)\mid j$ (1976-53).
- Repeated checks found no further formula error and no counterexample to the corrected
  equations. The Pell normalizations of this article deliberately differ from those of the 1978–1982 papers and are not harmonized with them.

**Observations recorded without changing the text** (from the Lean formalization).
- *Equations hold in $\mathbb Z$.* "All variables are nonnegative integers" (§2) has to be
  read as nonnegative unknowns in integer equations. If $u^2-a$ in Corollary 2.6 (III),
  which is Theorem 2.12 (8), were read as truncated subtraction, then $r=0$, $u=1$ would
  admit spurious solutions, for example $a=2$, $n=1$, $y=4$, $x=7$, $c=355$, $d=13$
  (even though $y\neq\psi_2(1)$). The Lean statements cast to $\mathbb Z$.
- *Theorem 3.9.* The chain (17) needs $n\ge k+3$. This follows from (2), since
  $(2k)^{2k}\ge4k\ge k+3$, though the text does not say so. The estimate (11) holds with
  "$\le$" on the right, and the strict consequences still follow. The sufficiency proof does
  not mention the case $\sigma-(w+1)x<0$; it is excluded because then $\beta\le0$, while
  (XIV) forces $\beta>S+\frac12$. The same observation replaces "$\sigma<\frac12\Rightarrow
  \beta<0$" in the argument that $p'=l'=0$. The square-root step for $r'>0$ can be replaced
  by $4RC^2<(R-C)^2$ for $R>C^3$, $C\ge5$. The bounds in (20) and (21) can be simplified.
  None of these is an error in a printed statement.
- *Theorem 4.1.* The formal proof uses the origin as its base point (1976-57).
- *Theorem 4.* The parenthetical "we may take $l=13$ and hence $k=14$" is formalized
  (`JSWW1976.theorem_4_fourteen`, via the 1982 nine-unknown reduction). Lean uses one-based
  indexing, `Nat.nth Nat.Prime (n - 1)`.

## 7. Verification summary

*Programs.* The verification programs are
`Papers/verification/jones1976_verify_mathematics.py` and
`jones1976_verify_87_operations.py` (which regenerates `jones1976_primality87.json` and
`jones1976_primality87.md`). They read the current source and were re-run on
24 September 2026; both pass.

- **Exact checks** (`jones1976_verify_mathematics.py`). All of the following pass:
  - The polynomial against Theorem 2.12 (14 residuals; degree 25; 26 variables; 917
    monomials; the value $-76$).
  - The Pell identity, both recurrences and Lemmas 2.1–2.2 (620 cases, $1\le a\le20$,
    $0\le n\le30$).
  - Lemma 2.4 (2080 cases).
  - Divisibility-compatible witnesses for Lemma 2.3 (40 cases).
  - The factorial bounds of Lemma 2.10 (36 cases).
  - The elementary bounds of Lemmas 2.7, 2.8 and 3.1–3.6 (2113 cases, exact rationals).
  - Formula (5) for $n=1,\ldots,100$ and the six zero-tests for $x=0,\ldots,1000$.
  - Denominator clearing and equations (23), (24) (4 identities).
  - The two boundary counterexamples to the printed strict inequalities (1976-23 and
    1976-43).

  These are finite and symbolic checks, not proofs of the general lemmas.
- **Certificate** (`jones1976_verify_87_operations.py`): the exact residual comparison of
  §5.2.
- **Independent checks:** `Papers/verification/round4_1976_checks.py` (results in
  `round4_1976_results.json`) checks degree 25 in 26 variables, the identity of (1) with
  Theorem 2.12, the $-76$ witness, formula (5) as printed for $n=1..40$, Lemma 2.3's least
  solutions, Lemma 2.4 and samples of Lemma 2.10. `Papers/verification/round4_1976_theorem39.wl`
  (results in `round4_1976_theorem39_results.json`) builds the necessity witnesses of
  Theorem 3.9 exactly for $k=1$: $n=244$, $x$ with 1461 digits, $M$ with 354,894 digits,
  $K$ and $C$ with about 86 million digits. It confirms $\sigma'=\binom nk=244$ and
  $\beta=k!=1$ to within $10^{-199}$, so (XIV) and the Case 1 bounds (15) and (17) hold.
  `Papers/verification/round4_1980_operation_count.py` reproduces the sign count 87. A
  number-by-number diff of all numerals against the scan finds only the documented changes
  (1976-63, 1976-64). No word in the prose is misspelled, and the LaTeX build logs show no
  undefined references and no overfull boxes.
- **Lean 4** (`Lean/Diophantine/Paper1976/`; status table in `Lean/STATUS.md`). The following
  are machine-checked, and the only external inputs are Mathlib and cited classical
  theorems:
  - The chain from Lemma 2.3 through Corollary 2.6, Lemmas 2.7–2.11 and Theorem 2.12 to
    Theorem 1 (`JSWW1976.theorem_1`).
  - Lemma 3.8 in full and Theorem 3.9 in both directions (`theorem_3_9`).
  - The elimination to ten witnesses with the cleared (XIV).
  - Equation (24).
  - Theorem 2 with an explicit 12-variable polynomial, and a padded construction of exact
    degree 13697. Degrees 13376/6848/13697 are proved only as upper bounds for the
    unpadded constructions; 148864 is not formalized.
  - Theorem 3 (`PrimeZeroTest`), Theorem 4 (including the 14-witness refinement), Theorem 5
    (the certificate of §5.2), Theorem 4.1 and Theorem 4.4.

  Theorem 4.2 and Corollary 4.3 are **not** formalized. Their rewritten proof (1976-58) was
  checked only by reading.
