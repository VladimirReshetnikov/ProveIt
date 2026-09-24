# Editorial notes: Jones 1978, *Three Universal Representations of Recursively Enumerable Sets*

James P. Jones, **Three Universal Representations of Recursively Enumerable Sets**,
*The Journal of Symbolic Logic* 43, no. 2 (June 1978), pp. 335–351.
DOI [10.2307/2272832](https://doi.org/10.2307/2272832).
Received December 8, 1975; revised August 30, 1976.

## 1. Scope

This document compares three objects:

- **The scan**: `original/1978/jones1978.pdf`, the JSTOR scan of the printed
  article, 17 pages, printed pp. 335–351. It is the authority for what Jones
  printed.
- **The naive OCR reading**: `original/1978/jones1978.tex`, the Mathpix OCR of the
  scan. The OCR did not transcribe three lines of system (1.3). It cropped them
  as images instead (`original/1978/images/*_03_35_*.jpg`, `*_03_41_*.jpg`,
  `*_03_37_*.jpg`) and put the rest of the system in garbled `verbatim` blocks.
- **The reconstruction**: `Papers/1978/jones1978_corrected.tex` and its PDF. It
  gives our reconstruction of what the article is meant to say mathematically.

This document explains every difference between the OCR and the reconstruction
that is not pure layout. It is the record for this article. The dated log of
revisions and checks, `Papers/EDITORIAL_NOTES.md`, registers individual changes
under IDs such as 78-R4-01 to 78-R4-27; those IDs are cited here where useful.
Page numbers are the original printed page numbers, not the pages of the new PDF.

The edition was first issued on 13 September 2026, with the whole article
transcribed, (1.3) reconstructed and all the substantive corrections made. It has
since been revised continuously: the effective-axiomatizability hypothesis was
made explicit in three places; (1.3) was re-derived and compared sign by sign
with the scan; typographical and bibliographic fixes were made, the margin
pagination marks added, the operation-count footnote rewritten, and the article
formalized in Lean. On 24 September 2026 the remaining silent clarifications
were made visible as editorial notes, the author's sentence of 1978-16 was
restored, footnote 2 and the `[335]` mark were corrected, and the edition
apparatus was pointed to this file (78-R4-09 to 78-R4-26).

## 2. Classifications

| Class | Meaning |
|---|---|
| **OCR** | Transcription defect: the scan is right and the OCR is wrong. |
| **ORIG** | Mathematical error in the printed original, corrected. |
| **CLAR** | Editorial clarification, proof completion or stated hypothesis. The edition marks these as editorial in the text. Fifteen were silent until they were marked on 24 September 2026; see §5. |
| **TYPO** | Typographical or cross-reference slip in the printed original, with no mathematical consequence once it is read correctly. |
| **BIB** | Bibliographic correction or normalization. |
| **EDN** | Edition apparatus: notices, pagination marks, metadata, numbering. |
| **LAYOUT** | Reflow or typesetting with no content change. |

The dated log also uses **BUILD** for source-build changes that do not affect the text
(78-R4-01, 78-R4-04). Those are described in §3.

## 3. Systematic differences (described once)

These classes of difference occur throughout. They are not repeated in the
register.

1. **Document scaffolding (LAYOUT, BUILD).** The OCR's XeLaTeX preamble is
   replaced by a standalone LuaLaTeX document with STIX Two fonts. The removed
   items are `ucharclasses` font transitions, `polyglossia`, the
   `\blfootnotetext` and `\footnotetext` overrides, and the `\newunicodechar{→}`
   hack. The epigraph font is Noto Serif Devanagari, with a fallback to Nirmala UI
   when Noto is absent (78-R4-01, BUILD). The fallback changes glyph shapes but
   not the text. Nine lines ended in a lone `\`, left over from the OCR's `\\`.
   These were removed (78-R4-04, BUILD; no change to the output).
2. **Front matter (EDN).** The following changes were made to the front matter:
   - The title and author, printed in capitals, are set in title case.
   - A journal/DOI/date line and the line "Corrected and re-typeset edition ·
     13 September 2026" are added.
   - "Received December 8, 1975; revised August 30, 1976", an unnumbered footnote
     in the print, becomes a centred line under the title. The date is as printed.
   - An "Editorial convention" box states that the edition has been continuously
     revised, explains the bracketed margin numbers, fixes the notation $\widehat
     W_n$ and $W_n$ (see 1978-06), and says that "best result", "open problem",
     "future paper" and "in press" keep their 1978 meaning.
   - Running heads are set.

   The notice and the source's header comments point readers to this file,
   which explains every discrepancy, and to `Papers/EDITORIAL_NOTES.md`, a dated
   log of revisions and checks (78-R4-09). The header comments read
   "% Continuously revised edition; last source revision 24 September 2026."
   and "% A dated log of revisions and checks is ../EDITORIAL_NOTES.md." The
   edition line under the title still reads "13 September 2026".
3. **Original pagination (EDN).** `\origpage{n}` puts a bold `[n]` in
   the margin of the line on which printed page *n* begins, for n = 335–351
   (17 marks). The marks are accurate to the line, not the word. The marks for
   pp. 341, 344 and 347–350 were placed by hand from the scan. The mark for p. 347
   sits at the corresponding sentence of the rewritten passage (1978-43). The
   `[335]` mark sits at the first line of §1 ("In his celebrated paper…"), the
   start of the article text, as the first mark does in the 1984 edition. The
   title and epigraph precede it on the same printed page. Until
   24 September 2026 the mark sat at the third paragraph of §1 ("In this
   article we construct…"), although the first two paragraphs are also on
   p. 335 (78-R4-11).
4. **Reflow (LAYOUT).** The following typesetting was undone or regularized:
   - hard line breaks (`\\`, `\\[0pt]`) and page-break line wraps;
   - run-in headings ("§1. Introduction.", "THEOREM 1.", "PROOF OF SUFFICIENCY.");
     these become section headings, bold lemma heads and italic proof heads;
   - OCR bold math, such as `\boldsymbol{x} \in \boldsymbol{W}_{\boldsymbol{n}}`,
     `\boldsymbol{A}_{i}`, `F \mid \boldsymbol{H}-C` and
     `\boldsymbol{\exists} \boldsymbol{\forall}^{\mathbf{2}}`;
   - small capitals in names;
   - the address block, printed in capitals.

   The universal-pairs table is printed as a 4×4 grid of entries `108, 4`, …,
   `40, 1380`. It is set with booktabs as `(108,4)`, …, `(40,1380)`, and the
   entries are unchanged.
5. **Condition lists.** The print sets B0–B8, T0–T9, A1–A7, P1–P7, Q1–Q4 and
   U1–U8 in two columns. The reconstruction sets each list in numerical order as
   a tagged `align`. The OCR's reading order is also broken: see 1978-30.
6. **System (1.3) numbering (EDN).** The print has one collective label (1.3). The
   reconstruction keeps it and also numbers the 36 equations (1.3.01)–(1.3.36).
   Its braces `{3g+2−r}{3n+g−r}` in (1.3.09) are set as parentheses.
7. **Notation normalization (LAYOUT).** The following normalizations change no
   content:
   - the integer part `[(X+1)^N/X^z]` of the print (Lemma 2.6, B0, Lemma 2.8) is
     written $\lfloor\cdot\rfloor$;
   - `\cdots`/`\ldots`, `\Leftrightarrow`/`\Longleftrightarrow`, `\Sigma_i` →
     `\sum_i`;
   - `z!^2` becomes `(z!)^2` in the BQT proof, but `Z!^2` is kept in Lemma 3.5;
   - Theorem 2's outer factor `{n+s+1-i}` is written `(n+s+1-i)`. The same braces
     are kept in the principle displayed on p. 347.
8. **Punctuation and spacing (OCR/TYPO/LAYOUT).** The OCR's spaces before
   punctuation are removed: `2 , is`, `9 . Yuri`, `9 . It`, `AB=0$ , $A=0`,
   `2 .`, `38 .`, `be ?`, `possible ?` (78-R4-02, classed OCR). The following are
   also normalized:
   - quotation marks become ``` ``…'' ``` without inner padding: "focused",
     "∧", "∨", "⟶", "<n", "<u+v", "j = s", "R", "β", "a", "b" (78-R4-03);
   - the empty groups in the second prefix `\forall{ }^{2} \exists{ }^{2}` are
     removed (78-R4-05);
   - condition and lemma ranges get en dashes: B0–B8, T1–T9, A1–A7, (i)–(iv),
     Lemmas 2.3–2.10 (78-R4-06);
   - missing spaces are restored in `[14],from`, `(cf.[5]`, `Robinson,Two`,
     `Matijasevič ,` and `this Journal ,`.

   In §1 the OCR reads the scan's "∨" as ` v ` and gives the arrow as a raw `→`.
   The reconstruction prints ∨ and ⟶ (OCR).
9. **Bibliography form (BIB, LAYOUT).** The following changes are form only:
   - the ditto rules "——" are expanded to author names ([3], [4], [10],
     [15]–[17], [23], [25]);
   - page ranges get en dashes;
   - entries are set with `thebibliography`, keeping the original numbering [1]–[27].

   Changes to the content of entries are listed in the register (1978-56 to
   1978-64).

## 4. Discrepancy register

Entries are in the order of the original pages. "OCR" quotes the Mathpix text,
"Scan" is given where it differs from the OCR, and "Reconstruction" is the
current text.

### p. 335 (title page)

**1978-01 · Epigraph, Devanagari · OCR.**
- OCR: `इंहैकस्यं जगन्कृन्स्त्रं पश्याद्य सचरायरम।` / `मम दे हे गुडाकेश यचान्यद्द्रष्टमिच्छसि॥`
- Scan: the canonical verse, printed in a hand-drawn Devanagari font.
- Reconstruction: `इहैकस्थं जगत्कृत्स्नं पश्याद्य सचराचरम् ।` / `मम देहे गुडाकेश यच्चान्यद्द्रष्टुमिच्छसि ॥`
- Justification: The text is *Bhagavad-Gītā* 11.7. It was compared with the
  scan and with standard verse editions (IIT Kanpur Gita Supersite), and checked
  again independently. The corruption is in the OCR only.

**1978-02 · Footnote 1, transliteration · OCR.**
- OCR: `Ihaikastham jagat kṛtsnam paśyādya sa-carācaram mama dehe guḍākeśa yac cānyad draṣtum icchasi.`
- Scan: `Ihaikasthaṁ … kṛtsnaṁ … draṣṭum` (anusvāra printed as ṁ; ṭ with an underdot).
- Reconstruction: `Ihaikasthaṃ jagat kṛtsnaṃ … draṣṭum icchasi.`
- Justification: The OCR dropped the diacritics. The reconstruction writes the
  anusvāra in the current IAST form ṃ instead of the printed ṁ; this is a
  convention change, not a correction. (The classification is from the scan.)
  Until 24 September 2026, footnote 2 in the reconstruction said that the
  Sanskrit and transliteration "have been corrected", which is true only
  relative to the OCR. On that date the footnote was changed to state the ṁ/ṃ
  difference instead (78-R4-10; see 1978-03).

**1978-03 · Footnote 2, English paraphrase and source · EDN.**
- OCR/scan: footnote ² reads "Whatever you wish … Everything is here completely.—Bh.G., 11, text 7."
- Reconstruction: The paraphrase is a small quotation under the verse. Its
  footnote reads "Bhagavad-Gītā, chapter 11, verse 7. In the original this
  paraphrase is itself footnote 2, attached to the transliteration, and ends
  '—Bh.G., 11, text 7.' The Sanskrit, the transliteration and the paraphrase are
  as printed, except that the transliteration writes the anusvāra ṃ where the
  original has ṁ."
- Justification: The paraphrase is kept verbatim. The source reference is spelled
  out, and the footnote now describes the edition's handling exactly. History:
  until 24 September 2026 the footnote read "The English paraphrase is retained
  from the original article; the Sanskrit and transliteration have been
  corrected." Compared with the print the only change is the ṁ→ṃ convention
  (1978-01, 1978-02); the corrections were to the OCR. On that date (78-R4-10)
  the footnote was rewritten accordingly, and it now also records the printed
  position of the paraphrase.

### p. 336 (Theorems 1 and 2)

**1978-04 · Theorems 1 and 2, domains of $x,n$ and of the sets · CLAR.**
- OCR/scan: "The r.e. sets, $W_1,W_2,\cdots$, may be represented in the form …" (both theorems).
- Reconstruction: The statements read "The r.e. sets of positive integers,
  $\widehat W_1,\widehat W_2,\ldots$, may be represented, for $x,n>0$, in the
  form …" and "The same r.e. sets $\widehat W_1,\ldots$ may be represented, for
  $x,n>0$, by …". Lemma 3.1 (p. 345) gains "for $x>0$". The 11 quantified
  variables still range over the nonnegative integers.
- Justification: §3 enumerates sets of *positive* integers, and Lemmas 3.2–3.5
  assume $n,x>0$. Without that convention, $x=0$ would satisfy every polynomial
  presentation $P_u=P_v+x$ that has a solution with $P_u=P_v$. The rewording "The
  same" in Theorem 2 is editorial; the scan repeats "The r.e. sets".

**1978-05 · Theorems 1 and 2, delimiters of the matrix · CLAR.**
- OCR/scan: Theorem 1 prints `{(s+w)^2+3w+s=2i ∧ ⟨[j=w ∧ v=q] ∨ [j=3i ∧ v=p+q] ∨ [j=s ∧ (v=p ∨ (i=n ∧ v=q+x))] ∨ [j=3i+1 ∧ v=pq] → a=v+e+ejb ∧ v+g=jb⟩}`. Theorem 2 prints `{n+s+1−i}{⟨…⟩^2+⟨[…][…][…][…]−e−1⟩^2⟨[v+e+ejb−a]^2+[v+g−jb]^2⟩}=0`. The OCR adds stray `.` characters between the bracketed factors.
- Reconstruction: The same formulas are set with nested parentheses. In
  Theorem 1 the whole disjunction is the antecedent, and the conjunction
  $a=v+e+ejb\wedge v+g=jb$ is the consequent.
- Justification: The angle brackets and the precedence of → are left implicit in
  the print. The grouping chosen is the only one that makes Theorem 1 the
  distribution of (3.3), and Theorem 2 its translation by the three principles of
  p. 347. That translation was checked by hand in both directions, and Lean
  (`Jones1978.thm1_iff_thm2`) proves it. No content change.

**1978-06 · Theorems 1–2 versus Theorem 3: two different enumerations · ORIG.**
- OCR/scan: Theorems 1–2 (p. 336), Theorem 3 (p. 337) and all of §3 use the same
  name $W_n$. On pp. 346–347 the article switches to nonnegative witnesses "Hence
  3.2 may be formulated in terms of least nonnegative residues", and then
  "rewrite[s] Lemma 3.2 in the form $x\in W_n\Leftrightarrow$ (3.3)".
- Reconstruction: The enumeration with nonnegative witnesses (Theorems 1, 2 and
  (3.3)) is written $\widehat W_n$. The enumeration with integer witnesses
  (Lemma 3.2, Lemmas 3.4–3.5, Theorem 3) remains $W_n$. The notice and §3 say the
  two families have the same range of sets but are not equal index by index. The
  rewritten passage is entry 1978-40.
- Justification: Take $n=5=J(0,2)$, so that $u=K(5)=0$ and $v=L(5)=2$. With
  $P_0=0$ and $P_2=X_0$, the condition becomes $0=X_0+x$. Over the integers it
  has the solution $X_0=-x$ for every $x>0$, so $W_5=\mathbb Z_{>0}$. Over the
  nonnegative integers it has no solution, so $\widehat W_5=\varnothing$. Each
  enumeration contains every Diophantine set, and hence every r.e. set by MRDP.
  Integer witnesses are differences of nonnegative ones; nonnegative witnesses
  are sums of four squares. But "the r.e. sets $W_1,W_2,\ldots$" cannot denote the
  same indexed family in Theorems 1 and 3. Lean formalizes both (`Jones1978.W`,
  `Jones1978.Wh`).

**1978-07 · First quantifier prefix · OCR.** Log: 78-R4-05.
- OCR: `\Xi^{2} \forall \Xi^{4} \forall{ }^{2} \Xi^{2}` (∃ read as Ξ), with empty groups in the second occurrence.
- Scan: $\exists^2\forall\exists^4\forall^2\exists^2$ (twice).
- Reconstruction: `\exists^{2}\forall\exists^{4}\forall^{2}\exists^{2}` in both places.
- Justification: The scan shows this prefix, and it matches the 11 bound variables
  $a\,b\;i\;s\,w\,p\,q\;j\,v\;e\,g$.

**1978-08 · Matijasevič's prefix · OCR.**
- OCR: `\boldsymbol{\exists} \boldsymbol{\forall}^{\mathbf{2}}` (reads as ∃∀²).
- Scan: $\exists\forall\exists^2$.
- Reconstruction: $\exists\forall\exists^{2}$.
- Justification: The OCR dropped the final ∃ group. The scan is unambiguous.

### p. 337

**1978-09 · Parameters $a_1,\ldots,a_\kappa$ · OCR.** First classified as a typo in the print; the scan shows the error is the OCR's.
- OCR: `The variables $a_{1}, \cdots, a_{k}$ are called parameters.`
- Scan: $a_1,\cdots,a_\kappa$.
- Reconstruction: $a_1,\cdots,a_\kappa$.
- Justification: The scan prints κ, so the error is the OCR's. Compare 1978-18,
  where the print really is wrong.

**1978-10 · Witness domain of Diophantine relations · CLAR.**
- OCR/scan: "…understood to run through the nonnegative integers, although it makes no difference whether we specify nonnegative integers, positive integers or integers."
- Reconstruction: "…although the same class of relations is obtained if we use positive integers or integers, after the appropriate change of variables." An editorial note quotes the printed clause and explains the change.
- Justification: Changing the witness domain preserves the class of Diophantine
  relations, but not a given polynomial or its index. Example 1978-06 shows the
  index is not preserved. The change was silent until it was marked on
  24 September 2026 (78-R4-12).

**1978-11 · Statement of Theorem 3 · EDN.**
- OCR/scan: "…the following system of equations **has** a solution in nonnegative integers: (1.3)"
- Reconstruction: "…the following system of equations **have** a solution in nonnegative integers. The system retains its original collective label (1.3); its 36 equations are individually numbered here for reference."
- Justification: The added sentence is edition apparatus (§3 item 6). The
  subjunctive "have" is an editorial rewording; the printed "has" is equally
  correct. No content change.

**1978-12 · System (1.3) as a whole · OCR.**
- OCR: The 11 printed lines are handled as follows:
  - line 1 (2n=… z=3n+α³) is cropped as the image `…03_35_1108_1727_132.jpg`;
  - lines 2–3 are a garbled `verbatim` block;
  - line 4, the B-factor of (1.3.09) with $(3g+2-r)(3n+g-r)=q\pi$, is the image
    `…03_41_1104_1855_134.jpg`;
  - lines 5–8 are `verbatim`, and the OCR drops "$=\delta^2$, $\eta=\sigma r+\sigma$,
    $\eta=b+(q'+\sigma)a'$" from line 5;
  - line 9, (1.3.27)–(1.3.31), is the image `…03_37_1062_2073_132.jpg`;
  - line 10 is `verbatim`.
- Reconstruction: The 36 equations are typed as LaTeX, (1.3.01)–(1.3.36). No
  mathematical content remains in an image.
- Justification: Every equation was checked against the scan and against its
  construction from U1–U8, B1–B8, T1–T9 and Q2–Q4. Page 337 was then read again
  at 400 dpi, sign by sign, and the system was re-derived by hand under the letter
  map of p. 349. The map is A→a, C→c, D→d, F→f, K→κ, L→λ, M→μ, N→η, P→p, R→α, T→t,
  W→ω, X→χ, Y→y, Z→z. The letters b₁…b₅→f′…j′, c₁…c₅→k′…p′ and d₁…d₅→q′…u′, with
  J=Z⁶ and U7 taken modulo q. The system is:

  | Equations | Source conditions |
  |---|---|
  | (1.3.01)–(1.3.04) | U1–U4 |
  | (1.3.05)–(1.3.06) | U5–U6 |
  | (1.3.07)–(1.3.08) | U7 as congruences mod $q$ (unknowns $\varphi,\phi$) |
  | (1.3.09) | U8 |
  | (1.3.10)–(1.3.12) | B1–B3 |
  | (1.3.13)–(1.3.17) | B4 (unknowns $a'$–$e'$) |
  | (1.3.18)–(1.3.20) | B5–B7 |
  | (1.3.21)–(1.3.25) | B8 |
  | (1.3.26)–(1.3.33) | T1–T7, T9 (T8 substituted; T3/T4 in the variant $5(C-KLY)^2\le K^2L^2$, $M=9NXY$) |
  | (1.3.34)–(1.3.36) | Q2–Q4 |

  All equations agree exactly with the scan (but see §6, first item) and with
  the construction.

**1978-13 · (1.3.01)–(1.3.09), individual misreadings · OCR.**
- OCR misreads (in the `verbatim` text):
  - `zl 8(z6+2)(r+1)\2+1=ψ2` is (1.3.06) $z^{18}(z^6+2)(r+1)^2+1=\psi^2$;
  - `t+e+eß+e 3s=α+q५` is (1.3.07) $t+e+e\beta+e\beta s=\alpha+q\varphi$;
  - `p+b+b +b + bw= α+q ,` is (1.3.08) $p+b+b\beta+b\beta w=\alpha+q\phi$;
  - `[3(s+w) 2+ qw+3s-2r] 2` is $[3(s+w)^2+9w+3s-2r]^2$ (the scan's "9w" is read
    as "qw");
  - `(1+ + + r 3 2` and `(1+; + r 3 ) 2` are $(1+\beta+r\beta)^2$;
  - `( 3-t 2 - p2)` is $(\beta-t^2-p^2)$;
  - `{[3 (s+w) 2+9w+3s+2-2r} 2+` is $[3(s+w)^2+9w+3s+2-2r]^2+$.
- Reconstruction: (1.3.01)–(1.3.09) as in the edition.
- Justification: Comparison with the scan. In the degree-38 product (1.3.09), the
  A-factor has $\alpha-t-p$ and the B-factor has $\alpha-tp$. Both use
  $\beta-t^2-p^2$. The two pairing brackets differ by $+2$, as $2\cdot(3J+1)=6J+2$
  requires. The degree is $16+20+1+1=38$.

**1978-14 · (1.3.10)–(1.3.36), individual misreadings · OCR.**
- OCR confusions:
  - ω read as `w`; σ read as `o`, `a` or `+`, or dropped; η read as `n`;
  - ζ read as `c` or `<`; ε² read as `e2`; μ read as `u`; χ read as `x`; ν read
    as `v`;
  - primes lost: `y=qg+(r+)l`, …, `y=qj+(u+)p` stand for
    $y=qg'+(r'+\sigma)l'$, …, $y=qj'+(u'+\sigma)p'$;
  - `(u2-1)2+1=v2` stands for $(\mu^2-1)\kappa^2+1=\nu^2$;
  - `a=ux+u` stands for $a=\mu\chi+\mu$; `c=m+n+1` stands for $c=m+\eta+1$;
  - `不=(a2-1)c2+1` stands for $d^2=(a^2-1)c^2+1$;
  - `f2=4(a-1)i curtnell` stands for $f^2=4(a^2-1)i^2c^4+1$;
  - `(n+1+2jc)` stands for $(\eta+1+2jc)$.
- Reconstruction: (1.3.10)–(1.3.36) as in the edition. The Greek letters
  $\upsilon$ (1.3.27) and $\nu$ (1.3.26) are both distinct from the Latin $v$, and
  $\varphi$ (1.3.07) is distinct from $\phi$ (1.3.08).
- Justification: Comparison with the scan and the construction. The count of
  unknowns is 67, not counting the parameters $x$ and $n$. It was counted twice,
  independently.

### p. 338

**1978-15 · "any other axiomatizable theory"; "an axiomatic theory $T$" · CLAR.**
- OCR/scan: "theorems of any other axiomatizable theory"; "the assertions of an axiomatic theory $T$ may be Gödel numbered so that the theorems become in effect an r.e. set".
- Reconstruction: "…any other effectively axiomatizable theory"; "…an effectively axiomatizable theory $T$…". An editorial note at the first occurrence quotes the three printed phrases (the third is in Corollary 1, 1978-17) and says that "effectively" is added in all three places.
- Justification: The theorems of an arbitrary set of axioms need not form an r.e.
  set, and the argument needs an effective presentation. Traditional usage often
  reads "axiomatizable" this way already. The edit makes the convention explicit
  and does not claim the author meant non-effective theories. It was silent
  until it was marked on 24 September 2026 (78-R4-13).

**1978-16 · "absolute epistemological upper bound" · CLAR.**
- OCR/scan: "Hence from Theorem 3 we obtain an absolute epistemological upper bound on the complexity of mathematical proofs."
- Reconstruction: the printed sentence, verbatim, with an editorial note: "What Theorem 3 bounds uniformly is the number of arithmetic operations needed to check a Diophantine certificate by the fixed system (1.3); see Corollary 1. It is not a bound on the sizes of the integers, on the time needed to find them, or on the length of an ordinary formal proof."
- Justification: MRDP gives a fixed verifier. It gives no constant bound on the
  size of the witnesses, on bit complexity, on search, or on the length of proofs
  in the original calculus. The printed sentence is the author's interpretation
  ("epistemological", "complexity" in his sense of operation count), in the same
  vein as the preceding printed sentence, which the edition always kept, that
  proofs "are reducible to a bounded number of arithmetical operations". It is a
  philosophical claim, not a mathematical error, so the author's words are kept
  and the precise reading goes into the note. History: an earlier revision of
  this edition replaced the sentence silently by "Hence from Theorem 3 we obtain
  a uniform bound on the arithmetic-operation count for checking such a
  Diophantine certificate. This is not a bound on the sizes of the integers, the
  time needed to find them, or the length of an ordinary formal proof." That
  replacement was reverted for the reason just given, and the printed sentence
  was restored on 24 September 2026 (78-R4-14).

**1978-17 · Corollary 1 · CLAR (marked by footnote).**
- OCR/scan: "COROLLARY 1. For any axiomatizable theory $T$ and any proposition $P$, if $P$ has a proof in $T$, then $P$ has another proof consisting of only 243 additions and multiplications of integers."
- Reconstruction: The heading is "Corollary 1 (certificate interpretation)". The
  statement reads "For any effectively axiomatizable theory $T$ …, then $P$ has a
  Diophantine certificate verified by the fixed system (1.3), with the stated
  count of 243 additions and multiplications of integers." A footnote says:
  - the original says "another proof";
  - the count excludes writing and searching for the witnesses and the equality
    tests;
  - 243 is the author's figure;
  - counting every indicated $+,-,\times$ sign of (1.3) once gives 241, and the two
    missing signs have not been located;
  - the same rule reproduces the counts 87 (1976) and 100 (1980/1982) exactly;
  - the reading is examined in `Papers/1980/jones1980_theorem5_operations.pdf`.
- Justification: See 1978-15 and 1978-16. The added "effectively" is marked by
  the note of 1978-15, which quotes the printed "any axiomatizable theory $T$".
  History of the footnote: an earlier version said "not independently
  rederived"; this was replaced by the sign-count finding. Lean now gives an
  explicit certificate of 241 instructions (§7). The number 243 itself is kept
  (§6).

### p. 339

**1978-18 · $U(x,n,z_1,\ldots,z_\nu)$ · TYPO.**
- OCR: `U\left(x, n, z_{1}, \cdots, z_{k}\right)`.
- Scan: $U(x,n,z_1,\cdots,z_\kappa)$. The print has κ, which is the letter for the number of parameters.
- Reconstruction: $U(x,n,z_1,\cdots,z_\nu)$.
- Justification: The same sentence continues with
  $U(J_\kappa(x_1,\ldots,x_\kappa),n,z_1,\ldots,z_\nu)$. The unknowns are
  $z_1,\ldots,z_\nu$ and κ counts parameters.

### p. 340 (§2)

**1978-19 · "$E=\square$ is an abbreviation…" · LAYOUT.**
- OCR/scan: "…(a, b)=1. $E=\square$ is an abbreviation for '$E$ is a perfect square'."
- Reconstruction: "…$(a,b)=1$. The notation $E=\square$ is an abbreviation for …"
- Justification: This is an editorial wording that avoids starting a sentence with
  a formula. No content change.

**1978-20 · "Lemmas 2.1." · TYPO.**
- OCR/scan: "LEMMAS 2.1."
- Reconstruction: "Lemma 2.1."
- Justification: A single lemma is meant.

**1978-21 · Divisor Lemma, $n\ge1$ · CLAR.**
- OCR/scan: "For any integers $s,t_1,\cdots,t_n$, $s\ge0$, if $s\mid t_1t_2\cdots t_n$ …"
- Reconstruction: "For $n\ge1$ and any integers $s,t_1,\cdots,t_n$ with $s\ge0$, …", with an editorial note quoting the printed opening.
- Justification: The conclusion $s^{1/n}\le p$ needs $n\ge1$. Silent until
  it was marked on 24 September 2026 (78-R4-15).

**1978-22 · BQT preamble, parameter list $a_1,\ldots,a_m$ · TYPO.**
- OCR/scan: "(think of $\tau,a_1,\cdots,a_n$ as parameters)". The polynomial was just written as $P(\tau,a_1,\cdots,a_m,y,z_1,\cdots,z_n)$.
- Reconstruction: "$\tau,a_1,\cdots,a_m$".
- Justification: In the print, $n$ counts the unknowns $z_i$ and $m$ counts the parameters.

**1978-23 · BQT hypotheses: $n\ge1$, $z\ge1$, $R(z)\ge1$ · CLAR.**
- OCR/scan: "…and a dominating function, $R(z)$ which we assume …"; Lemma 2.3: "…there exist nonnegative integers $z,r,z_1,\cdots,z_n$ such that"; necessity: "Choose $z>z_{y,i}$ for all $y,i$ and so that $z\ge\tau$."
- Reconstruction: "…where $n\ge1$, and a positive integer-valued dominating function $R(z)$, defined for $z\ge1$, …"; "…there exist integers $z\ge1$ and $r,z_1,\ldots,z_n\ge0$ …"; "…with $z\ge\max(1,\tau)$."
- Justification: The proof uses $z_1$, the Divisor Lemma for a product of $z$
  factors, and powers $1/z$, so it needs $n\ge1$ and $z\ge1$. The majorant may be
  replaced by $\max(1,R)$ and $z$ may be taken $\ge1$ without changing the
  predicate. This holds even when the bounded quantifier is vacuous ($\tau=0$).
  The three additions were silent until they were marked on 24 September 2026
  (78-R4-16) with one editorial note in the BQT preamble, which quotes the three
  printed phrases.

### p. 341

**1978-24 · Condition (iv), numerator $z_i$ · TYPO.**
- OCR: `\binom{ z_{i}^{i}}{z}`.
- Scan: the numerator is printed with a raised "i" and reads like $z^i$ (checked at high zoom).
- Reconstruction: $\binom{r}{z}\mid\binom{z_i}{z}$, $(i=1,\ldots,n)$.
- Justification: The proof and U0 use $\binom{z_i}{z}$ throughout.

**1978-25 · Divisor-chain indices and exponent · TYPO + OCR.**
- OCR: "satisfying $p_{i+1}\mid p_i$, $p_i\mid z_i-z_i'$, $0\le z_i'<z$ and $p_{i+1}\ge p_i^{1/2}$".
- Scan: "$p_{i+1}\mid p_i$, $p_i\mid z_i-z_i'$, $0\le z_i'<z$ and $p_{i+1}\ge p_i^{1/z}$". The exponent is $1/z$, and the index ranges are left unstated and mixed.
- Reconstruction: "$p_i\mid p_{i-1}$, $p_i\mid z_i-z_i'$, $0\le z_i'<z$ and $p_i\ge p_{i-1}^{1/z}$, for $1\le i\le n$".
- Justification: The OCR's exponent $1/2$ is a misreading of $1/z$. In the print,
  the first and last conditions are indexed by $i+1$ and the middle ones by $i$.
  The construction (step $i$ applies the Divisor Lemma to (1) with $p_{i-1}$ and
  produces $p_i$ and $z_i'$) gives the uniform form. Chain (3) is unchanged.

**1978-26 · $(t+z_1-r)$ in the congruence before (2) · TYPO.**
- OCR/scan: $z!P(r,z_1,\cdots,z_n)(t+z_1-r)\pmod{p_n}$.
- Reconstruction: $(\tau+z_1-r)$.
- Justification: The bound of the quantifier is τ, as in condition (i). There is
  no $t$ in this proof.

**1978-27 · The identity after (4), and pairwise coprimality · TYPO + CLAR.**
- OCR/scan: "The identity $j(r+1/j-1)-i(r+1/i-1)=i-j$ implies that the factors of (4) are pairwise relatively prime."
- Reconstruction: "The identity $j((r+1)/j-1)-i((r+1)/i-1)=i-j$ implies that every common divisor of two distinct factors divides $i-j$. Each factor is congruent to $-1$ modulo $z!$, since $(z!)^2\mid r+1$. Because $|i-j|\mid z!$ for $1\le i,j\le z$, $i\ne j$, the factors of (4) are pairwise relatively prime."
- Justification: As printed, $r+1/j$ means $r+\tfrac1j$. The identity alone gives
  only that a common divisor $d$ divides $i-j$. Since $(z!)^2\mid r+1$, each
  $(r+1)/j$ is divisible by $z!$, so each factor is $\equiv-1\pmod{z!}$. Then
  $d\mid i-j\mid z!$ forces $d\mid 1$. The added sentences complete the argument.
  They were silent until they were marked on 24 September 2026 (78-R4-17): an
  editorial note quotes the printed sentence and names the supplied parentheses
  and the two added sentences.

### p. 342

**1978-28 · Lemma 2.5, $d>0$ · CLAR.**
- OCR/scan: "If $a\equiv b\pmod d$, then $\binom az\equiv\binom bz\pmod{d/(d,z!)}$."
- Reconstruction: "For $d>0$, if …", with an editorial note quoting the printed opening.
- Justification: The quotient modulus $d/(d,z!)$ must be a positive integer.
  Silent until it was marked on 24 September 2026 (78-R4-18).

**1978-29 · Lemma statements 2.6–2.10: sentence fragments · TYPO.**
- OCR/scan:
  - Lemma 2.6: "For $z<N$ and $N^z<X$. If $Y=\dots$";
  - Lemma 2.7: "For $z!+6<r$. If $z!\mid r+1$ and U0 holds" (the OCR also has `U 0`);
  - Lemma 2.8: "For $0<Y$, $4N^Z<X$ and $0<Z<N$. The condition";
  - Lemma 2.9: "For $1<A$, $0<B$ and $0<C$. The relation";
  - Lemma 2.10: "For $1<A$ and $0<B$. The relation".
- Reconstruction: In each lemma the full stop becomes a comma: ", if", ", the condition", ", the relation". "U0" is restored.
- Justification: The print has sentence fragments. The punctuation is
  regularized, and the hypotheses are unchanged.

### pp. 342–345 (condition lists)

**1978-30 · Two-column condition lists read in the wrong order · OCR.**
- OCR: The two printed columns are read alternately, for example `B0. …`,
  `B4. …`, `B1. W=r+q+z_1+…+z_n`, `B5. …`, `+b_1+…+b_n,`, `B6. …`. The
  continuation of B1 ends up after B5. T0–T9, A1–A7, P1–P7, Q1–Q4 (p. 345) and
  U1–U8 (p. 348) are interleaved the same way. The label `Q4` is detached from its
  display.
- Reconstruction: Each list is in numerical order. B1 is whole:
  $W=r+q+z_1+\cdots+z_n+b_1+\cdots+b_n$. Q4 is labelled.
- Justification: The scan's layout is in two columns. The content of each
  condition was checked against the scan and against its use in (1.3).

### p. 344

**1978-31 · "$\sigma+d_i\mid X$ by B5" · TYPO.**
- OCR/scan: In the converse half of the proof of Lemma 2.7: "Similarly, $\sigma+d_i\mid X$ by B5."
- Reconstruction: "…by B6."
- Justification: B5 is the Pell-type square condition. B6,
  $X=\zeta(N-r)(\sigma+d_1)\cdots(\sigma+d_n)$, gives the divisibility, and the
  first half of the proof (p. 343) cites B6 correctly.

**1978-32 · Lemma 2.8, $X^Z$ · OCR.**
- OCR: `Y=\left[(X+1)^{N} / X^{z}\right]`.
- Scan: $Y=[(X+1)^N/X^Z]$ (upper-case $Z$, like the rest of Lemma 2.8).
- Reconstruction: $Y=\lfloor (X+1)^N/X^Z\rfloor$.
- Justification: The scan.

**1978-33 · A3, local multiplier $e\to e_0$ · CLAR.**
- OCR/scan: A3 reads $E=2(i+1)DC^2e$. The following text reads "The number $e$ in A3 may be any arbitrary positive integer. Since A3 and A4 imply $e\perp F$, … say $e\mid Q$, … $eF\mid QF+e(H-C)$". On p. 349: "If we take $e=M(u)$ in A3".
- Reconstruction: $e_0$ in all these places, including "If we take $e_0=M(u)$ in A3".
- Justification: $e$ is already a witness of the bounded quantifier ($z_2$ in
  U0/U7). Specializing the lemma's free multiplier to $M(u)$ must not read as a
  constraint on that witness. The renaming was silent until it was marked on
  24 September 2026 (78-R4-19) with one editorial note after Lemma 2.9 that
  covers all its occurrences, including the one on p. 349.

### p. 345

**1978-34 · "this condition may be dropped from A1 when using A1–A7" · TYPO.**
- OCR/scan: "As the condition $B\le C$ is expressed by T9, this condition may be dropped from A1 when using A1-A7 to define a partial binomial. Thus we shall need only three equations, Q2-Q4, to define T0."
- Reconstruction: "As the condition $B\le C$ is expressed by T9, Q1 may be dropped when using Q1–Q4 to define a partial binomial. Thus we need only the three equations Q2–Q4 to define T0. Likewise, $B\le C$ may be omitted from A1 when using A1–A7."
- Justification: The passage concludes the Q-system, and its conclusion (Q2–Q4
  suffice) is about dropping Q1. The A1 remark is true, and the collected system
  on p. 349 uses it, so it is kept as a separate sentence.

**1978-35 · "exponention" · TYPO.**
- OCR/scan: "Nowhere have we defined exponention." (as printed)
- Reconstruction: "exponentiation".

**1978-36 · Recursive definition of $P_k$ and the variable list · CLAR.**
- OCR/scan: "$P_0=0$, $P_{3i+2}=X_i$, $P_{3i}=P_{K(i)}+P_{L(i)}$, $P_{3i+1}=P_{K(i)}\cdot P_{L(i)}$." and "…all variables appearing in $P_k$ are included in the list $X_0,X_1,\cdots,X_{k-2}$."
- Reconstruction: The index ranges $(i\ge0)$, $(i\ge1)$, $(i\ge0)$ are stated. The list sentence ends "…$X_{k-2}$ when $k\ge2$; $P_0=P_1=0$."
- Justification: At $i=0$ the rule for $P_{3i}$ would read $P_0=P_0+P_0$, but
  $P_0$ is already defined, so $i\ge1$. For $k<2$ the list $X_0,\ldots,X_{k-2}$ is
  empty, and indeed $P_1=P_0\cdot P_0=0$. The additions were silent until
  they were marked on 24 September 2026 (78-R4-20) with an editorial note after
  "$P_0=P_1=0$".

### p. 346

**1978-37 · Two-index enumeration order · TYPO.**
- OCR/scan: "(equivalently $W_{1,0},W_{0,1},W_{1,1},\cdots$)".
- Reconstruction: "$W_{1,0},W_{0,1},W_{2,0},W_{1,1},\ldots$".
- Justification: $J(1,0)=1$, $J(0,1)=2$, $J(2,0)=3$ and $J(1,1)=4$, so $W_{2,0}=W_3$ is missing in the print.

**1978-38 · (3.2), missing parenthesis · TYPO.**
- OCR/scan: `S(R, \beta, L(i)]`.
- Reconstruction: $S(R,\beta,L(i))]$.

**1978-39 · Proof of necessity of Lemma 3.2, coding range · TYPO.**
- OCR/scan: "Choose positive integers $R,\beta$ so that $S(R,\beta,k)=P_k(X_0,\cdots,X_\tau)$, $(k=1,\cdots,3\tau+2)$. Then $S(R,\beta,0)=0$ …"
- Reconstruction: $(k=0,\ldots,3\tau+2)$.
- Justification: $S(R,\beta,0)=0$ does not follow from the other coded entries.
  It holds because $P_0=0$ is itself one of the coded values, so $k=0$ must be in
  the range of the Chinese-remainder coding.

### pp. 346–347 (the nonnegative-witness passage)

**1978-40 · Lemma 3.1 with nonnegative witnesses and the residues $S_+$ · CLAR.** See also 1978-06.
- OCR/scan: "Lemma 3.1 is also true if the integers $X_i$ are replaced by nonnegative integers. Hence 3.2 may be formulated in terms of least nonnegative residues. If we use the modulus $m(i)=1+i\beta$, then the condition $S(R,\beta,0)=0$ holds automatically and may be dropped. Also, $S(R,\beta,j)=v$ then has the simple definition $(\exists e,g)(R=v+e(1+j\beta)\wedge v+g=j\beta)$. Now if we let $s=K(i)$, $w=L(i)$, $p=S(R,\beta,s)$ and $q=S(R,\beta,w)$, then we may rewrite Lemma 3.2 in the form $x\in W_n\Leftrightarrow$"
- Reconstruction: "Lemma 3.1 is also true if the integer witnesses $X_i$ are replaced by nonnegative integers. Let $\widehat W_n$ denote the resulting enumeration, defined by the same polynomial equation but with $X_i\in\mathbb N_0$. This changes the indexing of sets in general; it does not change the fact that every r.e. set occurs. The analogue of Lemma 3.2 for $\widehat W_n$ uses least nonnegative residues. Write $S_+(R,\beta,i)$ for the least nonnegative residue modulo $m(i)=1+i\beta$. Then $S_+(R,\beta,0)=0$ automatically, and $S_+(R,\beta,j)=v\iff(\exists e,g)(R=v+e(1+j\beta)\wedge v+g=j\beta)$. Now put $s=K(i)$, $w=L(i)$, $p=S_+(R,\beta,s)$ and $q=S_+(R,\beta,w)$. The nonnegative-witness analogue of Lemma 3.2 becomes $x\in\widehat W_n\iff$ (3.3)", and (3.3) ends with "$\longrightarrow S_+(R,\beta,j)=v$".
- Justification: Both the modulus ($1+(1+i)\beta$ becomes $1+i\beta$) and the
  representative interval (centred becomes least nonnegative) change here. The
  name $S$ keeps its centred meaning for U2–U8, which follow. The enumeration also
  changes (1978-06). The reconstruction names both changes explicitly.
- Decision: the rewriting is kept. Unlike 1978-16, the printed passage
  is mathematically wrong as it stands, not merely loosely worded: it keeps the
  name $S$, defined on p. 346 as the absolutely least residue modulo $M(i)$, for a
  different residue function, and it concludes "$x\in W_n\Leftrightarrow$ (3.3)"
  for the integer-witness enumeration, which fails for $n=5$ (1978-06: $W_5$ is
  all positive integers, while (3.3) holds for no $x$). The rewriting was silent
  until it was marked on 24 September 2026 (78-R4-21). An editorial note at its
  first sentence quotes the whole printed paragraph (the display as a formula in
  line) and gives the $n=5$ failure.

**1978-41 · (3.3), bound of the universal quantifier · OCR.**
- OCR: `\forall i_{s n}`.
- Scan: $\forall i_{\le n}$.
- Reconstruction: $\forall i_{\le n}$.
- Justification: The scan. The delimiters of (3.3) are set as in 1978-05:
  $\{J(s,w)=i\wedge([\ldots]\longrightarrow S_+(R,\beta,j)=v)\}$.

**1978-42 · "We continue using Lemma 3.2." · CLAR.**
- OCR/scan: "We continue using Lemma 3.2. We also continue with the modulus $M(i)=1+(1+i)\beta$ rather than $m(i)$, …"
- Reconstruction: "We now return to the integer-witness enumeration $W_n$ of Lemma 3.2 and to its centered residues. We continue with the modulus …"
- Justification: This marks the return from $\widehat W_n$ and $S_+$ to $W_n$ and $S$ (1978-06, 1978-40).
  The rewording was silent until it was marked on 24 September 2026
  (78-R4-22) with an editorial note quoting the printed sentences.

**1978-43 · Page mark [347] in the rewritten passage · EDN.**
- Scan: p. 347 begins with "$w=L(i)$, $p=S(R,\beta,s)$ and …".
- Reconstruction: `[347]` is on the line "Now put $s=K(i)$, $w=L(i)$, …", the corresponding step of the rewritten text.

### p. 347

**1978-44 · $A(y)$ and $B(y)$: integer coefficients · ORIG.**
- OCR/scan: "In terms of $T$ and $P$ define polynomials $A(y)=[3J(s,w)-y]^2+[\ldots]^2$, $B(y)=[3J(s,w)+1-y]^2+[\ldots]^2$".
- Reconstruction: "…define the following integer-coefficient polynomials. In their first terms, the pairing denominators are cleared as in (1.3); this does not change their zero sets:" The first terms are $[3(s+w)^2+9w+3s-2y]^2$ and $[3(s+w)^2+9w+3s+2-2y]^2$. The second summands are unchanged.
- Justification: $2J(s,w)=(s+w)^2+3w+s$. So $J$ is integer-valued, but as a
  polynomial it has denominator 2. The BQT argument uses $P(r,\ldots)\equiv
  P(y,\ldots)$ when $r\equiv y$, which needs integer coefficients. A sum of two
  real squares vanishes iff both do, so the zero sets are unchanged. The corrected
  terms are exactly the first brackets already printed in (1.3.09), so the printed
  system needs no change. The majorant $Z^{90}$ stays valid (§7).

### p. 348

**1978-45 · Lemma 3.4, display label (3.4) · TYPO.**
- OCR/scan: The displayed predicate of Lemma 3.4 has no number. The proof of Lemma 3.5 (p. 348) cites "Condition (3.4)".
- Reconstruction: The display is tagged (3.4).
- Justification: The label is the one the article already cites, and no assertion is added.

**1978-46 · Lemma 3.5 statement: $u,v$ not quantified; lower-case $z$ in U0 · TYPO.**
- OCR/scan: "…there exist nonnegative integers $b,e,g,h,q,r,s,w,\beta,\pi,\theta$ and integers $J,P,R,T,T_1,Z$ such that U0. $q=\binom rz,\ q\mid\binom bz,\ldots,q\mid\binom wz$". U1 and U3 use $u,v$.
- Reconstruction: "$b,e,g,h,q,r,s,u,v,w,\beta,\pi,\theta$", and U0 has lower argument $Z$ in all six binomials.
- Justification: $u,v$ occur free in U1, U3 and U4, and the collected list on
  p. 349 includes them. Only $Z$ is defined in the lemma (U5), and $z=Z$ is
  identified only when collecting the system (1978-50).

**1978-47 · Remark after U0–U8 on the letters $J$ and $Z$ · CLAR.**
- OCR/scan: (absent)
- Reconstruction: "Here the scalar $J$ in U6 is distinct from the pairing function $J(u,v)$; $Z$ is the lower binomial argument throughout U0."
- Justification: U1 uses the pairing function $J(u,v)$ and U6 uses a scalar
  unknown $J=Z^6$. The print leaves the clash to the reader. The sentence
  accompanies the 1978-46 repair. It is a clarification and changes no condition.
  Since 24 September 2026 (78-R4-23) an editorial note says that the
  sentence is added and that the print has $z$ in U0 and omits $u,v$ from the
  list of unknowns (1978-46).

**1978-48 · Proof of necessity of Lemma 3.5: witness bound and sign of π · CLAR.** Rechecked independently and in Lean.
- OCR/scan: "It is not difficult to show that these numbers, when they exist, need never be as large as $T_1+R^3$. … The proof of the BQT shows how to find $b,e,g,s,w,\pi,T,P$ satisfying U7 and U8. The lemma is proved."
- Reconstruction: "By choosing the residue code $R$ sufficiently large, these witnesses can be chosen smaller than $T_1+R^3$. … The proof of the BQT shows how to find $b,e,g,s,w,T,P$ satisfying U7 and the divisibility in U8. The Chinese-remainder representative for $g$ may be increased by a multiple of $Z!q$ until $g\ge r$. This preserves the required congruences and binomial divisibilities, and makes the product in U8 nonnegative. Thus a nonnegative $\pi$ exists."
- Justification: The two points are these.
  - **Bound.** The residue code is not unique, and the bound holds only for a
    suitable choice. Choose the coded values and β first, and then $R$ large. A
    hand argument shows that $R\ge8\beta$ with $R$ dominating the
    $|T|,|P|,|T\pm P|,|TP|$ that occur is enough. Then Lemma 2.2 gives
    $0\le g\le\beta(1+4R^2)<R^3$, the division witnesses are $\le2R$, and at a
    free-variable node $C(y)=3g+2-y$ allows $g<n$. Lean proves it with the
    sufficient choice $R\ge V^2+10\beta+1$, where $V$ bounds the coded values.
  - **Sign.** Divisibility of the U8 product by $q$ does not make π
    nonnegative. With $g\ge r$, both linear factors $3g+2-r$ and $T_1+g-r$ are
    $\ge0$, and $A,B\ge0$ are sums of squares. The shift $g\mapsto g+kZ!q$
    keeps every congruence mod $q$. By Lemma 2.5 with $d=Z!q$ it also keeps
    $\binom{g}{Z}\bmod q$. Lean shifts all five witnesses above $r$; shifting $g$
    alone already suffices.
  - **Marking.** Both completions were silent until they were marked on
    24 September 2026 (78-R4-24) with one editorial note at the end of the
    proof, which quotes the two printed sentences.

### p. 349

**1978-49 · Collected conditions: "$z_1,\cdots,z_5$ replaced by $b,e,g,s,t$" · TYPO.**
- OCR/scan: "…hold with $z_1,\cdots,z_5$ replaced by $b,e,g,s,t$ respectively and $B\le C$ dropped from A1."
- Reconstruction: "…replaced by $b,e,g,s,w$ respectively …"
- Justification: The fifth witness of the bounded quantifier is $w$ (Lemma 3.4, U0). $t$ is used only later, for $T$.

**1978-50 · Collected conditions: $z=Z$, and which witness carries $z_1$ · CLAR.** Log: 78-R4-07 (parenthesis), 78-R4-25 (marking).
- OCR/scan: "…replaced by $b,e,g,s,t$ respectively and $B\le C$ dropped from A1."
- Reconstruction: "…replaced by $b,e,g,s,w$ respectively (Lemma 2.3 singles out $z_1$ in its condition (i) only by the choice of names; in U8 that factor is carried by $g$), with $z=Z$ and $B\le C$ dropped from A1."
- Justification: Read literally, "respectively" makes $z_1=b$. But U8 and (1.3.09)
  carry the factor $(T_1+g-r)$, so $z_1=g$, and the proof completion 1978-48
  assumes this as well. The BQT is symmetric in the names of the $z_i$ apart from
  condition (i), so this is harmless, and the parenthesis now says so. "$z=Z$"
  states the identification left implicit in the print (1978-46). Both
  additions were silent until they were marked on 24 September 2026
  (78-R4-25) with an editorial note that quotes the printed clause (with its $t$,
  1978-49).

**1978-51 · Combined divisibility condition · ORIG (marked by footnote).** Confirmed by repeated independent checks.
- OCR/scan: "We have only to replace $F\mid H-C$ in A1 by $FM(u)^2\mid M(u)(H-C)+F(hM(v)-x)^2$."
- Reconstruction: "$FM(u)^2\mid M(u)^2(H-C)+F(hM(v)-x)^2$". A footnote reads: "The first multiplier on the right is squared. The original prints only $M(u)(H-C)$, which is not an equivalent combination of the two divisibility conditions."
- Mark: since 24 September 2026 (78-R4-27) the footnote mark stands after
  "in A1 by", before the formula; directly after $(hM(v)-x)^2$ it read as part of
  the exponent.
- Justification: Write $M=M(u)$, $Q=hM(v)-x$ and $D_0=H-C$. With $e_0=M$, A3–A4
  give $F\equiv1\pmod{M^2}$, so $\gcd(F,M)=1$.
  - *The squared form is equivalent to U3 ∧ ($F\mid D_0$).* Modulo $F$, the
    condition gives $F\mid M^2D_0$, hence $F\mid D_0$. Modulo $M^2$ it gives
    $M^2\mid FQ^2$, hence $M^2\mid Q^2$, hence $M\mid Q$. Conversely, the two
    divisibilities make both terms divisible by $FM^2$.
  - *The printed form is not.* Take $M=9$, $F=163\equiv1\pmod{81}$, $Q=3$ and
    $D_0=1304=8\cdot163$. Then $MD_0+FQ^2=13203=FM^2$, so the printed
    condition holds and $F\mid D_0$, yet $9\nmid3$. So the printed form does not
    imply U3.
  - Conversely, take $M=2$, $F=3$, $D_0=-3$ and $Q=-8$. Both
    divisibilities hold, but $MD_0+FQ^2=186$ is not divisible by $12$. This
    example ignores the side condition $F\equiv1\pmod{M^2}$ and only illustrates
    that the printed form is not a general combination.

  The correction affects only this remark on universal pairs. (1.3) encodes U3
  separately ((1.3.03)), so none of its equations changes.

**1978-52 · "Calculation shows that the highest degree … will then be 690. Thus we obtain the universal pair $\nu=40,\delta=1380$." · CLAR (marked by footnote).**
- Reconstruction: "The original degree calculation reports a highest degree of 690 and hence the universal pair $\nu=40,\delta=1380$." A footnote says the omitted elimination and relation-combining calculations are not certified, and that the corrected combined-divisibility route (1978-51) has had no fresh degree audit. It contrasts this with the directly audited 36-equation system.
- Justification: The article omits these calculations ("extremely tedious"). The
  edition does not claim to have verified them. The 16 pairs of the table on
  p. 339 are kept as printed (§6).

**1978-53 · Final paragraph: "replacing conditions A1–A7 by the equivalent equations Q2–Q4" · CLAR.**
- OCR/scan: "…and replacing conditions A1-A7 by the equivalent equations Q2-Q4."
- Reconstruction: "…and replacing the Pell-sequence definition A1–A7 by the alternative definition Q2–Q4, using T9 for $B\le C$."
- Justification: Q2–Q4 are not equivalent to A1–A7 by themselves. They are
  equivalent only together with $B\le C$, which T9 supplies (compare 1978-34).
  The rewording was silent until it was marked on 24 September 2026
  (78-R4-26) with an editorial note quoting the printed phrase.

**1978-54 · The fifth square-condition unknown $\upsilon$ · OCR.**
- OCR: `The unknowns $\psi, \delta, \varepsilon, \nu, v$ were used …`
- Scan: In the scan's fonts the fifth letter can hardly be told apart from the
  article's italic $v$. The same holds in the typewriter setting of (1.3.27),
  whose right side is the square of this letter.
- Reconstruction: $\psi,\delta,\varepsilon,\nu,\upsilon$.
- Justification: $v$ is already an unknown, the second pairing coordinate in
  (1.3.01) and (1.3.03). The square condition T2 needs a *new* unknown, and 67
  unknowns are counted only when it is distinct from $v$. So the letter is read
  as Greek upsilon, in (1.3.27) as well. It was first classified as OCR together
  with 1978-55; it is really a glyph ambiguity resolved by the variable count.

**1978-55 · "the inequalities U4, 13" · TYPO.**
- OCR/scan: "The unknowns $\gamma,\iota$ express the inequalities U4, 13 …" (the scan prints "13").
- Reconstruction: "U4, T3".
- Justification: $\iota$ is the slack of (1.3.28),
  $5(c-\kappa\lambda y)^2+\iota=\kappa^2\lambda^2$, which is the strengthened T3.
  Equation (13) of Lemma 2.7 is a congruence, not an inequality.

### pp. 349–351 (references)

**1978-56 · [5], Russian translation · BIB.**
- OCR/scan: "… pp. 425–436 = *Matematika* 8:5 (1964), pp. 69–79."
- Reconstruction: "… = Matematika, vol. 8, no. 5 (1964), pp. 69–79."
- Justification: The same data in the style of the other entries.

**1978-57 · [6] "Dekalb" · BIB.**
- OCR/scan: "Dekalb, Illinois" (as printed).
- Reconstruction: "DeKalb, Illinois" (the city's spelling).

**1978-58 · [7] Gödel's title and journal · OCR + BIB.**
- OCR: `Kurt Godel,Über formal Unentscheidbare Sätze der Principia Mathematica und Verwandter Systeme I, Monatshefte Mathematik und Physik`.
- Scan: "KURT GÖDEL, *Über formal Unentscheidbare Sätze der Principia Mathematica und Verwandter Systeme I*, *Monatshefte Mathematik und Physik*". The umlaut is printed, and so are the capitals and the missing "für".
- Reconstruction: "Kurt Gödel, Über formal unentscheidbare Sätze der Principia Mathematica und verwandter Systeme I, Monatshefte für Mathematik und Physik".
- Justification: `Godel` and the missing space are OCR errors. The capitalization
  and the missing "für" are in the print, and the reconstruction corrects them
  (BIB) to the actual title and journal name.

**1978-59 · [8] and [26] "Mathematische-Physikalische Klasse"; [26] title · BIB.**
- OCR/scan: [8] and [26] both have "II. Mathematische-Physikalische Klasse". [26] also has "Zur theorie der quadratischen formen, Nachrichten der Akademie Wissenschaften in Göttingen" (as printed).
- Reconstruction: The class is "Mathematisch-physikalische Klasse" in both. [26] reads "Zur Theorie der quadratischen Formen, Nachrichten der Akademie der Wissenschaften in Göttingen".
- Justification: These are the correct German forms of the series and title names.

**1978-60 · [12] "in press" · BIB (marked by footnote).** Log: 78-R4-08.
- OCR/scan: "…Acta Arithmetica (in press)"
- Reconstruction: "…Acta Arithmetica (in press)." with the footnote "'In press' is the printed text; the paper appeared in Acta Arithmetica 35 (1979), pp. 209–221."
- Justification: History: an earlier revision embedded the gloss "(in press in
  the original bibliography)" in the entry. The printed text was then restored and
  the publication data moved to a footnote.

**1978-61 · [13] "Kosovskiĭ" · OCR.**
- OCR: `Kosovskǐ`.
- Scan: KOSOVSKIĬ (i with breve).
- Reconstruction: "Kosovskiĭ".

**1978-62 · [14] English page range 354–358 → 354–357 · BIB.**
- OCR/scan: "English translation: Soviet Mathematics. Doklady, vol. 11 (1970), pp. 354–358." (as printed)
- Reconstruction: "…pp. 354–357."
- Justification: Matiyasevich's own publication list (item [111]) and the 1982
  article support 354–357. The six articles disagree: 1974, 1982 and 1984 print
  354–357, while 1976, 1978 and 1980 print 354–358. The *JSL* Reviews record of
  the translation reads "Soviet mathematics, vol. 11 no. 2 (1970), pp. 354–357",
  with errata in vol. 11 no. 6, p. vi. On that basis 354–357 is adopted corpus-wide. The Russian range 279–282
  is unchanged.

**1978-63 · [21], [24], [25] "this JOURNAL" · BIB.**
- OCR/scan: "this JOURNAL" in all three.
- Reconstruction: "The Journal of Symbolic Logic".
- Justification: "This Journal" is meaningful only inside the *JSL* printing.

**1978-64 · [23] series name · BIB.**
- OCR/scan: "Proceedings of the Symposium on Pure Mathematics, vol. 20 (1971)" (as printed).
- Reconstruction: "Proceedings of Symposia in Pure Mathematics, vol. 20 (1971)".
- Justification: This is the title of the AMS series.

## 5. Editorial additions

Every addition to the article's text, with where it is justified. "Marked" means
that the text flags it as editorial (footnote "Editorial note." or a notice).

| Addition | Where | Marked? | Reason |
|---|---|---|---|
| Edition line, DOI, editorial-convention box, margin page numbers, (1.3.xx) numbers | front matter, throughout | yes (notice) | §3 items 2, 3, 6 |
| Footnote 2 source line and statement on the epigraph | p. 335 | yes | 1978-03 |
| "of positive integers", "for $x,n>0$" (Thms 1–2), "for $x>0$" (Lemma 3.1) | pp. 336, 345 | no | 1978-04 |
| $\widehat W_n$ notation | pp. 336, 346–347 | notice | 1978-06 |
| §3 paragraph defining $\widehat W_n$, $S_+$; return to $W_n$ | pp. 346–347 | yes (78-R4-21, 78-R4-22) | 1978-40, 1978-42 |
| "the same class … after the appropriate change of variables" | p. 337 | yes (78-R4-12) | 1978-10 |
| "effectively" (three times) | p. 338 | yes (78-R4-13) | 1978-15, 1978-17 |
| Qualification of the "absolute epistemological upper bound" sentence (printed sentence restored) | p. 338 | yes (78-R4-14) | 1978-16 |
| Corollary 1 title, certificate wording, footnote (241 sign count) | p. 338 | yes | 1978-17 |
| $n\ge1$ (Divisor Lemma, BQT), $z\ge1$, $R(z)\ge1$, $\max(1,\tau)$ | pp. 340–341 | yes (78-R4-15, 78-R4-16) | 1978-21, 1978-23 |
| Index range "for $1\le i\le n$" in the divisor chain | p. 341 | no | 1978-25 |
| Coprimality argument after (4) | p. 341 | yes (78-R4-17) | 1978-27 |
| "For $d>0$" (Lemma 2.5) | p. 342 | yes (78-R4-18) | 1978-28 |
| $e_0$ for the A3 multiplier | pp. 344, 349 | yes (78-R4-19) | 1978-33 |
| "Likewise, $B\le C$ may be omitted from A1…" | p. 345 | no | 1978-34 |
| Index ranges of $P_k$; "when $k\ge2$; $P_0=P_1=0$" | p. 345 | yes (78-R4-20) | 1978-36 |
| "integer-coefficient"; sentence on cleared pairing denominators | p. 347 | no | 1978-44 |
| $u,v$ in Lemma 3.5; remark on scalar $J$ and on $Z$ | p. 348 | yes (78-R4-23) | 1978-46, 1978-47 |
| Choice of $R$ for the witness bound; $g$-shift and $\pi\ge0$ | p. 348 | yes (78-R4-24) | 1978-48 |
| "with $z=Z$"; parenthesis on $z_1$ and $g$ | p. 349 | yes (78-R4-25) | 1978-50 |
| Footnote on the squared combined divisibility | p. 349 | yes | 1978-51 |
| "The original degree calculation reports…" and its footnote | p. 349 | yes (footnote) | 1978-52 |
| "using T9 for $B\le C$"; "alternative definition" | p. 349 | yes (78-R4-26) | 1978-53 |
| Footnote with the publication data of [12] | p. 351 | yes | 1978-60 |

The edition's convention is that every clarification is marked as editorial in
the text. Until 24 September 2026 only four editorial notes (1978-17, -51, -52,
-60), the notice and the epigraph footnote were marked, and the fifteen CLAR
entries 1978-10, -15, -16, -21, -23, -27, -28, -33, -36, -40, -42, -47, -48, -50
and -53 were silent. On that date each of them was given an editorial note at
the place of change, quoting the printed wording wherever it was replaced
(78-R4-12 to 78-R4-26); the edition now has 19 editorial notes. Of the two replacements of
the author's own sentences, 1978-16 is a philosophical claim and was restored verbatim with the
qualification in a note, while 1978-40 is mathematically wrong as printed and
keeps its rewriting, with the printed paragraph quoted in the note. The four
additions still marked "no" above are a stated domain (1978-04), a stated index
range (1978-25, TYPO), a separated remark (1978-34, TYPO) and the cleared
pairing denominators (1978-44, ORIG); they are documented here only.

## 6. Readings examined and retained

These were considered and left as they are, or were changed and then reverted.
There is no net discrepancy for any of them unless stated otherwise.

- **(1.3.09) B-factor modulus.** The scan prints $(1+\beta+\beta r)^2$ in the
  B-factor and $(1+\beta+r\beta)^2$ in the A-factor. The edition writes
  $(1+\beta+r\beta)^2$ in both. These are identical polynomials, recorded here
  only for completeness. It is the only non-identical spelling between
  the scan and the reconstruction of (1.3).
- **U8's factor $(T_1+g-r)$** is as printed. The BQT's $z_1$ is $g$ here (1978-50).
- **Pell forms.** A5 $G=A+F(F-A)$ and P5 $G=A+F^2(F^2-A)$ are both as printed. They
  belong to different lemmas and were not harmonized.
- **243 and 350 are kept.**
  - The print's count 243 is not changed. Counting signs gives 241
    (numeral coefficients counted as multiplications; 224 if numerals are free).
    The two missing signs were not located. See also §7.
  - $350-243=107=36+36+35$ charges one subtraction and one squaring per equation
    and 35 additions.
  - The promise to reduce the count to 149 in a future paper is kept as history.
- **Universal pairs table.** The 16 pairs are as printed and not re-derived. The
  intermediate degree 690 is reported only (1978-52).
- **Lemma 3.5, estimate $|A(y)B(y)C(y)|<Z^{90}$.** The estimate is correct with
  a wide margin. A hand derivation gives $<2\cdot10^{13}Z^{77}$ for $Z\ge30$,
  and a cruder bound gives about $Z^{86}$. Lean proves it and the chain
  $(2ZZ!Z^{90})^{Z^5}+Z\le Z^6-1+(Z^6)^{Z^6-2}$. Clearing the pairing
  denominators (1978-44) does not affect it.
- **"U2, U3 and U4 imply $2\le\beta$ and $3\le R$."** This is correct, but it
  uses the standing hypothesis $x>0$. If $\theta=0$, then $R=0$. With $h=0$, U3
  needs $M(u)\mid x$ although $0<x<\beta<M(u)$. With $h\ge1$, $hM(v)\ge1+\beta$
  violates U4 (checked by hand and in Lean). There is no edit.
- **Lemma 3.4.** The residue facts behind "∃g A(y)=0 …" hold for every
  $\beta\ge1$ in the sufficiency direction. "Provided β is sufficiently large"
  concerns only the converse. The case $u=0$ of $S(u)=S(v)+x$ needs a separate
  one-line argument (Lean). There is no edit.
- **Equations are read over ℤ.** The article says "all variables are nonnegative
  integers", but the subtractions in (1.3.04), (1.3.09), (1.3.19), (1.3.20),
  (1.3.30) and (1.3.36), and in Q4, are integer subtractions. Read with truncated
  natural-number subtraction, Q1–Q4 have spurious solutions. An example is
  $A=2,B=1,C=4,D=7,F=1,i=0,j=26,\tau=355$, where $C\ne\psi_2(1)=1$. In actual
  solutions of (1.3) the differences $\eta-r$, $\eta-z$, $\mu-1$, $\mu\chi-1$
  are nonnegative anyway (Lean). There is no edit; this is context only.
- **Lemma 2.8 and its variant.** Lemma 2.8 is cited from [20], and its variant
  $5(C-KLY)^2\le K^2L^2$, $M=9NXY$ is stated without proof. Both are correct:
  necessity was checked numerically on instances up to $(N,Z,X)=(5,3,600)$, and Lean
  proves both by the ratio method.
- **Lemma 2.4** is correct. The least $r$ for $J=2,\ldots,6$ is 2, 20, 244, 4060
  and 87814, against the bound $J-1+J^{J-2}=2,5,19,129,1301$.
- **Theorem 2.** Theorem 2 is the literal translation of Theorem 1. The witness
  $e$ is used by two principles in disjoint cases, so there is no clash.
- **Kept as printed:** the epigraph reference (chapter 11, verse 7), the dates
  "Received December 8, 1975; revised August 30, 1976", and "Lemma 2.2 … cf. [25]".
- **Historical statements** about best results, open problems (degree 3, $\nu=2$),
  "Forty-five years" and future work keep their 1978 meaning.
- **Uncited references.** [6], [15], [18], [19] and [22] are not cited in the
  text. They are uncited in the original too, and they are kept.
- **Further review.** The witness domains, the BQT and CRT arguments, the Pell
  congruences, the combined divisibility and the effectiveness hypothesis were
  reviewed again. No further change was found necessary.
- **Spelling and number checks.** A spelling check of all prose found no
  misspelling. A diff of all multi-digit numbers against the OCR found only the
  documented changes: 354–357, the (1.3.xx) numbers, and metadata.

## 7. Verification summary

*Programs.* The checkers are in `Papers/verification/`.
`jones1978_validation.py` reads the current source and passed on
24 September 2026.

- **System (1.3).** `Papers/verification/jones1978_validation.py` holds an
  independent SymPy transcription, and
  `Papers/verification/round4_1978_checks.py` (results in
  `Papers/verification/round4_1978_results.json`) re-types the system and
  compares it with the §3 construction. The results were:
  - 36 equations and 67 unknowns, with $x,n$ as parameters;
  - maximum degree 38, reached by (1.3.09);
  - degrees in order 2, 2, 3, 6, 3, 26, 3, 3, 38, 1, 6, 2, 2, 2, 2, 2, 2, 6, 7,
    2, 2, 2, 2, 2, 2, 4, 6, 6, 3, 2, 3, 2, 1, 4, 8, 12;
  - sum of squares of degree 76, since leading forms of squares cannot cancel;
  - "matches_section3_construction": true.
- **Lemmas.** Lemmas 2.1, 2.2, 2.5 and 2.6 and the pairing $J,K,L$ were checked by
  brute force. Finite regressions cover 6,138 cases of Lemma 2.2, 79,375 of the squared combined divisibility and 4,800 of Lemma 2.5.
  Lemma 2.8's necessity (both variants) was checked on eight instances. The
  counterexamples of 1978-51 and example 1978-06 were checked by hand again.
- **Lean formalization** (`Lean/Diophantine/Paper1978/`; the status table is
  `Lean/STATUS.md`). The following are machine-checked against Mathlib:
  - Theorems 1, 2 and 3 (`Jones1978.theorem_1`, `theorem_2`, `theorem_3`);
  - Lemmas 2.1–2.10, 3.1, 3.2, 3.4 and 3.5, including the omitted $Z^{90}$
    estimate;
  - the variant of Lemma 2.8.

  They cover the enumerations $W_n$ (integer witnesses) and $\widehat W_n$
  (nonnegative witnesses) of Diophantine sets of positive integers. That these
  enumerations contain every r.e. set is MRDP, supplied separately.
  `Jones1978.corollary_1` (`OperationCount.lean`) gives a fixed straight-line
  certificate for (1.3) with 241 instructions: 89 additions, 24 subtractions and
  128 multiplications, with numerals free, intermediates reused and 36 equality
  tests. The one-equation form costs 348 ≤ 350. This is an upper bound under that
  model and does not reconstruct the author's 243. The omitted degree calculation
  behind (40, 1380) is not formalized.
- **Not certified.** The following are not certified:
  - the historical universal-pair table and the degree 690;
  - the author's count 243 as such, and the future 149;
  - the proofs the article delegates to [11], [20] and [25] beyond what the Lean
    development proves.

  The operation-count analysis (the sign-count rule reproducing 87 and 100) is in
  the satellite article `Papers/1980/jones1980_theorem5_operations.pdf`. It is
  not an editorial note on this article.
