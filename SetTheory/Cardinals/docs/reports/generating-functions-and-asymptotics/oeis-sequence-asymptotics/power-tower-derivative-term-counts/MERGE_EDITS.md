# Every edit made to the three source texts

This package merges three separately delivered reports into one article.  The
three originals are reproduced as Parts 2, 3 and 4, and the merge was
constrained: apart from four mechanical transformations, **nothing in them was
changed except the edits listed here**.

The mechanical transformations, applied uniformly by script:

1. Strip each source's own front matter (title, author, date, its own table of
   contents).  Each source's abstract was *not* discarded - it is reproduced
   verbatim in the box that opens its part.
2. Demote headings one level, so each source's sections become subsections of
   its part.
3. Prefix every `\label` (`xx:`, `xxb:`, `xxc:`) and rewrite every `\ref`,
   `\eqref` and friends to match.
4. Merge the three preambles and the three bibliographies.

Everything else is below.  The check is mechanical and repeatable: re-apply the
four transformations and these edits to the pristine sources and the result is
byte-identical to the corresponding part of `article.tex`.  That check was run.

No theorem, lemma, proposition, corollary, definition, conjecture or remark was
touched.  All fifty of them - eighteen, twenty and twelve - are present with
their statements unchanged.


## Part 2 --- A293239 (`x^x`)

### Edit 2.1

A plain-text section number the merge invalidated: Section 1 of the standalone report was 'The question and the status of the answer'; Section 1 of the merged article is 'The common framework'. Every \ref was rewritten automatically; this number was prose.

```diff
- This proves the range correction asserted in Section 1.
+ This proves the range correction asserted at the start of this part.
```

### Edit 2.2

Script moved into code/ in the merged package.

```diff
- The standard-library program \texttt{verify\_diagonals.py} reconstructs
+ The standard-library program \texttt{code/verify\_diagonals.py} reconstructs
```

### Edit 2.3

Commands updated for the merged code/ layout; both were run and pass.

```diff
- python3 verify.py --max-n 1500 --data-dir data\\
- python3 verify\_diagonals.py --output-dir data --check-only
+ python3 code/verify.py --max-n 1500 --data-dir data\\
+ python3 code/verify\_diagonals.py --output-dir data --check-only
```

### Edit 2.4

Source moved into code/ in the merged package.

```diff
- c++ -O3 -std=c++17 verify\_gmp.cpp -lgmpxx -lgmp -o verify\_gmp
+ c++ -O3 -std=c++17 code/verify\_gmp.cpp -lgmpxx -lgmp -o verify\_gmp
```


## Part 3 --- A290268 (`x^(x^2)`)

### Edit 3.1

The generic key 'oeis' was ambiguous beside three other OEIS entries in the merged bibliography.

```diff
- cite{oeis}
+ cite{oeis290268}
```

### Edit 3.2  **(major)**

\appendix is document-global. Harmless as the last structural command of a standalone article; in the merged article it switched every later section to appendix numbering, so the A281434 part printed as 'Appendix A' and the synthesis section collided with it, duplicating four subsection numbers and their hyperref anchors.

```diff
- 
- \appendix
- \subsection{Reproducing the computations}
+ 
+ \subsection{Reproducing the computations}
```

### Edit 3.3

The article file names changed in the merge.

```diff
- \texttt{A290268\_partial\_results.tex} & Complete article source.\\
- \texttt{A290268\_partial\_results.pdf} & Compiled article.\\
- 
+ \texttt{article.tex} & Complete source of the merged article; this part is its Part~3.\\
+ \texttt{article.pdf} & The compiled merged article.\\
+ 
```

### Edit 3.4

The checksum manifests were deleted from every package in this collection by an earlier decision: a stored hash goes stale on the first rebuild. The file table still advertised one.

```diff
- \texttt{SHA256SUMS.txt} & Integrity checks for the distributed files; these are not mathematical proof certificates.\\
- 
+ (line removed)
```


## Part 4 --- A281434 (`x^(x^x)`)

### Edit 4.1  **(major)**

Second document-global \appendix; see the A290268 entry. This one reset the section counter again, giving the synthesis section the same number and anchors as this part.

```diff
- 
- \appendix
- \subsection{A compact exact implementation}
+ 
+ \subsection{A compact exact implementation}
```

### Edit 4.2

Consequent on the \appendix removal: the target is now a subsection of this part, not an appendix.

```diff
- Appendix~\ref{xxc:app:code}
+ Section~\ref{xxc:app:code}
```

### Edit 4.3

The source set language=Python globally in its preamble; the merged preamble cannot, because the A290268 part's listing is shell. Marking the one Python listing restores the source's rendering. The other two A281434 listings already carry language={}.

```diff
- \begin{lstlisting}
- from collections import defaultdict
+ \begin{lstlisting}[language=Python]
+ from collections import defaultdict
```


---

11 distinct edits across 2415 lines of source text.  One of them, the
bibliography key, applies at two places; the rest apply once each.

Two were not cosmetic.  Both `\appendix` removals were forced.  The command is
document-global, so a source that ends with one is harmless on its own but,
placed mid-document, switches every later section into appendix numbering.  Left
in, they made Part 4 print as "Appendix A" while its siblings were 2 and 3, gave
the closing part the same number *and the same PDF anchors* as Part 4, and so
silently redirected every cross-reference into the closing part.  The article
compiled without a single error or undefined reference in that state, which is
the reason this record exists.
