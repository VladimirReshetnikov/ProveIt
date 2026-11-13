# Independent review of the natural-79 decimal render candidate

The revised [candidate TeX/PDF](../../research/ordinary14-natural79-decimal-render-candidate/README.md)
and this read-only independent checker agree on the checked graph rows, decimal
seed and four coefficient values. The author's PDF extraction receipt also
reproduces. No concrete mathematical transcription error was found in these
checks. This is an external source, integer and PDF-text comparison, not Lean
elaboration or formal document semantics.

The 14 nonnegative inputs are distinct: `J,F,A,f,i,T,w,s,r,e,z,y,g,h`. The
revised coefficient formulas use bound indices `j` and `k` and the fixed slot
sequence `λ_j`, avoiding reuse of the free inputs `i` and `s`. All written
numerals and the complete selector seed use decimal notation; the fixed
coefficient definitions still legitimately use the power radix `ρ=2^67`.
The enormous four coefficients are specified by finite formulas, rather than
printed as four fully expanded decimal integers.

The checker independently parses all 79 binary-operation rows from the pinned
Lean graph source and compares them with the graph inventory, every TeX
abbreviation and every PDF-extracted graph row. It checks the distinct input
and port-position mappings and the final `vout=0` equation. The PDF text
comparison normalizes a known extraction limitation: `pdftotext -raw` turns
the underscores in monospaced identifiers such as `vguard_base` into spaces.
The underscores are visible in the inspected first-page rendering, but copied
text should not be treated as a faithful machine-readable graph. Exponent and
other mathematical layout can likewise be flattened by PDF text extraction.

The displayed 15,086-digit seed matches the TeX and PDF extraction exactly.
Its 943 right-to-left, zero-padded decimal blocks agree in order with selector
values independently computed from the pinned 943 Lean table rows. The 41
printed slot values match the pinned source list. Independently evaluating the
displayed β, K, μ and ω formulas yields exactly the four retained P72 raw byte
values, including adding β to the high part **once**. This compares exact
integers and retained hashes; it does not prove inside Lean that displayed
formulas or physical files denote those integers.

Visual inspection of page one found the graph and coefficient definitions
legible at the rendered scale. The three-page seed section uses small type, as
the candidate notes, and is better checked or copied as the supplied decimal
text. The page is marked source-only. The natural-79 endpoint, the four Lean
port-equality assumptions, the TeX/PDF parser and rendering semantics, and the
iPRA equivalence remain separate unproved obligations. The candidate does not
replace the maintained `equation.tex` or `equation.pdf`.

From the repository root, with the retained coefficient files and `pdfinfo`
and `pdftotext` available:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary14-natural79-decimal-render-candidate/verify_render.py | cmp - Computability/DiophantineConsistency/research/ordinary14-natural79-decimal-render-candidate/render-result.json
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural79-decimal-render-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural79-decimal-render-independent/result.json
```
