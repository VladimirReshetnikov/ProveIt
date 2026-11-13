# 84-operation 2011 display

`equation84-2011.tex` and its one-page PDF display the exact thirteen-positive-variable, 84-operation, degree-92 corrected unit-sphere candidate. The 84 binary operations count the positive-input graph, not the expanded `positiveShift` syntax used by the internal iPRA statement. The selected Foundation consistency encoding and its translation are documented in `research/thirteen84-model-binding`; no global minimum is claimed.

`check_display.py` parses the displayed 25 polynomial abbreviations and boxed equation as exact sparse polynomials, comparing each cut with the pinned 84-row graph and its output wiring. It checks the 13 distinct positive unknowns, exact displayed metrics, and the fixed-integer/decimal-seed block against both the existing fourteen-variable display and the SHA-256 of the independently reviewed 69-operation display's block. Five negative controls mutate the rank, ordinate, correction, final constant and degree caption. It does not formalize TeX/PDF rendering or independently re-prove the fixed-block decoder; those boundaries are inherited from the 69-operation display review. Exact degree 92 for the full 2011 tuple was checked separately in `reviews/thirteen84-degree2011-independent-audit`; the Lean graph/iPRA binding was independently reviewed in `reviews/thirteen84-model-binding-independent-audit`.

The checker exited 0 using:

```
python3 -I -S Computability/DiophantineConsistency/reviews/equation84-2011-display/check_display.py
```

The PDF was generated twice with `SOURCE_DATE_EPOCH=0 TZ=UTC pdflatex -interaction=nonstopmode -halt-on-error` in separate output directories. Both builds exited 0 and were byte-identical, one letter-sized page, with no overfull or underfull box warnings. The inherited small-font layout produced three font-substitution notices. The author also visually inspected the page; independent review remains pending.

- TeX SHA-256: `7fc6ad1fcb7620f9c349f3b2a7c918c3f26d0c5bc4cc6c420c6484c2d8ddc954`
- PDF SHA-256: `8190c8827b478f4f5ad5f8d45e1fdf279cff6894a17120913e0992390d93b534`
- Checker SHA-256: `bd3334c3e4c6d53346441d9b29d60c952646189627c8fd6952a2daa6b927e7d1`
- Graph SHA-256: `a214fc19ea776e4e3880e13a7cd92260e76e71588c8c6b391669007a180ab3be`
