# Sharp Euler-factor agreement for prime-order Dirichlet character packets

Research note dated 2026-11-27. Intended as a candidate addition to the ProveIt merged GRH article, especially `rec:sec:qmatch` and open question 6 in `rec:sec:open`.

## Deliverables
- `paper.tex` — complete LaTeX research note, including proofs, references and research questions.
- `paper.pdf` — compiled, visually checked nine-page note.
- `verify.py` — standalone exact-arithmetic checks (Python 3.8+, standard library only).
- `verification.txt` — output of the executed checker: 146,863 exhaustive packet-pair checks, 139 sharp base construction/Fourier norm checks, 21 lift and saturation checks.
- `phase_table.csv` — tabulation of the exact minimum (when proved sharp) or general lower bound for sample ranks and sizes. `sharp=false` means the bound is not proved attained here, not that it is unattainable.

## Reproduce

```
python3 verify.py
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
```

The proofs are human-readable mathematical proofs relying on the classical projective Reed–Muller minimum-distance theorem and the standard explicit formula. The checker is not a formal proof assistant. No Lean build was run for this note, and no upstream proof replay was undertaken. The density theorem is unconditional; the finite-prime estimates invoke only Dirichlet GRH (not Artin/Hecke/automorphic GRH). The full agreement spectrum and remaining sharp phases for larger primes are not resolved. No assertion of worldwide literature priority is made.

## Sources examined via GitHub

Repository: `VladimirReshetnikov/ProveIt`, branch `main`, directory `Analysis/GeneralizedRiemannHypothesis/`.

- `vendor/grh-lean/README.md` (blob a04f66a62af93fc0757f2aa573f3b053fde51bfa): vendored upstream revision 72fead102f663d5c7a407964a13dc0cf9d977207.
- `vendor/grh-lean/grh/README.md` (blob 68cd862687bac1dadf3f14dc7266365e5c8b1ec4): upstream theorem and reported verification scope.
- `vendor/grh-lean/grh/src/Statements.lean` (blob 1cd1bce93344065936b2b392b23306254e0785ef) and `src/Main.lean` (blob 1adf4187a938510363cdb0dde0a6d628ff39c600): exact exported statements.
- `Article/README.md` (blob 7f3286088c94a8df3d8b9846112ea83dbbbbfa25), `Article/article.tex` and `Article/sections/intro.tex`: scope and status of merged reports.
- Relevant sections `Article/sections/{rec,zer,li,ana,dir}.tex`: theorem and subsection inventories; matching and finite-detection proof and open questions from `rec.tex` directly examined. This is a targeted reading, not an audit of all 914 results or all 818 vendored files.
- Ghorpade and Ludhani, *On the minimum distance, minimum weight codewords, and the dimension of projective Reed-Muller codes*, Advances in Mathematics of Communications 18 (2024), 360–382, DOI 10.3934/amc.2023035; cited for the classical projective distance formula of Sørensen.

No repository modifications were made.
