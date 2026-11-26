# Beyond Dirichlet GRH: orthogonal kernels and sharp p-adic recovery

Prepared 26 November 2026 for Vladimir Reshetnikov.

## Main deliverable

Read `report.pdf`. Its complete LaTeX source is `report.tex` with the files in `sections/`.

The report develops three method transfers beyond ordinary RH/Dirichlet-GRH corollaries:

1. For uniform binary Q with Q^T Q = I, the maximum nullity over all principal submatrices has the upper tail
   `P(nu(Q) >= r) <= min(1, 6 * 2^(n-r*(r-1)/2))`.
   This rules out the linear-growth behavior proposed in Mathematics Stack Exchange question 5119604. It does not determine the exact typical order.
2. A sharp bound for Lubin–Tate multibranch recovery modulo pi^r, an exact base-p carry criterion for attaining it, and an exact all-precision formula for contact depths zero and one. This answers an explicit sharpness question in a previous ProveIt report.
3. Exact total-variation formulas for half-size blocks of split orthogonal matrices over fields of odd order. Rank parity is an optimal test for the special orthogonal group; full rank is optimal for the full group.

The proofs are mathematical derivations with exact finite checks. They are not claimed as new Lean-kernel-checked results. No new nonabelian GRH, Artin holomorphy, BSD, or matching binary-nullity lower bound is asserted. Worldwide publication priority has not been established.

## Reproduce the computations

Python 3.10 or later; standard library only. Run without `-O`, since assertions perform verification.

```bash
python3 code/check_binary_orthogonal.py
python3 code/check_binary_independent.py
python3 code/check_jets.py
python3 code/check_orthogonal_blocks.py
```

Each script writes its corresponding JSON result in `checks/`. The two binary implementations are independent and agree on every group order and maximum-nullity histogram for dimensions one through six. The first also checks quotient fibers and independent symplectic frame Gram classes.

Finite checks establish the advertised finite assertions only. The report's proofs establish the unbounded families. In particular, the binary upper tail is conservative and vacuous at the small dimensions enumerated.

## Rebuild the PDF

With a standard TeX Live installation:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
```

Or run `pdflatex report.tex` repeatedly until references stabilize. The document uses common TeX Live packages and no external figure assets or bibliography processor. All substantive mathematical arguments are in the TeX source.

## Evidence and archive layout

- `sources/source_manifest.json`: pinned upstream commit, selected source paths, hashes, and public links.
- `sources/prior_manifest.json`: the 52 prior archives, Git blob identities, SHA-256 hashes, and extracted-member inventory. The prior archives are not duplicated in this ZIP.
- `sources/prior_coverage.csv` and `sources/prior_audit.md`: comparison with earlier work, with review depth recorded.
- `sources/upstream/`: a small attributed source snapshot for the mechanisms used here, with license/notice files. It is not the complete upstream dependency closure and is not a standalone build of GRH.
- `checks/`: exact computation outputs, proof-review notes, and PDF verification summary.
- `formalization/plan.md`: a precise Lean-oriented implementation plan; not a claim of compiled formalization.
- `SHA256SUMS.txt`: checksums of the final archive contents other than this checksum file.

The upstream commit is `72fead102f663d5c7a407964a13dc0cf9d977207`.
The ProveIt snapshot is `9816644452bb42827167d6110e6d0322315a02b9`.
See the report's bibliography for primary literature, the posted question, and the exact prior packets.
