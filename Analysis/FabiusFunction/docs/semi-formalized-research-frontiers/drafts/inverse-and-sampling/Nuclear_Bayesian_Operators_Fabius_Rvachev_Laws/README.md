# Beyond Polynomial Diagonals
## Nuclear Bayesian Operators, Exact Null Modes, and a Rényi Phase Transition for Fabius–Rvachev Laws

Research article prepared for Vladimir Reshetnikov, 29 September 2026.

## Read the article

`article.pdf` is the compiled article; `article.tex` is the complete source with an inline bibliography. The figure source output needed by LaTeX is included under `figures/`.

The model is

    X_q = (1-q) sum_{j>=0} q^j U_j,       U_j iid Uniform[-1,1],
    S_{q,m} = (1-q) sum_{0<=j<m} q^j U_j,
    X_q = S_{q,m} + q^m X_q',
    C_m g(s) = E[g(X_q) | S_{q,m}=s].

The operator acts from L2(law X_q) to L2(law S_{q,m}). Those are different weighted Hilbert spaces.

## Principal proved results

- Membership in every Schatten class, with a fixed-q, fixed-m upper bound
  `limsup log(s_n)/(log n)^2 <= -1/(6 log(1/q))` for positive singular values.
- Dense range, a simple constant singular mode, and infinitely many exact Fourier/exponential-polynomial null modes.
- Factorially growing lower bounds on condition numbers of the polynomial restrictions, although every polynomial coefficient matrix is unipotent.
- Exact Appell intertwining, finite Jordan blocks, moment determinant ratios, exterior-power generating determinants, and a low-degree obstruction to elementary cyclotomic q-product formulas.
- A finite-variance Gaussian rigidity theorem, with an explicit strictly improving cubic correlation witness for geometric uniforms.
- Finiteness of all finite Rényi orders at each finite depth, but infinite order-infinity divergence.
- An exact critical order at alpha=2 in the large-depth excess `I_alpha - m log(1/q)`: an explicit finite limit for 1<alpha<=2, divergence for alpha>2.
- Exact collision information as the squared Hilbert–Schmidt norm, and the critical-depth asymptotic constant `log(2 integral f_q^2)`.
- A complete negative answer to rate-distortion optimality of prefix-only postprocessing at the original prefix's exact squared-error distortion.

The complete positive singular spectrum, the sharp decay constant, the growth rate above the critical Rényi order, and the full rate-distortion expansion are not claimed solved. Eight follow-up research questions appear in Section 12.

## Reproduce the calculations

Python 3.10+:

    uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 --with matplotlib==3.10.8 python verify.py --degree 18

The program writes `data/` and `figures/` under `rerun/` unless `--output-dir` is given; only `--output-dir .` overwrites the recorded files (see Editorial amendments).

The default run uses exact rational cumulants, moments, orthogonalization, and matrix inner products, followed by 100-decimal-digit numerical eigenvalue calculations. Numerical values are not interval-certified. `data/verification_report.json` records the executed checks. `data/polynomial_bounds.csv` retains exact fractions for the finite Hilbert–Schmidt trace lower bounds.

The article's table is an inline copy of the degree-18 output. Re-running at another degree changes the generated CSV/table fragment and figure, but does not automatically rewrite the explanatory prose or inline article table. The delivered article and data both use degree 18.

## Compile the PDF

A TeX Live installation providing newpx, amsmath, amsthm, mathtools, microtype, xurl, and the usual graphics packages is sufficient:

    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

No network access and no Python execution are required to recompile the delivered PDF from its included dependencies.

## Provenance and verification status

See `PROOF_AUDIT.md` and Section 13. Repository navigation was inspected at the commit recorded in the article. The detailed source-question wording came from the user's Library copy of `fabius_information_frontier.tex`; the article explicitly records that this copy is not byte-identical to the current repository file. The source report itself is not redistributed here.

These are self-contained mathematical proofs and reproducible checks, not a Lean formalization. No peer-review status, global priority, exhaustive literature search, or solution of the entropy-monotonicity conjecture is claimed. The independent mathematical arguments do not assume unverified repository theorems.

## File map

- `article.tex`, `article.pdf`: article source and rendered article.
- `verify.py`, `requirements.txt`: reproducible computation.
- `data/`: exact trace fractions, numerical diagnostics, generated table fragment, verification report, and run log.
- `figures/`: vector figure for LaTeX and PNG preview.
- `PROOF_AUDIT.md`: dependency and validation audit.
- `SHA256SUMS` (not kept): the delivered checksum ledger was verified in full (13/13) on filing (batch 56) and not kept; the delivered archive remains in the repository history (see `docs/incoming/README.md`, batch 56 row).

## Editorial amendments (ProveIt, 2026-09-29)

Made in the editorial pass after batch 56 of `docs/incoming/` (see `docs/incoming/README.md`); every change to the source is marked `% ed. (2026-09-29)`, every change to the program `ed. (2026-09-29)`.

- `article.tex`: an unnumbered environment "Editorial note (ProveIt, 2026-09-29)" is defined in the preamble. A note in Section 11.1 records that the information frontier `../fabius_information_frontier/` now carries an editorial note, directly after `prob:Bayesian-spectrum`, marking its expected `q^{mn}` Appell diagonal incorrect for `C_m` and citing this article (Proposition `prop:appell`), and that its README records the same erratum. A note at the end of the provenance paragraph of Section 13 records that the hexadecimal string there identifies a commit, not a tree; that the Library copy is byte-identical to the report as first archived on 30 August 2026; and that the three continued problems changed since only by renamings of notation macros.
- `article.pdf`: rebuilt from the amended source with `latexmk -pdf` (MiKTeX pdfTeX 1.40.29): 21 pages as delivered, no error, undefined reference or citation, duplicate destination, or overfull box; every font is embedded and none is Type 3 (the delivered PDF had one Type-3 `DejaVuSans` inherited from the Matplotlib figure). The pages carrying the notes were rendered and inspected.
- `figures/polynomial_spectra.pdf`: regenerated by the amended program (Matplotlib 3.10.8) with TrueType instead of Type-3 fonts; its rendering differs from the delivered figure only in glyph rasterization. `figures/polynomial_spectra.png` is kept as delivered (the font setting does not affect it).
- `verify.py`: new option `--output-dir`, default `rerun/`, so a plain run no longer overwrites the recorded `data/` and `figures/` (the article includes the figure); `--output-dir .` regenerates the recorded files. The CSV files are written with LF line endings (the delivered program wrote CRLF CSV files on every operating system), and the JSON report and `bounds_table.tex` with LF on Windows too; Matplotlib's `pdf.fonttype` and `ps.fonttype` are set to 42. `requirements.txt` stays unpinned as delivered; the pinned command above is the one used for the recorded outputs (the figure bytes depend on the Matplotlib version).
- `data/polynomial_bounds.csv`, `data/singular_values.csv`: delivered with CRLF line endings; normalized to LF on filing (batch 56).
- A rerun of the amended program on a copy (2026-09-29, the command above, Python 3.13.5) reproduced `data/polynomial_bounds.csv`, `data/singular_values.csv`, `data/verification_report.json` and `data/bounds_table.tex` byte for byte, and its standard output equals `data/run_log.txt` (which is captured console output; the program does not write it).
- `PROOF_AUDIT.md`: a dated amendment under the snapshot hash says that it is a commit and identifies the Library source, as in the article note.
- `README.md`: the reproduction command and output location, "commit" for "tree snapshot" under "Provenance and verification status", the retired ledger in the file map, and this section.
- Recorded, not changed: the PDF metadata title (`pdftitle`, "Beyond Polynomial Diagonals: Bayesian Operators for Fabius–Rvachev Laws") is shorter than the printed title; and notation clashes with the information frontier — here `J_q` is a Fisher constant and `V` the variance, there `J_q` is the surprisal and `V_q` the varentropy.
