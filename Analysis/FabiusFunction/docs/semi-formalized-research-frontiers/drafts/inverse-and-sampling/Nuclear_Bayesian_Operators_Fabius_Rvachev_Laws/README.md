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

    python -m pip install -r requirements.txt
    python verify.py --degree 18

The default run uses exact rational cumulants, moments, orthogonalization, and matrix inner products, followed by 100-decimal-digit numerical eigenvalue calculations. Numerical values are not interval-certified. `data/verification_report.json` records the executed checks. `data/polynomial_bounds.csv` retains exact fractions for the finite Hilbert–Schmidt trace lower bounds.

The article's table is an inline copy of the degree-18 output. Re-running at another degree changes the generated CSV/table fragment and figure, but does not automatically rewrite the explanatory prose or inline article table. The delivered article and data both use degree 18.

## Compile the PDF

A TeX Live installation providing newpx, amsmath, amsthm, mathtools, microtype, xurl, and the usual graphics packages is sufficient:

    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

No network access and no Python execution are required to recompile the delivered PDF from its included dependencies.

## Provenance and verification status

See `PROOF_AUDIT.md` and Section 13. Repository navigation was inspected at the tree snapshot recorded in the article. The detailed source-question wording came from the user's Library copy of `fabius_information_frontier.tex`; the article explicitly records that this copy is not byte-identical to the current repository file. The source report itself is not redistributed here.

These are self-contained mathematical proofs and reproducible checks, not a Lean formalization. No peer-review status, global priority, exhaustive literature search, or solution of the entropy-monotonicity conjecture is claimed. The independent mathematical arguments do not assume unverified repository theorems.

## File map

- `article.tex`, `article.pdf`: article source and rendered article.
- `verify.py`, `requirements.txt`: reproducible computation.
- `data/`: exact trace fractions, numerical diagnostics, generated table fragment, verification report, and run log.
- `figures/`: vector figure for LaTeX and PNG preview.
- `PROOF_AUDIT.md`: dependency and validation audit.
- `SHA256SUMS`: checksums of the package files.
