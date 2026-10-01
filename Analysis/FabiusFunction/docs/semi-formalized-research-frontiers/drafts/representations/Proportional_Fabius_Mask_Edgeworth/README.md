# A Uniform Second-Order Profile for Proportional Fabius Masks

This research note (eight pages since the editorial amendments below; seven
as delivered) answers the geometric proportional-regime part of the repository's q:rates and q:edgeworth questions. The arbitrary-mask Gaussian limit, TV profile and forward-KL limit were already proved in the source and are explicitly credited.

The new result is a uniform second-order total-variation expansion with O(n^(-3/2)) error, for fixed geometric parameters and hidden bulk fractions in an interior compact interval. Arbitrary finite/countable mask and tail membership is allowed. At order 1/n, geometry enters only through hidden and observed variance defects. Equivalently, the expansion has a universal correction when expressed using the true variance fraction and total variance.

The report gives an explicit same-count mask comparison and a positive phase-dependent 1/n separation of the canonical early-hidden and late-hidden overlaps. It also records the precise divergence scope: positive finite forward Renyi orders and forward KL converge, while reverse KL is infinite for all sufficiently large finite n. Fractions approaching 0 or 1 and higher-order entropy corrections are outside the theorem.

## Files and reproduction

- `proportional_mask_edgeworth.pdf`: complete mathematical report
- `proportional_mask_edgeworth.tex`: editable LaTeX source
- `build.sh`: three-pass ordinary TeX Live build
- `checks/verify_tv_coefficient.py`: exact symbolic density-mass and TV coefficient checks using SymPy
- `checks/independent_tv_reconstruction.py`: separate exact reconstruction from cumulants/Hermite terms, also using SymPy
- `checks/check_proportional_tv.py`: Gamma/Beta and one-cap floating-point regression checks using NumPy/SciPy
- `checks/numerical_results.json`: all 30 finite-n evaluations and 9 passing regression cases
- `checks/README.md`: numerical reproduction and limitations
- `SOURCES.md`, `validation.json`, `SHA256SUMS`: provenance and artifact verification (`SHA256SUMS` retired on filing; not in the repository)

Run the two symbolic scripts with Python 3. Run `python3 checks/check_proportional_tv.py --output checks/numerical_results.json` for the optional floating-point checks. The latter are not rigorous asymptotic error certificates. Run `bash build.sh` to rebuild the PDF. (Since the editorial amendments of
2026-10-01 below, the scripts write to `checks/rerun/` by default; the command
above, with an explicit `--output`, still overwrites the recorded file, so run
it on a copy. `build.sh` runs `pdflatex` in this directory and overwrites the
filed PDF, so build on a copy.)

The uniform error is proved analytically in the manuscript, including signed measures, central and tail estimates, product transfer, and the moving TV boundaries. Ordinary mathematical proof is distinguished from formal verification and external peer review; no worldwide priority claim is made.

## Editorial amendments (ProveIt, 2026-10-01)

Made in the editorial pass after batch 72 of `docs/incoming/` (see
`docs/incoming/README.md`); every change to the source is marked
`% ed. (2026-10-01)`, every change to a program `ed. (2026-10-01)`. The
mathematical text is unchanged; the byline and `pdfauthor` entry ("Research
note prepared for Vladimir Reshetnikov with OpenAI") are kept as delivered.
The eight notes of the series are filed beside one another, in the order
written: `../Exact_Fabius_Mask_Order/`, `../Universal_Garbling_Classification/`,
`../Universal_Fabius_Mask_Criterion/`, `../Uniform_Smoothing_Mask_Stabilization/`,
`../Arithmetic_Geometric_Mask_Order/`, `../Exact_Fixed_Conditioning_Order/`,
`../Strict_Fabius_Conditioning_Order/`, `../Proportional_Fabius_Mask_Edgeworth/`.

- `proportional_mask_edgeworth.tex`: an unnumbered environment `ednote` ("Editorial note (ProveIt,
  2026-10-01)") is defined after the theorem environments (no counter
  changes). Two notes:
  - after the first paragraph of Section 1: the source `Repository` is
    `../Sharp_Conditioning_Laws_Uniform_Random_Series/`; its `q:edgeworth` is
    answered here at order `1/n` for geometric weights and hidden fractions in
    a fixed `[delta, 1 - delta]`, but `q:rates` only in part, since it asks for
    bounds uniform as the complement fraction tends to zero, whereas the
    rates here hold for a fixed `delta`. In
    that article's notation (`V = V_T`, observed variance fraction
    `alpha_t = 1 - xi`) the leading term `V(xi)` of (5) is its profile
    `Delta(alpha_t)`, and the exact likelihood (7) is its block likelihood
    ratio (6.1), with the normalization `J(t)` of its Theorem 5.1;
  - at the end of Section 7, a series map: the eight notes in the order
    written (this is the eighth and last); `Critical` (source
    `Second_Order_Fabius_Crossover.tex`) is the second-order article
    `../Second_Order_Critical_Complements_Fabius_Conditioning/` (batch 71),
    whose (5.1) and (5.2) are the signed measures and the product bound (9)
    here, as are (4.1) and Lemma 4.1 of its source
    `../Critical_Complements_Sharp_Information_Loss/`; `Strict` is
    `../Strict_Fabius_Conditioning_Order/`, whose strict order (its
    Corollary 4.2, every `n >= 2`) Corollary 5.2 here quantifies in the
    proportional regime.
- `proportional_mask_edgeworth.pdf`: rebuilt from the amended source with three `pdflatex` passes
  (MiKTeX 26.2, pdfTeX 1.40.29): 8 A4 pages (7 as delivered), 388,853 bytes; all 22
  fonts embedded, none Type 3; the final log has no error, overfull or
  underfull box, undefined or multiply defined reference, duplicate
  destination, or rerun request. The pages carrying the notes were rendered
  and inspected.
- Reciprocal notes of 2026-10-01 now stand after `q:rates` and
  `q:edgeworth` of `../Sharp_Conditioning_Laws_Uniform_Random_Series/` and
  after Corollary 3.3 of
  `../Second_Order_Critical_Complements_Fabius_Conditioning/`.
- `checks/verify_tv_coefficient.py`: new option `--output-dir`.
  As delivered, the program overwrote the recorded file beside itself, with
  CRLF line endings on Windows; it now writes `checks/rerun/tv_coefficient_symbolic.json` (or
  `<output-dir>/tv_coefficient_symbolic.json` with `--output-dir`), with LF line endings. Pass
  `--output-dir` with the program's own directory, on a copy, to regenerate
  the recorded file. On the ProveIt machine use `py` rather than `python3`.
- `checks/check_proportional_tv.py`: the default of `--output` is now
  `checks/rerun/numerical_results.json` (it was the recorded
  `checks/numerical_results.json`), written with LF line endings.
  `checks/independent_tv_reconstruction.py` writes nothing and is unchanged.
  Reruns of the amended programs on a copy (2026-10-01): with
  `uv run --no-project --with sympy==1.14.0 python` (Python 3.13.5) both
  symbolic scripts passed, and `checks/rerun/tv_coefficient_symbolic.json`
  equals the recorded file byte for byte; with
  `uv run --no-project --with numpy --with scipy python` (NumPy 2.5.3,
  SciPy 1.18.1; the recorded file names Python 3.12.14, NumPy 2.3.5, SciPy
  1.17.0) all 9 regression checks passed, and every number in
  `checks/rerun/numerical_results.json` agrees with the recorded file within
  1.4e-11 in absolute value; only the environment entries differ. No
  requirements file pins SymPy, NumPy or SciPy.
- `checks/README.md`: a parenthesis after its command.
- `build.sh`: kept as delivered. It runs `pdflatex` three times in this
  directory, so it overwrites the filed PDF and leaves `.aux`, `.log` and
  `.out` files here: build on a copy.
- `validation.json`: `pages` set to 8; its other entries are as delivered.
- `README.md`: the page count, the retired ledger under "Files and
  reproduction", the parenthesis after the build command, and this section.
