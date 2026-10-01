# A Uniform Second-Order Profile for Proportional Fabius Masks

This seven-page research note answers the geometric proportional-regime part of the repository's q:rates and q:edgeworth questions. The arbitrary-mask Gaussian limit, TV profile and forward-KL limit were already proved in the source and are explicitly credited.

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
- `SOURCES.md`, `validation.json`, `SHA256SUMS`: provenance and artifact verification

Run the two symbolic scripts with Python 3. Run `python3 checks/check_proportional_tv.py --output checks/numerical_results.json` for the optional floating-point checks. The latter are not rigorous asymptotic error certificates. Run `bash build.sh` to rebuild the PDF.

The uniform error is proved analytically in the manuscript, including signed measures, central and tail estimates, product transfer, and the moving TV boundaries. Ordinary mathematical proof is distinguished from formal verification and external peer review; no worldwide priority claim is made.
