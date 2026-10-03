# Uniform Smoothing and Commensurate Observation Masks

A seven-page mathematical continuation of Universal Comparison of Fabius Observation Masks.

The report proves an exact criterion for finite commensurate masks of unequal cardinalities: the source must have at least as many coordinates as the target, the q-integer denominator must divide the numerator, and an explicitly given signed cardinal spline must be nonnegative. Exponential tilting does not change its sign.

A direct application of classical Polya positivity, using the half-unit digit decomposition of a uniform variable, proves that a finite signed lattice measure becomes nonnegative after sufficiently many unit-uniform convolutions exactly when its polynomial is positive on the positive real axis. Consequently a finite number of additional base-cap source observations permits universal mask domination exactly when the denominator polynomial divides the numerator, equivalently when all nontrivial cyclotomic divisor counts are nonnegative.

For P(u)=1-u+u^2, the least uniform-smoothing order is exactly nine. The report includes all six Bernstein rows needed by symmetry, the negative order-eight value -17/2520, and a separate order-eleven half-step coefficient certificate. Thus nine additional h-cap observations are necessary and sufficient to upgrade source caps (h,6h) to dominate target caps (2h,3h), uniformly over all common real tilts and all total-sum weights.

## Files and reproduction

- uniform_smoothing_mask_stabilization.pdf: complete report
- uniform_smoothing_mask_stabilization.tex: editable source
- build.sh: standard TeX Live build
- SOURCES.md: references and exact repository context
- validation.json: artifact verification and exact-check summary
- checks/verify_stabilization.py: Python standard-library certificate checker
- checks/stabilization_certificates.json: all eleven exact Bernstein rows, the order-eight obstruction, the half-step certificates, and algebraic results
- checks/verification.log: recorded checker output
- SHA256SUMS: integrity manifest (retired on filing; not in the repository)

Run `bash build.sh` to rebuild the PDF with standard TeX Live. (Since the editorial amendments of 2026-10-01 below, the checker writes to
`checks/rerun/`; `build.sh` runs `pdflatex` in this directory and overwrites the
filed PDF, so build on a copy.) Run `python3 checks/verify_stabilization.py` for the exact arithmetic checks. These verify the sharp order-nine certificate by two independent Bernstein coefficient computations, reflection and integral one, 1,344 normalized-coefficient identities, and 7,056 polynomial-divisibility cases. The general eventual-positivity proof is analytic. The report describes a terminating algorithm for arbitrary rational data; the included checker verifies its formulas and the displayed example rather than implementing a general-purpose Sturm solver.

## Attribution and scope

Polya's theorem and the eventual positivity of polynomial coefficient measures have classical antecedents, explicitly cited. No general priority claim is made. All comparisons require one observation kernel valid for the entire total-sum weight or threshold family; they do not decide every isolated two-hypothesis comparison. The arguments are ordinary mathematical proofs, not formalized or externally refereed results.

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

- `uniform_smoothing_mask_stabilization.tex`: an unnumbered environment `ednote` ("Editorial note (ProveIt,
  2026-10-01)") is defined after the theorem environments (no counter
  changes). Two notes:
  - at the end of Section 5: at `r = 0` Theorem 1.1 is Theorem 3.1 of the
    preceding note `../Universal_Fabius_Mask_Criterion/`, and (2) is that
    note's Theorem 1.1. The quotient `1 - u + u^2` of Theorem 5.1 is the
    base-six obstruction of `thm:base6` of
    `../../spectra-and-arithmetic/Simultaneous_Convolution_Divisors_Fabius_Type_Laws/`
    and `prop:base6` of
    `../../spectra-and-arithmetic/Arithmetic_Rigidity_off_Resonance_Geometric_Uniform_Laws/`,
    which neither note cites: there the two largest source uniforms have
    lengths `6h` and `h` (`h = 1/3`, respectively `1/6`) and the targets `3h`
    and `2h`, and the signed factor `delta_{-h} - delta_0 + delta_h` (the
    measure `eta_P` scaled by `h` and centred) is convolved with the
    remaining geometric tail, which is supported on an interval shorter than
    `h` and leaves a negative central mass, whereas nine uniforms of length
    `h` remove it and eight do not;
  - at the end of Section 6, a series map: the eight notes in the order
    written (this is the fourth); `Masks` (source
    `universal_fabius_mask_criterion.tex`) is
    `../Universal_Fabius_Mask_Criterion/`.
- `uniform_smoothing_mask_stabilization.pdf`: rebuilt from the amended source with three `pdflatex` passes
  (MiKTeX 26.2, pdfTeX 1.40.29): 7 A4 pages, as delivered, 387,875 bytes; all 21
  fonts embedded, none Type 3; the final log has no error, overfull or
  underfull box, undefined or multiply defined reference, duplicate
  destination, or rerun request. The pages carrying the notes were rendered
  and inspected.
- Reciprocal notes of 2026-10-01 now stand after `thm:base6` of the first
  `spectra-and-arithmetic/` article named above and after the question
  "Composite reciprocal returns" of the second.
- `checks/verify_stabilization.py`: new option `--output-dir`.
  As delivered, the program overwrote the recorded file beside itself, with
  CRLF line endings on Windows; it now writes `checks/rerun/stabilization_certificates.json` (or
  `<output-dir>/stabilization_certificates.json` with `--output-dir`), with LF line endings. Pass
  `--output-dir` with the program's own directory, on a copy, to regenerate
  the recorded file. On the ProveIt machine use `py` rather than `python3`.
  A rerun of the amended checker on a copy (2026-10-01,
  `py checks/verify_stabilization.py`, Python 3.14.4, standard library) wrote
  `checks/rerun/stabilization_certificates.json` equal to the recorded file
  byte for byte, and its console output equals `checks/verification.log`
  after CRLF-to-LF conversion.
- `build.sh`: kept as delivered. It runs `pdflatex` three times in this
  directory, so it overwrites the filed PDF and leaves `.aux`, `.log` and
  `.out` files here: build on a copy.
- `validation.json`: unchanged (the page count is still 7).
- `README.md`: the retired ledger under "Files and reproduction", the
  parenthesis after the build command, and this section.
