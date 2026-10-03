# Universal Garblings of Tilted Uniform Observations

A self-contained mathematical companion (six pages since the editorial
amendments below; five as delivered) to Exact Observation Order for Fabius Conditioning.

The main theorem classifies one Markov kernel that must work under every total-sum reweighting: two independent truncated exponentials admit such a kernel exactly when their real tilt parameters agree and the source cap is a positive integer multiple of the target cap. The kernel is uniquely the residue map, up to reference-null sets. Arbitrary independent additive noise, with no moment assumptions, does not alter the criterion. All lower-threshold conditionings already determine the full experiment.

A separate proposition proves that for arbitrary compactly supported independent coordinate laws, universal garbling is equivalent to a probability convolution factorization of the source law by the target law. Classical comparison-of-experiments and convolution antecedents are explicitly acknowledged. The proofs are ordinary mathematical arguments, not formalized or externally refereed results.

## Files

- universal_garbling_classification.pdf: complete report
- universal_garbling_classification.tex: editable LaTeX source
- build.sh: standard TeX Live build command
- SOURCES.md: references and exact repository source identifiers
- validation.json: final artifact and check summary
- checks/verify_discrete_analogue.py: standard-library exact rational regression
- checks/discrete_analogue_results.json and checks/verification.log: recorded results
- SHA256SUMS: package-file integrity manifest (retired on filing; not in the repository)

## Reproduction

Run `bash build.sh` with a standard TeX Live installation containing the packages named in the source. (Since the editorial amendments of 2026-10-01 below, the checker writes to
`checks/rerun/`; `build.sh` runs `pdflatex` in this directory and overwrites the
filed PDF, so build on a copy.) Run `python3 checks/verify_discrete_analogue.py` to reproduce the finite exact checks. The checker reconstructs a unique candidate kernel from total-sum equations in a discrete truncated-geometric analogue and then verifies all remaining equations and stochasticity. It checks 576 parameter pairs, identifies exactly 42 feasible cases, and checks independent-noise and threshold identities. This finite analogue is a regression check; the continuous theorem rests on the analytic proof in the report.

## Scope

The classification concerns a single source coordinate, a single target coordinate, and one kernel for the complete weight or threshold family. It does not classify multicoordinate kernels, one prescribed threshold, or a restricted pair of hypotheses. The preceding modulo report is a separate unchanged companion.

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

- `universal_garbling_classification.tex`: an unnumbered environment `ednote` ("Editorial note (ProveIt,
  2026-10-01)") is defined after the theorem environments (no counter
  changes). Two notes:
  - after Proposition 4.1 (`prop:convolution`) and the paragraph following
    it: the proposition is the case of two one-coordinate masks of Theorem 1.1
    of `../Universal_Fabius_Mask_Criterion/`, which proves the same criterion
    by the same transform argument for arbitrary finite or countable masks
    (overlapping or of different sizes) and re-proves Lemmas 2.1 and 2.2 in
    its Sections 1.1 and 1.2; read as one series, that theorem is the primary
    statement. Corollary 5.1 is extended to masks by Theorem 2.1 of that note
    (`q = 1/M`) and by Theorem 2.1 of `../Arithmetic_Geometric_Mask_Order/`
    (every `q`);
  - at the end of "Source and attribution", a series map: the eight notes in
    the order written (this is the second); the companion cited as `Modulo`
    (source `exact_fabius_mask_order.tex`) is `../Exact_Fabius_Mask_Order/`,
    whose residue swap (its Lemma 2.1) Section 3 reproduces, and the pinned
    `Repository` article is `../Critical_Complements_Sharp_Information_Loss/`.
- `universal_garbling_classification.pdf`: rebuilt from the amended source with three `pdflatex` passes
  (MiKTeX 26.2, pdfTeX 1.40.29): 6 A4 pages (5 as delivered), 340,285 bytes; all 18
  fonts embedded, none Type 3; the final log has no error, overfull or
  underfull box, undefined or multiply defined reference, duplicate
  destination, or rerun request. The pages carrying the notes were rendered
  and inspected.
- `checks/verify_discrete_analogue.py`: new option `--output-dir`.
  As delivered, the program overwrote the recorded file beside itself, with
  CRLF line endings on Windows; it now writes `checks/rerun/discrete_analogue_results.json` (or
  `<output-dir>/discrete_analogue_results.json` with `--output-dir`), with LF line endings. Pass
  `--output-dir` with the program's own directory, on a copy, to regenerate
  the recorded file. On the ProveIt machine use `py` rather than `python3`.
  A rerun of the amended checker on a copy (2026-10-01,
  `py checks/verify_discrete_analogue.py`, Python 3.14.4, standard library)
  wrote `checks/rerun/discrete_analogue_results.json` equal to the recorded
  file byte for byte, and its console output equals `checks/verification.log`
  after CRLF-to-LF conversion.
- `build.sh`: kept as delivered. It runs `pdflatex` three times in this
  directory, so it overwrites the filed PDF and leaves `.aux`, `.log` and
  `.out` files here: build on a copy.
- `validation.json`: `pdf_pages` set to 6; its other entries are as delivered.
- `README.md`: the page count, the retired ledger under "Files", the
  parenthesis under "Reproduction", and this section.
