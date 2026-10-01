# Universal Comparison of Fabius Observation Masks

A self-contained research companion (eight pages since the editorial
amendments below; seven as delivered).

The report proves:

1. For arbitrary independent bounded coordinates with summable caps, one observation mask universally simulates another under every total-sum reweighting exactly when its observed-sum law has the target observed-sum law as a probability convolution factor. Masks may overlap, have unequal cardinalities, or be countably infinite. Arbitrary independent additive noise and all-threshold formulations are included.
2. For common-tilt uniform coordinates with reciprocal-integer geometric caps, universal dominance is equivalent to prefix-count dominance. The result allows randomized kernels pooling every source observation; the deterministic residue map already realizes the full possible order.
3. For finite equal-cardinality masks with commensurate caps, universal dominance is equivalent to the explicit q-integer quotient being a polynomial with nonnegative coefficients. A posterior kernel works independently of the common tilt.
4. Classical Gaussian polynomials yield positive comparisons beyond pairwise cap divisibility, while the polynomial 1-u+u^2 gives a genuine positivity obstruction.

## Files and reproduction

- universal_fabius_mask_criterion.pdf: complete report
- universal_fabius_mask_criterion.tex: editable LaTeX source
- build.sh: standard TeX Live build command
- SOURCES.md: checked references and repository identifiers
- validation.json: final QA and regression results
- checks/verify_mask_criteria.py: standard-library exact arithmetic checker
- checks/mask_criteria_results.json and checks/verification.log: recorded results
- SHA256SUMS: integrity manifest (retired on filing; not in the repository)

Run `bash build.sh` with standard TeX Live, or `python3 checks/verify_mask_criteria.py` to reproduce the exact checks. (Since the editorial amendments of 2026-10-01 below, the checker writes to
`checks/rerun/`; `build.sh` runs `pdflatex` in this directory and overwrites the
filed PDF, so build on a copy.) The checker covers 4,092 finite geometric-mask pairs by polynomial divisibility, directly solves the full kernel equations for 256 overlapping-mask pairs in an independent Bernoulli model, and verifies 66 Gaussian-polynomial identities plus both displayed examples. These finite checks support transcription and algebra; the infinite-mask and arbitrary-noise results rest on the analytic proofs.

## Scope

Universal means one kernel for the entire weight or threshold family. The result does not decide every isolated two-hypothesis comparison. The polynomial coefficient criterion specifically requires equal cardinalities; the general convolution theorem has no such restriction. Vector kernels need not be unique; only their conditionally averaged scalar-sum kernels are unique. These are ordinary mathematical proofs, not formalized or externally refereed results. Classical comparison and q-polynomial identities are attributed without a general novelty claim.

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

- `universal_fabius_mask_criterion.tex`: an unnumbered environment `ednote` ("Editorial note (ProveIt,
  2026-10-01)") is defined after the theorem environments (no counter
  changes). Four notes:
  - after the paragraph following Theorem 2.1 (`thm:geometric`): it is the
    case `d = 1`, `q = 1/M`, of Theorem 2.1 of
    `../Arithmetic_Geometric_Mask_Order/`, which classifies the universal
    order for every ratio with the same tail bound, zero-multiplicity argument
    and residue vector; read as one series, that theorem is the primary
    statement of the order;
  - at the end of Section 4: Theorem 3.1 is the equal-cardinality case of
    Theorem 1.1 of `../Uniform_Smoothing_Mask_Stabilization/`, whose Theorem
    5.1 shows that the source `(h, 6h)` with nine further caps `h` dominates
    `(2h, 3h)` and with eight does not. The same signed quotient is
    `thm:base6` of
    `../../spectra-and-arithmetic/Simultaneous_Convolution_Divisors_Fabius_Type_Laws/`
    and `prop:base6` of
    `../../spectra-and-arithmetic/Arithmetic_Rigidity_off_Resonance_Geometric_Uniform_Laws/`,
    which this note does not cite: there the two largest source uniforms
    have lengths `6h` and `h` and the targets `3h` and `2h` (`h = 1/3`,
    respectively `1/6`), the centred factor `delta_{-h} - delta_0 + delta_h`
    is that of `1 - u + u^2` up to translation, and the remaining geometric
    tail, supported on an interval shorter than `h`, leaves a negative mass
    at the centre;
  - at the end of Section 5: the two halves of the proof of Theorem 2.1 (zero
    multiplicities, digit splitting) are those of the prime-adic Hall
    criterion `thm:hall` of the first of those articles, uncited; the
    statements differ (all uniform divisors of the whole law for a prime
    base, against sub-masks of one family for every integer `M >= 2`), and
    composite `M` causes no obstruction here because every target is a
    coordinate of the family;
  - after it, a series map: the eight notes in the order written (this is
    the third); `Modulo` and `Classification` are `../Exact_Fabius_Mask_Order/`
    and `../Universal_Garbling_Classification/` (whose Proposition 4.1 is the
    case of two one-coordinate masks of Theorem 1.1 here, and whose Lemmas
    2.1 and 2.2 Sections 1.1 and 1.2 re-prove), and `Repository` is
    `../Critical_Complements_Sharp_Information_Loss/`.
- `universal_fabius_mask_criterion.pdf`: rebuilt from the amended source with three `pdflatex` passes
  (MiKTeX 26.2, pdfTeX 1.40.29): 8 A4 pages (7 as delivered), 368,916 bytes; all 19
  fonts embedded, none Type 3; the final log has no error, overfull or
  underfull box, undefined or multiply defined reference, duplicate
  destination, or rerun request. The pages carrying the notes were rendered
  and inspected.
- Reciprocal notes of 2026-10-01 now stand after `thm:base6` of the first and
  after `thm:separated` and the question "Composite reciprocal returns" of the
  second `spectra-and-arithmetic/` article named above.
- `checks/verify_mask_criteria.py`: new option `--output-dir`.
  As delivered, the program overwrote the recorded file beside itself, with
  CRLF line endings on Windows; it now writes `checks/rerun/mask_criteria_results.json` (or
  `<output-dir>/mask_criteria_results.json` with `--output-dir`), with LF line endings. Pass
  `--output-dir` with the program's own directory, on a copy, to regenerate
  the recorded file. On the ProveIt machine use `py` rather than `python3`.
  A rerun of the amended checker on a copy (2026-10-01,
  `py checks/verify_mask_criteria.py`, Python 3.14.4, standard library, about
  17 seconds) wrote `checks/rerun/mask_criteria_results.json` equal to the
  recorded file byte for byte, and its console output equals
  `checks/verification.log` after CRLF-to-LF conversion.
- `build.sh`: kept as delivered. It runs `pdflatex` three times in this
  directory, so it overwrites the filed PDF and leaves `.aux`, `.log` and
  `.out` files here: build on a copy.
- `validation.json`: `pdf_pages` set to 8; its other entries are as delivered.
- `README.md`: the page count, the retired ledger under "Files and
  reproduction", the parenthesis after the reproduction command, and this
  section.
