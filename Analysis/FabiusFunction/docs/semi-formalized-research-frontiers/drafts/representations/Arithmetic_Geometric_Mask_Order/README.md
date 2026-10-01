# Arithmetic Classification of Geometric Observation Masks

A research companion (five pages since the editorial amendments below;
four as delivered) classifying the universal observation order for every geometric ratio 0<q<1.

Let H contain the positive integers k for which q^(-k) is an integer. If H is empty, one mask universally dominates another exactly when it contains that target mask. Otherwise H=dN for a least positive d, and the complete order is prefix-count dominance separately in each residue class modulo d. Classwise deterministic residue maps realize every permitted comparison, including finite/countable masks, unequal cardinalities, overlap, and arbitrary independent additive noise. Randomized kernels pooling source observations do not add comparisons.

The exceptional ratios are exactly M^(-1/d), M>=2 and d>=1 integers. They form a countable dense set. For any fixed comparison beyond inclusion, however, the admissible ratios are locally finite in (0,1); only inclusion comparisons persist on a nonempty open interval. Universal equivalence of masks holds only when the masks are equal.

## Files and reproduction

- arithmetic_geometric_mask_order.pdf: complete report
- arithmetic_geometric_mask_order.tex: editable LaTeX source
- build.sh: standard TeX Live build
- SOURCES.md: source context and references
- validation.json: final artifact and regression summary
- checks/verify_arithmetic_order.py: standard-library exact arithmetic checker
- checks/arithmetic_order_results.json and checks/verification.log: recorded results
- SHA256SUMS: integrity manifest (retired on filing; not in the repository)

Run `bash build.sh` with standard TeX Live or `python3 checks/verify_arithmetic_order.py` for exact checks. (Since the editorial amendments of 2026-10-01 below, the checker writes to
`checks/rerun/`; `build.sh` runs `pdflatex` in this directory and overwrites the
filed PDF, so build on a copy.) The checker uses prime valuations to determine integer powers for 44 root-parameter configurations and compares the residue-prefix test against a generic bipartite matching algorithm for 180,224 mask pairs. It also checks 12,288 nonexceptional rational-ratio mask pairs and 1,320 exact power-membership identities. These are finite regression checks; the countable product and universal-kernel assertions are proved analytically.

## Scope

Universal comparison means one kernel for every total-sum reweighting, equivalently every positive-probability lower threshold. The theorem does not decide one fixed conditioning rule, a specified two-hypothesis comparison, or the sharp overlap asymptotics for the Fabius conditioning weight. General Blackwell and convolution methods are classical. No general priority claim is made, and these are ordinary mathematical proofs rather than formalized or externally refereed results.

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

- `arithmetic_geometric_mask_order.tex`: an unnumbered environment `ednote` ("Editorial note (ProveIt,
  2026-10-01)") is defined after the theorem environments (no counter
  changes). Two notes:
  - after the second paragraph of Section 4: for ratios `q` no positive power
    of which is rational, case 1 of Theorem 2.1 also follows from
    `thm:separated` of
    `../../spectra-and-arithmetic/Arithmetic_Rigidity_off_Resonance_Geometric_Uniform_Laws/`
    (filed 2026-09-30, batch 69), which this note does not cite: the caps
    `c q^i` are pairwise rationally incommensurable, and that theorem allows a
    target width `c q^j` only as `c q^i / n` with distinct source coordinates
    `i`, which forces `i = j` and `n = 1`, that is, `L` contained in `E`
    (translation does not affect divisibility, and a common tilt carries a
    factorization both ways). This note adds the ratios with a rational but
    no integer power of `1/q`, such as `q = 2/3`; its exceptional set lies in
    that article's countable dense set of ratios with a rational power
    (`prop:full`), and its classwise prefix counts are a sub-mask analogue of
    the rationality classes of its `thm:channels`;
  - at the end of Section 4, a series map: the eight notes in the order
    written (this is the fifth); `Masks` (source
    `universal_fabius_mask_criterion.tex`) is
    `../Universal_Fabius_Mask_Criterion/`, whose Theorem 2.1 is the case
    `d = 1` of Theorem 2.1 here, re-proved with the same tail bound and
    zero-multiplicity argument (read as one series, Theorem 2.1 here is the
    primary statement of the order), and `Repository` is
    `../Critical_Complements_Sharp_Information_Loss/`.
- `arithmetic_geometric_mask_order.pdf`: rebuilt from the amended source with three `pdflatex` passes
  (MiKTeX 26.2, pdfTeX 1.40.29): 5 A4 pages (4 as delivered), 341,323 bytes; all 20
  fonts embedded, none Type 3; the final log has no error, overfull or
  underfull box, undefined or multiply defined reference, duplicate
  destination, or rerun request. The pages carrying the notes were rendered
  and inspected.
- A reciprocal note of 2026-10-01 now stands after `thm:separated` of the
  `spectra-and-arithmetic/` article named above.
- `checks/verify_arithmetic_order.py`: new option `--output-dir`.
  As delivered, the program overwrote the recorded file beside itself, with
  CRLF line endings on Windows; it now writes `checks/rerun/arithmetic_order_results.json` (or
  `<output-dir>/arithmetic_order_results.json` with `--output-dir`), with LF line endings. Pass
  `--output-dir` with the program's own directory, on a copy, to regenerate
  the recorded file. On the ProveIt machine use `py` rather than `python3`.
  A rerun of the amended checker on a copy (2026-10-01,
  `py checks/verify_arithmetic_order.py`, Python 3.14.4, standard library)
  wrote `checks/rerun/arithmetic_order_results.json` equal to the recorded
  file byte for byte, and its console output equals `checks/verification.log`
  after CRLF-to-LF conversion.
- `build.sh`: kept as delivered. It runs `pdflatex` three times in this
  directory, so it overwrites the filed PDF and leaves `.aux`, `.log` and
  `.out` files here: build on a copy.
- `validation.json`: `pdf_pages` set to 5; its other entries are as delivered.
- `README.md`: the page count, the retired ledger under "Files and
  reproduction", the parenthesis after the reproduction command, and this
  section.
