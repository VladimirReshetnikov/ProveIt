# Exact Erasure without a Common Invariant Line

A research article prepared for Vladimir Reshetnikov, October 2, 2026.
Mathematical development and implementation: ChatGPT.

## Read first

`article.pdf` is the compiled 29-page report. `article.tex` is its standalone
LaTeX source, including the bibliography. The central theorem is in Section 4;
the direct PCP frontend is in Section 5; the Diophantine certificates are in
Section 9. Section 14 gives nine concrete research directions.

The positive-stochastic compiler maps m integer d-by-d matrices to m+2 positive
rational (2d+1)-by-(2d+1) column-stochastic matrices with no common invariant
complex line. It preserves mortality through the exact identity

    rank(S_word) = 1 + 2 rank(A_source_projection).

A prescribed contraction factor eta in (0,1) is retained. Published mortality
bounds imply undecidability for at most eight 7-by-7 target matrices. A separate
explicit PCP reduction gives a many-one complete nine-state family when alphabet
size is part of the input. These are distinct statements; the package does not
claim many-one completeness for the eight-letter bound without an additional
source reduction.

For an external horizon T, the compressed natural quartic has

    T((n-1)^2+k) witnesses,
    T((n-1)^2+1)+(n-1)^2 squared residuals.

At n=7,k=8 this is 44T witnesses and 37T+36 residuals. The natural zero set is in
bijection with the accepted labelled words of length T.

**Boundaries:** no irreducibility claim (a common hyperplane remains); no fixed
numerical universal gate alphabet is supplied; no claim about undecidable HMM
output entropy; no expanded small fixed-arity DPRM polynomial; no improvement to
ProveIt's stated 87-operation universal bound; no Lean/Rocq verification or
independent peer review. The proofs are fully supplied as mathematics, with
external dependencies and novelty qualifications in `PROOF_STATUS.md`.

## Reproduce

Python 3.10 or newer; Python standard library only. The recorded run used 3.13.5.

```sh
python3 code/run_checks.py
python3 code/check_certificate.py examples/seven_state_information_certificate.json
python3 code/check_certificate.py examples/pcp_nine_state_information_certificate.json
```

The suite writes examples and `verification/check_results.json`. The recorded
run passed **50,582 assertions**, including 10,188 mortality/rank comparisons,
3,448 independent evaluations of each numerical quartic format, and 1,638
arbitrary PCP connector-word checks. These are finite checks, not a replacement
for the universal proofs.

For the PDF, install a standard TeX distribution with the packages listed in the
preamble, then run:

```sh
make pdf
```

The make target runs pdfLaTeX three times to stabilize contents and references.
`make all` reruns the Python suite and builds the PDF.

## Files

- `code/erasure.py`: exact affine and tensor compilers, PCP frontend, numerical
  full and compressed certificates, rank utility, and invertibilizing perturbations.
- `code/check_certificate.py`: independent residual evaluator. It imports no
  generator code and rejects noninteger/negative witness fields.
- `code/run_checks.py`: deterministic finite checks and example regeneration.
- `examples/three_state_*`: completely printed readable example; includes a
  deliberately **incorrect uniform-target certificate** that must be rejected.
- `examples/seven_state_*`: numerical eight-letter instance and its full,
  uniform-target, and compressed certificates.
- `examples/pcp_nine_state_*`: end-to-end PCP instance and both certificate forms.
- `examples/perturbed_non_erasing_instance.json`: positive invertible perturbation.
- `verification/check_results.json`: exact test counts and example ledgers.
- `verification/pdf_preflight.json`: PDF build/render inspection receipt.
- `SOURCE_AUDIT.md`, `PROOF_STATUS.md`: provenance and mathematical claim boundaries.

JSON words use **zero-based labels in chronological order**: `[i,j]` means the
matrix product S_j S_i. The article uses mathematical labels as stated in each
section. `D` is the common denominator, and `matrices` contains integer numerators.
`linear_parts` and `translations`, when present, are compiler metadata, not extra
certificate witnesses.

The certificate checker accepts the two numerical formats
`exact-erasure-natural-quartic-v1` and `exact-erasure-information-quartic-v1`.
It returns exit status 0 for an accepted certificate and nonzero otherwise.
The uniform-*input-parameter* schema of Proposition 9.3 is proved in the article
but is not implemented as a third certificate format.

The repository was inspected at commit
`928ea97017a25ebe56d240c84f27d2275d818c75`. No repository files were changed.
