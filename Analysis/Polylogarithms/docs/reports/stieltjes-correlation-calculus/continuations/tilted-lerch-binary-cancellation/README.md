# Tilted Lerch Convolutions and Binary Harmonic Cancellation

**Research continuation for Vladimir Reshetnikov's ProveIt project — 10 October 2026.**

The primary deliverables are `article.tex` (self-contained LaTeX) and `article.pdf` (28 pages in the delivered build). The article gives ordinary mathematical proofs; it is not a proof-assistant development. Its questions come from the inspected *Reciprocal Lerch Convolutions* continuation, especially Q1–Q3, rather than from archive names alone.

## Main results

The report proves a finite ordinary-Lerch formula for arbitrary complex orders in a matched-shift exponentially tilted convolution; a Hermite formula for every partial tilt collision; cancellation of all artificial interior branch points and explicit boundary singular germs; a globally available normally convergent single-anchor expansion for independent shifts and tilts; all independent order jets; and an exact criterion for termination in that one-anchor functional basis.

Consequences include all-index Stieltjes differences, Gamma and polygamma identities, a pure Gaussian polylogarithm pairing, finite generalized harmonic corrections, all raw logarithmic moments with the required matched-shift chain-rule correction, and anchored primitives at every integration resonance.

The arithmetic continuation gives a polynomial-inverse cancellation criterion and its reduction modulo two. It completely classifies the cancellation sets at depths `2^h + 1`, proves a symbolic infinite mixed-parity depth-seven family, and evaluates its first six-dimensional elementary integral as an explicit rational polynomial in pi squared.

## Evidentiary status

The exact script passed **2,185 assertions**, including four negative controls. Two numerical runs, at **45 and 60 working decimal digits**, each passed **56 positive comparisons and one negative control**. Largest normalized residuals are approximately `3.6783e-44` and `2.9871e-59`, respectively. These floating-point checks use recorded finite truncations and are **not interval enclosures**. Infinite statements are proved in the article, not established by those residuals.

The short Gaussian S6 and revised S8 candidates remain unresolved. The existing S4 theorem is not recounted as new. No false source theorem is invented for an error-correction narrative: the audit identifies concrete integration pitfalls and explains the exact correction formulas. Historical priority for every special case is not claimed. Some incoming binary archive contents could not be inspected; see `SOURCE_AUDIT.md`.

## Replay

Use Python 3 with the versions in `requirements.txt`, and a standard TeX installation providing `pdflatex` and the packages named in `article.tex`.

```sh
python -m pip install -r requirements.txt
python code/verify_exact.py
python code/verify_numerical.py --dps 45
python code/verify_numerical.py --dps 60
python code/build.py
python code/inspect_pdf.py
```

The inspection command renders all pages in a sibling directory, not inside this distribution. It checks page text boundaries and expected headings. Visual review remains separate. `data/visual_review.md` records the delivered review.

## Package map

- `article.tex`, `article.pdf`: complete article, proofs, examples, audit, and ten further research directions.
- `code/`: exact checks, independent numerical diagnostics, build, and PDF inspection.
- `data/`: exact fractions, numerical settings and residuals, build/inspection receipts, and theorem-label records.
- `integration/`: additive manuscript fragment, citation entry, theorem index, and integration instructions.
- `CLAIM_STATUS.md`, `SOURCE_AUDIT.md`: claim boundaries and source provenance.
- `SHA256SUMS`: hashes of delivered files, excluding the manifest itself.

The suggested repository destination is `Analysis/Polylogarithms/docs/reports/tilted-lerch-binary-cancellation/`. Nothing was committed, uploaded, or changed in the repository. The consolidated manuscript was not rebuilt. Apply the repository's licensing and authorship conventions during integration; no third-party source article or font files are redistributed here.
