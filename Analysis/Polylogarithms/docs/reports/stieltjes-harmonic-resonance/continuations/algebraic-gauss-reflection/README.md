# Algebraic Gauss Residues and Centered Harmonic Reflection

A research continuation for `VladimirReshetnikov/ProveIt`.

The main article is **`article/article.pdf`**. Its source is
`article/article.tex`, with `body.tex` and `references.tex` in the same
folder. A single-file source is also included as
`Algebraic_Gauss_Centered_Harmonic_Reflection.tex`. The compact proposed
integration insertion has a three-page PDF preview in `integration/`.
This package does not modify the live repository.

## Results

The article supplies an elementary proof of the explicitly requested
Gauss/Bernoulli residue identity, then evaluates the entire resonant tail
by finite Stirling sums. It proves a moving-reflection theorem for
harmonic Barnes derivatives, common all-depth even zeros, uniqueness of
the center, an all-depth Gamma generating function for convergent
harmonic sums, an unequal-frequency extension, and shifted all-order
polygamma–Stieltjes identities with ordinary antiderivatives.

The fixed-shift negative Laurent theorem is prior repository work and is
credited accordingly. A specific off-by-one error in the introductory
Stieltjes-limit formula of arXiv:2403.07123v1 is corrected; the original
PDF page was inspected. Neither S6 nor S8 is proved here, and no global
priority claim is made.

## Rebuild and verify

From this directory:

```sh
python -m pip install -r requirements.txt
python code/verify.py --part all
bash build.sh
```

The verification script can also run `--part exact` or `--part numeric`.
It writes its receipts into `data/`. The delivered exact run has 436
rational/polynomial checks and four specified negative controls. The
numerical run has 30 comparisons at 65 decimal digits. The largest
reported discrepancy is approximately 1.99e-51. These are diagnostic
comparisons, not rigorous interval certificates; an asymptotic tail
accelerator is used for one group of numerical checks. The arbitrary-index
proofs are in the article, not inferred from the finite tests.

A normal TeX installation with pdfLaTeX, AMS packages, Latin Modern,
mathrsfs, microtype, fancyhdr, enumitem, xurl, and hyperref builds the PDF.
No font files are distributed.

## Files

- `article/`: the complete research article and its editable TeX sources.
- `code/verify.py`: exact independent Bernoulli/Stirling constructions and
  numerical Mellin/Beta comparisons.
- `data/`: machine-readable results and exact coefficient tables.
- `audit/`: source provenance, proof status, and the specific correction.
- `integration/`: proposed repository placement and a self-contained TeX
  addendum with the principal algebraic and reflection results.
- `SHA256SUMS`: hashes of delivered files other than the manifest itself.

The repository baseline is pinned to
`dd78c6c9079e1e4a32600d8f9400667b4de8bd54`. The source audit records
observed blob identifiers. The incoming directory was inspected as a
queue; not every binary ZIP in it was unpacked or audited. The integration
files are proposals pending independent mathematical and editorial review.
