# Source and novelty audit

## Repository source

Repository: VladimirReshetnikov/ProveIt
Inspected commit: `6c9175a54bcaad3bfc2d416257d2b7d3dff2c1e0`
Inspection date: 28 September 2026.

Exact source path:

    Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/
    drafts/inverse-and-sampling/fabius_information_frontier/
    fabius_information_frontier.tex

The line breaks above are for presentation, not part of the path.

Canonical pinned URL:
https://github.com/VladimirReshetnikov/ProveIt/blob/6c9175a54bcaad3bfc2d416257d2b7d3dff2c1e0/Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/inverse-and-sampling/fabius_information_frontier/fabius_information_frontier.tex

The near-Gaussian section, including the exact cumulants, the formal cubic
entropy calculation, conjecture `conj:entropic-edgeworth`, and its explanation
of the missing tail estimate, was read. The package README and the original
numerical table were also inspected. Repository search was used to locate the
label and related Edgeworth references. This was a targeted investigation,
not an exhaustive audit of the entire repository.

The source explicitly conjectures:

    Delta(q) = (3/100)(1-q)^2 + (33/500)(1-q)^3 + O((1-q)^4),

and an all-orders rational-coefficient expansion with the stated power
remainder. The present article's Theorem 2.1 proves that assertion. Its
Fourier, density-envelope, and nonlinear-transfer estimates are supplied as
conventional proofs, independently of any claims elsewhere in the repository.

The separate conjecture `conj:deficit-monotone` is NOT resolved here.

## Relationship to existing mathematics

The first two coefficients and the exact infinite-law cumulant hierarchy were
already in the repository source. They are not claimed as discoveries here.
The quartic and higher coefficients, the explicit tail-control proof, the
finite-prefix two-parameter formulation, and the positive-order Renyi
formulation are the additions developed in this package. Their exact
formulations were not found in the targeted source inspection. That is not a
proof of worldwide publication priority or of absence from every other file.

General entropic Edgeworth expansions and Renyi central limit theorems predate
this manuscript. The primary references used to situate the contribution are:

1. S. G. Bobkov, G. P. Chistyakov, F. Gotze, Rate of convergence and
   Edgeworth-type expansion in the entropic central limit theorem,
   Ann. Probab. 41 (2013), 2479-2512, DOI 10.1214/12-AOP780.
   https://arxiv.org/abs/1104.3994
2. S. G. Bobkov, G. P. Chistyakov, F. Gotze, Renyi divergence and the
   central limit theorem (2016).
   https://arxiv.org/abs/1608.01805
3. S. G. Bobkov, G. P. Chistyakov, F. Gotze, Renyi Divergences in
   Central Limit Theorems: Old and New (2025).
   https://arxiv.org/abs/2503.03926
4. Juan Arias de Reyna, Arithmetic of the Fabius function,
   arXiv:1702.06487v3 (2017).
   https://arxiv.org/abs/1702.06487

The iid literature is not silently invoked as an infinite triangular-array
theorem. The analytic proof needed for the geometric family is written out.
The references were inspected through the primary arXiv records, with the
2013 paper additionally read as a PDF during development. No copyrighted
external papers or complete repository manuscripts are redistributed.

## Trust boundary

No Lean theorem was added, compiled, or audited as part of this deliverable.
No ProveIt file was modified. The article and code have not received an
independent peer review. The mathematical proofs should be reviewed on their
stated hypotheses and conclusions; exact symbolic checks are not a substitute
for checking the analytic argument.
