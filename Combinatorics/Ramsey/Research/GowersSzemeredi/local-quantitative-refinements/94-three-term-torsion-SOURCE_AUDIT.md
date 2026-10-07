# Source audit and mathematical status

Prepared 7 October 2026. Repository comparison is pinned to
`0ef37201dea1237390e59d0960c1058aaeaa3572` of
`VladimirReshetnikov/ProveIt`.

## Sources used directly

**Gowers (2001), A new proof of Szemeredi's theorem.** The edited repository
transcription was read for the Fourier normalization, Lemma 2.2, and the counting
step of Theorem 2.6. The article cites the original paper, GAFA 11, 465-588,
DOI 10.1007/s00039-001-0332-9. The inspected repository file is
`Combinatorics/Ramsey/Papers/sz-thm-gowers-proof/sz-thm-gowers-proof.tex`,
Git blob `bd512b4ab43aa5f373621cdc6c8be6685178dce5`.

**Christ (2013), The optimal constants in Holder-Brascamp-Lieb inequalities for
discrete Abelian groups**, arXiv:1307.8442. The paper and Theorem 1.1 were inspected
for the general finite-group sharp-constant principle. The constrained Fourier
sum in the present manuscript is an HBL datum on the solution subgroup
{(beta,gamma):a beta+b gamma=0}, with the three indicated projections and
exponents (1/p,1/2,1/2). The manuscript's proof is direct and does not import
Christ's theorem as an unproved step.

**Repository source 10, torsion-energy.** The verifier
`code/10-torsion-energy-verify_torsion.py`, blob
`55a5e93019c81338516a7a5daa20404a6a582a16`, was inspected, together with its source
manifest. Its mixed-norm function explicitly requires an invertible final adjacent
difference and already treats ordinary endpoint torsion. The present article
extends the three-term coefficient to arbitrary increment maps; it does not
claim to have introduced torsion-sensitive estimates generally.

**Repository source 20, quadratic-counting.** The verifier
`code/20-quadratic-counting-verify.py`, blob
`703defdd4052714e05823dae38389b3f3fdf821a`, was inspected for directional,
two-function, finite-index, and single-set three-term estimates. The present
operator approach is complementary and is not claimed to dominate all of those
bounds.

The code paths for sources 10 and 20 are relative to
`Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements/`.
Full URLs appear in `data/source_audit.json`.

## Scope of the review

The repository directory, research index, selected source manifests, and targeted
source code and paper ranges were inspected. This is not a line-by-line audit of
the entire consolidated research article or a proof that no related formulation
occurs anywhere in the repository. It is also not an exhaustive literature-priority
search. The article explicitly states these limits.

No third-party paper or repository source file is redistributed. The ZIP contains
the prepared manuscript, its verifier, and provenance/integration documentation.
The remote repository was not modified.

## Status of the contribution

The exact coefficient diagram, singular-spectrum formula, equality classification,
stability estimates, exponent obstructions, and counting corollaries all have
deductive proofs in `article.tex`. They are submitted as research claims for
mathematical review. The finite checks provide independent diagnostics only.

The general HBL principle and the familiar ordinary endpoint coefficient are
credited as prior results. Specific priority for the full structural/stability
formulations has not been established. No global Szemeredi improvement, resolution
of the proposed further questions, peer review, or Lean verification is claimed.
