# Source map and limits

The article's mathematical proofs are self-contained. Source comparisons fix terminology, normalizations, and established antecedents; they do not import an unproved numerical constant.

## Established analytic antecedent

Tanja Eisner and Terence Tao, Large values of the Gowers-Host-Kra seminorms, arXiv:1012.3509v2, Theorem 1.1(2), Remark 1.6, and Section 2:
https://arxiv.org/abs/1012.3509v2

This paper establishes a broader near-extremizer theorem for compact abelian groups with R/Z-valued polynomial maps. It discusses effective polynomial rates without giving the numerical constants used here. No copy of the paper is distributed.

## Pinned repository definitions

Repository: VladimirReshetnikov/ProveIt
Commit: 95460768cc4015862fec316f83df5861b04d28bc

- Combinatorics/Ramsey/Lean/GowersSzemeredi/Definitions.lean, lines 81-101 for progression properness and 149-170 for differences and UniformOfDegree
- lake-manifest.json, pinning Mathlib at 81a5d257c8e410db227a6665ed08f64fea08e997

The exact raw files are under provenance/sources. Their byte counts, SHA-256 hashes, Git-blob SHA-1 hashes, paths, and pinned URLs are in provenance/source_manifest.json and checked by the companion.

## Pinned Fourier definition

Repository: leanprover-community/mathlib4
Commit: 81a5d257c8e410db227a6665ed08f64fea08e997
Path: Mathlib/Analysis/Fourier/ZMod.lean
Relevant lines: 107-108

This is the unnormalized negative-sign transform. The raw snapshot is named Mathlib_Fourier_ZMod.lean in the payload.

## Established dense extension antecedent

Canonical source 12, global affine extension of a Freiman map above density 2/3, appears at lines 12970-12979 of the canonical article at the fixed ProveIt pin:
https://github.com/VladimirReshetnikov/ProveIt/blob/95460768cc4015862fec316f83df5861b04d28bc/Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements/article.tex#L12970-L12979

The article here proves the one-variable partial-additivity-to-Freiman step and the full higher-dimensional slice induction. No full canonical article or excerpt is distributed.

## Bounded overlap check

One bounded repository-source check on 7 October 2026 used snapshot 7ed8eec958bf266ed5e7be136e296cbe58310f89 and canonical article Git blob 98978519d5187f71453b832226135f3c7d6e73be. It located established extension and near-extremizer antecedents but did not locate this particular higher-order explicit-constant Fourier-box formulation. This is a bounded finding only, not a priority certificate or an exhaustive literature/repository search. Raw search responses are excluded.

## What has not been established

No Lean implementation, kernel audit, new arbitrary-uniformity inverse theorem, integration theorem in unrestricted small characteristic for ordinary residue-ring polynomials, constructive noncyclic integration theorem, all-degree extraction iteration, or global Ramsey/Szemeredi bound is claimed. The all-finite-abelian Fourier and energy theorems, the all-cyclic periodic rational polynomial-phase theorem, and the factorial-qualified ordinary residue-ring corollary must be kept distinct.

The cyclic extension is proved in the article using rational shift antiderivatives: P(x+N)-P(x)=c*binom(x,d), P(0)=0, and coefficient c/((d+1)!*N) at x^(d+1). Integrality on all integer arguments makes e(P), rather than P itself, N-periodic. Any integer lift of c is allowed; the phase can depend on that lift, while its top-derivative frequency does not. The article supplies both triangular and Newton-basis constructions and reuses the same selected-energy theorem and descent constants. This is a self-contained construction within the established near-extremizer phenomenon, with no historical-priority claim. The exact companion tests finite ranges only; it does not replace the universal proof.
