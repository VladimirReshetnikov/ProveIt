# Integration into ProveIt

## Suggested destination

A separate research directory avoids assigning a source number that may already
have been used by a concurrent contribution:

    Combinatorics/Ramsey/Research/GowersSzemeredi/
      sharp-three-term-torsion-stability/

Copy the package contents into that directory. Alternatively, incorporate the
manuscript into `local-quantitative-refinements` after allocating a fresh source
number and reconciling its preamble with the consolidated article. This package
does not edit or renumber existing sources.

The inspected baseline is commit
`0ef37201dea1237390e59d0960c1058aaeaa3572`. The repository may have later changes;
the comparison is pinned to this baseline, not asserted to cover future additions.

## Main theorem interfaces

| Manuscript result | Stable LaTeX label | Role |
| --- | --- | --- |
| Lemma 2.1 | `st3:lem-fourier` | Constrained Fourier identity for arbitrary increment maps |
| Lemma 2.2 | `st3:lem-fiber` | Uniform common-kernel fiber multiplicity |
| Proposition 2.3 | `st3:prop-multiplicity` | Multiplicity of each accessible support coset |
| Theorem 3.1 | `st3:thm-constants` | Exact Fourier-lp coefficient, all p |
| Corollary 3.2 | `st3:cor-u2` | Sharp U2 estimate without invertibility assumptions |
| Theorem 4.1 | `st3:thm-spectrum` | Full singular spectrum and reduced operator norm |
| Theorem 5.3 | `st3:thm-equality` | All complex equality cases, 2 < p < infinity |
| Theorem 6.1 | `st3:thm-stability` | Dimension-free near-extremizer repair |
| Proposition 6.4 | `st3:prop-optimal-exponents` | Optimality of both stability exponents |
| Propositions 7.1, 7.2 | `st3:prop-endpoint`, `st3:prop-middle` | Exact ordinary-progression control seminorms |
| Theorem 7.3 | `st3:thm-counting` | Quotient-corrected three-set counting |

These numbers refer to the standalone PDF. Labels and citation keys have `st3:`
and `st3-` prefixes. Theorem environments and mathematical macros have an `st`
prefix; they are defined in the source preamble. Check for name collisions when
merging. Do not include the standalone `documentclass`, title, headers, or
`document` environment inside an existing article.

## Normalization and hypotheses

Physical averages are probability averages. Fourier transforms include the factor
1/|G|; Fourier sequence norms use counting measure. In particular,

    ||hat f||_4 = ||f||_{U2, normalized}
    ||hat f_sum||_4 = |G| ||f||_{U2, normalized}
    ||f||_{U2, unnormalized cube} = |G|^(3/4) ||f||_{U2, normalized}
    ||f||_{L2, unnormalized} = |G|^(1/2) ||f||_{L2, normalized}.

D and G may be different finite abelian groups. A,B are arbitrary homomorphisms.
Coincident or zero maps are allowed. No assumption on A-B enters the sharp
coefficient, but the dual kernel of a-b affects spectral multiplicities.

The equality classification is for 2 < p < infinity, not for p=2 or infinity.
The stability theorem is for p=4, unit norm triples, and 0 <= epsilon <= 1/64.
It is a complex-function theorem. It does not promise an indicator-valued repair.
The proper-progression correction in Section 7 subtracts all d with 2d=0,
not only d=0.

## Proof dependencies

All general mathematical results have written proofs independent of numerical
experiments. The finite verification JSON is a reproducibility artifact, not an
additional unproved mathematical hypothesis. A useful formalization order is:
Fourier identity -> block fibers -> sharp norm bounds -> common-kernel character
sectors -> equality -> the seven stability steps.

A Lean formalization would need an exact finite-dimensional unitary/singular-value
interface, not a numerical SVD axiom. No proof-assistant certification is supplied.

## Attribution boundaries to preserve

Retain the attribution to Gowers and Christ and the comparison with existing
sources 10 and 20. Do not advertise the p=4 endpoint factor |G[2]|^(1/4) as newly
discovered. Do not describe this article as improving a global bound for r_k(N).
Do not turn the proposed directions in Section 10 into settled conclusions or
claim they are all previously published open problems.
