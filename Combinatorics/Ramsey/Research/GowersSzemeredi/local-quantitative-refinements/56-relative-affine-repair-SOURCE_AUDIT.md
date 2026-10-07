# Source audit, mathematical scope, and integration guidance

## Source versions

The Gowers interface was inspected through the connected GitHub repository.
A concrete checked snapshot is:

    b6a8ee96631fa845067e9ec9e5b1c2f42960a9c9

`Sections06_07.lean` was read at this exact ref. The Section 10 statement and
proof searches returned this ref as well. Later repository searches returned
`128f514afce0bf7eb48133fb30dd3f8e034ea3a2`; this later search head is not silently
substituted for the pinned snapshot. The consolidated research README was
inspected as an observed file blob, separately recorded in the source manifest.

The principal external comparison sources are:

1. Gowers (2001), *A new proof of Szemerédi's theorem*; the repository contains
   its edited transcription and statement/proof interfaces.
2. Kazhdan–Ziegler, *Polynomial functions as splines*, arXiv:1712.09047v3,
   especially Theorems 1.6 and 1.7. The statement page was inspected both as
   parsed text and as a PDF image. The text already establishes linear repair
   under an error-dependent uniformity hypothesis. We do not claim to invent
   linear repair, exact extension, or arbitrary abelian targets.
3. Peluse, *Another proof of the U⁴(F_p^n)-inverse theorem*,
   arXiv:2609.15788v1, Section 7. Her Lemma 7.4 is the direct explicit
   comparison: error 16ε^(1/4), uniformity u<(αε)^32, ε<2^(-15).
4. Blum–Luby–Rubinfeld (1993), classical self-testing/correction. The ordinary
   homomorphism correction argument is re-proved and credited, not presented
   as a new theorem.

External papers are not included in the archive. Their citation URLs and
identifiers are in the manuscript and source manifest.

## What this manuscript establishes

The weighted theorem uses only finite abelian Fourier analysis, exact moment
identities, collision-to-mode selection, classical self-correction, and an
explicit marked-error count. Its proposed contribution is the specific
quantitative statement with a fixed domain condition u⁴≤α⁵/1024, the relative
normalization, the profile, and the proved corollaries.

The sharper displayed profile is valid for every affine comparison map,
without the main smallness hypotheses. Those hypotheses first place the
constructed map in a small-error neighborhood. The profile then yields
linear error. This is why an intermediate bound that does not vanish with
ε is not a gap in the proof.

The code tests 1,086 exhaustive labeled subsets, 90 seeded weighted cases,
three weighted nonzero-error theorem instances, four small closed-form
cross-checks, and a larger exact-formula instance. It executes 33,889 exact
assertions. Most arbitrary small domains fail the theorem's hypotheses and
are used only to check unconditional intermediate identities.

## What is not claimed

- No global Szemerédi, Ramsey-number, or U⁴ inverse-theorem improvement is
  deduced merely from this local theorem.
- No optimality claim is made for density exponent 5/4, the finite-error
  coefficient 13/50, the constant 1024, or the quadratic-rank threshold.
- The sharpness of 1/4 is a joint small-error/small-normalized-uniformity
  statement, not a complete fixed-uniformity extremal classification.
- Rank-independent-of-ε affine repair on a quadratic domain is not
  rank-independent-of-ε repair of approximately quadratic labels.
- The relative result on a coset does not automatically extend to a larger
  group. The Z/4 → Z/2 obstruction is given in the article.
- No external peer review, worldwide novelty certification, or Lean build
  has been performed.

## Comparison with existing ProveIt refinements

The inspected consolidated README already describes full-domain affine graph
energy profiles, coset stability, Bohr/Freiman extension, and transport-sensitive
local rigidity. Their hypotheses are different from the present relative
Fourier-uniform-domain hypothesis. The current article does not re-label those
results as its own or claim to replace their statements universally.

For the graph Γφ of a map on A, the exact normalization is

    E(Γφ) = (1−ε) E(A)
          = (1−ε) |G|³ (α⁴ + u⁴).

Consequently, if γ=E(Γφ)/|A|³, then γ=(1−ε)α(1+u⁴/α⁴).
A sparse uniform set has γ near α, not near 1. Confusing these quantities would
incorrectly turn a relative theorem into a full-energy stability assertion.

The concrete high-agreement branch gives one agreement subset of relative
size at least 1−13ε/50, on which the map is a Freiman homomorphism of every
order and comes from one global affine map. This is a strengthening under
additional hypotheses of the small-restriction conclusion used around
Corollary 7.6, not an unconditional replacement.

## Suggested formalization order

1. Normalized weighted configurations and graph energy dictionary.
2. Autocorrelation variance and exact triangle second moment.
3. Finite supported modes and weighted interpolation.
4. Ambient group-valued BLR correction and weighted return.
5. Pointwise triple links and both types of marked-pair Fourier bounds.
6. The local profile, scalar constant lemma, and affine separation.
7. Spectral certificate and odd-characteristic matrix-rank corollary.

The article gives proposed theorem names only. Place the files in a new
research directory without changing `gowers-proof-status.json` or
`FORMALIZATION_STATUS.txt`. Such a change would require actual compiled proofs.
