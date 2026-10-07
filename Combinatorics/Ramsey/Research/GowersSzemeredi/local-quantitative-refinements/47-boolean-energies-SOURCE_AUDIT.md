# Source audit and comparison ledger

## Repository scope

Requested scope:

https://github.com/VladimirReshetnikov/ProveIt/tree/main/Combinatorics/Ramsey

The repository directory and the current research collection were inspected
through the GitHub connector. The local-quantitative-refinements collection
already covered many density, arrangement, phase-partition, Fourier, and
interpolation refinements. The selected target instead came from the latest
Boolean phase-integration draft's explicit unresolved quartic question.

Observed branch reference at final inspection:

`5c9a442d263632fdcd4e9690154c12c2dcc70b53`.

Actual inspected interface blobs:

| Path relative to Combinatorics/Ramsey | Git blob |
|---|---|
| Lean/GowersSzemeredi/Sections17_18.lean | 18495f50475835ca1c497d85b0052215f865b8ca |
| Lean/GowersSzemeredi/Definitions.lean | 97113b7afa6925a2dd4b76641eeaeff09597ab6a |

The branch reference is provenance, not a claim that a repository-wide build
was performed. No repository write action was taken.

## Primary mathematical sources

### W. T. Gowers (2001)

*A new proof of Szemerédi's theorem*, Geometric and Functional Analysis
11 (2001), 465–588, DOI 10.1007/s00039-001-0332-9.

https://www.cs.umd.edu/~gasarch/TOPICS/vdw/sz-thm-gowers-proof.pdf

Inspected Section 17, including the PDF page image of printed page 578
(Proposition 17.2 and its proof). The article's local crosswalk is to this
phase-removal stage, not to a new complete density-increment proof. The
repository statement explicitly uses phase degree k+1, prime modulus, and
factorial invertibility. Its `IsMultilinear` predicate is multiaffine.

### Jonathan Tidor (2022)

*Quantitative bounds for the U^4-inverse theorem over low characteristic
finite fields*, Discrete Analysis 2022:14, DOI 10.19086/da.38591.

https://arxiv.org/abs/2109.13108

The primary paper's Definition 3.1 and Proposition 3.5 identify and integrate
nonclassical symmetric multilinear forms. This is credited background. The
manuscript supplies a direct Boolean coordinate proof of the specialization
it needs, rather than presenting the integrability criterion as new.

### Preceding project draft

*Sharp Boolean Phase Integration from Gowers Derivative Spectra*, prepared
with ChatGPT for Vladimir Reshetnikov and the ProveIt project, 6 October 2026.

Inspected Library source: `boolean_phase_integration.tex`, 1938 source lines.
Its own repository comparison pin was `797aa3cfe967`.

Directly read: definitions and selected cube identity; explicit Boolean
integration; projective orthogonality and shear; exact cubic obstruction
ranks; quartic normal-form reduction; two-dimensional quartic calculation;
and Research Question 1.

Baseline established there:

- Symmetric integrability iff the repetition defect vanishes.
- The selected-energy gauge identity.
- E_T(f) <= average_z 2^(-rank(Phi_T(z))/2).
- Exact cubic energy determined by the alternating defect rank.
- E_{C_d}(1) = 1 - (d+1)/2^d.
- Exact binary quartic maximum 11/16.
- Universal quartic reduction to the pullback of the canonical tensor,
  leaving 11/16 <= M <= 3/4 in arbitrary dimensions.
- Explicitly open: whether the optimizing function's extra coordinates can
  improve that quartic maximum.

The new manuscript reproduces the background proof components needed for
its conclusions, so correctness does not rest on unreviewed prior assertions.

## Present refinements

1. Retain exact even-direction periods of iterated derivatives, including
   zero-valued functions. Use them to prove the sharp fixed-derivative cap
   E_{u^m}(∂_z f) <= 1 - 2^(1-m) when u(z)=0.
2. Close the canonical induction in every degree and dimension, without any
   assumption that the optimizer descends to the tensor's binary quotient.
3. Classify pure defects in every degree >=4. Bianchi compatibility already
   forces their alternating value to have rank two.
4. Reduce one-dimensional defect images to two active coordinates modulo an
   integrable tensor, while retaining the separate optimization question.
5. Prove sharp 7/32 support for non-pure symmetric trilinear maps and propagate
   it by contraction to all higher degrees.
6. Establish universal sharp symmetric thresholds in degrees four, five,
   and six; improve the all-degree nonintegrable upper bound.
7. Give an exact deficit recursion and explicit noise margins.

These are claims proved in the manuscript and checked against the stated
baseline. They are not a certification of historical first priority.

## Verification and boundaries

The delivered standard-library verifier uses exact arithmetic, includes
formal cube monomial identities and zero amplitudes, and reproduces the
printed support census. Its finite cases are recorded precisely in JSON.
The continuous optimization and arbitrary-dimensional claims rest on the
proofs, not on finite tests.

No Lean proof or build, independent peer review, exhaustive literature
survey, mixed-function analogue, odd-characteristic analogue, local-domain
analogue, or new global Szemerédi bound is claimed.
