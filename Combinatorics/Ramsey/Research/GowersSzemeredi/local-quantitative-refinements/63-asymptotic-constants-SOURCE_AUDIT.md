# Source audit

Inspection date: 7 October 2026, UTC.

## Repository snapshot

- Repository: <https://github.com/VladimirReshetnikov/ProveIt>
- Scope: `Combinatorics/Ramsey`
- Pinned commit: `d7b83fa1fe60478e3ed8525d58f747a1d76e35c2`
- Commit date: `2026-10-07T04:15:32Z`
- Commit message: “Merge incoming research reports after the progression-variance checkpoint”.
- Pinned directory:
  <https://github.com/VladimirReshetnikov/ProveIt/tree/d7b83fa1fe60478e3ed8525d58f747a1d76e35c2/Combinatorics/Ramsey>

The corrected Gowers transcription, consolidated research article, research
index, and relevant later source reviews were read. The index lists 46 reports;
the consolidated TeX contains the first 33. Later reports affecting the present
comparison were inspected through their supplied source/review records.

## Exact source identities

| Source | Git blob | Original bytes |
|---|---|---:|
| Corrected Gowers TeX | `41085a0efde8c1932e86e80c791984f52841c22e` | 379,608 |
| Consolidated research TeX | `32087ba1eeff55d5c3c68cbd31a7777dce427c65` | 3,309,296 |
| Research index README | `689dbd37cf1a495a38124a62c20aff90460ca7a5` | 173,195 |

These blobs can be retrieved through the repository's Git data API, for example:
<https://api.github.com/repos/VladimirReshetnikov/ProveIt/git/blobs/41085a0efde8c1932e86e80c791984f52841c22e>.

The local text copies used in the analysis each have one additional terminal
newline compared with the corresponding Git blob. Their SHA-256 fingerprints
are therefore fingerprints of the working copies, not of the original blobs:

| Working copy | SHA-256 |
|---|---|
| Corrected Gowers TeX | `e06fd9cc6f5e3234a8f5d0c2cb8960e6b18fce70198de944e71f0f79531bc5b6` |
| Consolidated research TeX | `b3377e930c7b627e5a246b317903cd9a660b83aa1d34bbdf2a120ef942c50850` |
| Research index | `f32aabcc379f30e52f54af85b8eaf3b744d2cdb03c42a53aa08d1d62cc420b1e` |

Original source files are not redistributed in this archive.

## Separate immediate predecessor

*Local Phase Removal and Cubic Rigidity in Gowers' Szemerédi Framework*,
prepared by ChatGPT for Vladimir Reshetnikov, dated 7 October 2026.

- Inspected file: `article(20261007-014857).tex`.
- Size: 126,709 bytes.
- SHA-256: `9cd0a536250370bb2126de79bc063ba20d6c48e351b5224f08697b95f3a24343`.

This source supplies the sliding-window method, explicit phase polarization,
positive-cover analytic interface, and previous coefficient

    v_k / Dhat_k,
    Dhat_k = sum_j binom(k,j) (2/(3k))^j * 2/(j+2)!.

The new contribution is the smaller dimension-dependent face cost,
its exact nonnegative convolution identity, asymptotic optimality,
and the finite construction's full joint-scale profile. The old interface is
reproved with attribution so the new article can be read independently.

## Comparison claims used

| Topic | Inspected baseline | Present result |
|---|---|---|
| Odd-order high-order norm ratio | Source 29: limiting interval `[1/3,1/2]` | Exact limit `1/3`, uniform explicit rate |
| Fixed fourth-order ratio | Source 45: upper `(832/4795)^(1/4)` | No claim to improve this fixed-order value |
| Quartic centered cube term | Earlier reports: exact parallelogram coefficient `P_d` | Optimal coefficient `P_d c_d` tends to `P_d/3` |
| Local phase removal | Immediate predecessor: ceiling fraction tends to about `0.80542` | Ceiling fraction tends to 1 |
| Finite localization | Explicit width and rounding losses required | Exact finite formula and scale profile for this construction |

Sources 28 and 29 contain different norm comparison results. The specific
central-binomial bound tending to `1/2` is attributed to Source 29. Source 04
already gives the exact third-order value `1/sqrt(2)`. The article does not
reintroduce the previously rejected pointwise quartic lower bound obtained by
discarding the signed higher-order remainder.

## Normalizations and scope

- All `U^d` norms in the norm-comparison sections use normalized averages.
- Centering and real-valuedness are explicit; odd order excludes real
  nontrivial characters of order two.
- Local cube sums are unnormalized, with
  `C_r(u)=N^(r+1)||u||Ur^(2^r)`.
- The local output quotient is `sum_Q C_(k+1)(1_Q u)/(M U^(k+2))`.
  The finite theorem uses `U=L+1`; the asymptotic optimum uses the maximum cell
  size. These agree for the partitions produced in the theorem.
- Input boxes have a common invertible difference, and their phase extends
  to a multi-affine polynomial in the box coordinates. The prime exceeds
  `k+1` in the nontrivial finite range, so the polarization factorials invert.
- The limit defining the best local coefficient first takes box width to
  infinity for fixed degree. The separate joint-scale corollary concerns
  the explicit finite coefficient, not an optimality claim for every finite
  construction.

## Literature and verification status

The original Gowers paper and standard primary references are cited in the
article. The targeted literature check is recorded in `review/literature_scope.md`.
It did not identify an identical statement in the inspected sources, but this
does not certify publication priority. The manuscript claims a resolution of
specific questions in the inspected project reports.

The included proofs and internal reviews were produced by ChatGPT instances.
Finite exact checks are supplementary. No Lean certification or external peer
review is claimed. No current global bound for Szemerédi's theorem is replaced.
