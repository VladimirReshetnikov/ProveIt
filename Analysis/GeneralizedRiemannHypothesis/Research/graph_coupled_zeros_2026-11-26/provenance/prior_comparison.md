# Prior-result comparison for graph-coupled completed L-functions

## Snapshot and actual review depth

Repository: `VladimirReshetnikov/ProveIt`, commit
`4d7990202f9f106b2ffe8c209f073ad01d5e1987`.

The requested `Analysis/GeneralizedRiemannHypothesis` directory contains two
different bodies of material. Its top-level README catalogs 61 already
organized research packets under `Research/`. A further 39 ZIP archives are
under `docs/incoming/` **inside that GRH directory**. Looking only at the
top-level catalog would miss the later zero-recovery and moment papers.
The root repository's `docs/incoming/` contains an intake README, not those
39 archives.

All 61 organized packet READMEs were retrieved and content-screened. Their
source paths and Git blob identifiers are in `organized_readme_manifest.json`.
Five relevant local-interpolation source files were also read separately.
The full source files remain available in the pinned repository and are not
redistributed here. This was not a proof audit of all 61 packets.

All 39 later ZIPs were retrieved. Each binary's Git blob SHA-1 was recomputed
and matched to the repository tree. Every archive member was inventoried;
TEX, Markdown, text, and JSON members smaller than 1 MB were extracted for
search and inspection. Packet descriptions and selected theorem/proof
passages were read. The full proofs in all 39 packages were not reviewed.
`incoming_archive_manifest.json` records the exact scope, filenames, blob
identifiers, SHA-256 digests, and sizes. The 39 archives total 19,550,402 bytes.

## Topics already occupied

| Packet or group | Existing contribution encountered | Relation to the proposed graph theorem |
|---|---|---|
| `li_ritz_zero_recovery.zip` | A moment pencil recovers individual zeta zeros; a two-term logarithmic Ritz error law; a finite simplicity and enclosure test; Hankel determinant asymptotics; a shifted-height Dirichlet version. | Ordinary finite-moment zero recovery is already developed. It is not the new contribution here. |
| `zeta_zero_moment_bounds.zip` | Alternating multiplicity-sensitive errors from high-order power sums; spectrum recovery from successive errors; a sharp attainable endpoint for incomplete moments. | Avoid presenting elementary symmetric-function bounds or moment extremizers as new. |
| `grh_zero_certificates_2026-11-26.zip` | Separation-free bounds between Hermite-matrix positivity defect and imaginary parts of roots, with sharp exponents and certified moment errors. | Generic noisy PSD zero certificates already occur. |
| `sparse_dirichlet_zero_tests.zip` | Sparse logarithmic-derivative/Hankel tests, independent integer strides, a negative-index formula, exceptional rational center sets, and sampling designs. | Sparse finite positivity by itself is not new relative to the incoming set. |
| `dirichlet_zero_recovery.zip` | Recovery of prime weights from zero residues despite a positive fraction of erased or corrupted observations; stable bounded-noise recovery. A separate paper studies omitted primes from zero-gap distributions. | An unrelated analytic error-correction theorem is already present. |
| `grh_zero_count_certificate.zip`, `dirichlet_inverse_problems.zip` | Finite rational-binomial zero counts and finite phase/logarithmic-derivative counts in the Euler-product half-plane. | Counting zeros from real data is occupied. |
| Many prime-window packets | Filtered prime races, sparse one-sided Mellin criteria, exact growth abscissae, finite-scale prime products, covariance, coalescing scales, balanced windows, spectral rigidity, and reconstruction of characters or zeros. | A new filter differing only cosmetically from these would have substantial overlap. |
| `symplectic_rank_blindness_2026-11-26.zip` | Rank statistics versus full matrix-law separation in symplectic projections, with exact total-variation formulas. | Extends earlier finite-field block work; does not concern root polynomials coupled by a graph. |
| Earlier graph-tower packets | p-adic valuations and stabilization of spanning-tree counts in graph towers; a separate signed-cycle spectral optimization. | The graph and spanning-tree terminology overlaps, but the objects and theorems differ. No logarithmic-derivative coupling of real-rooted inputs was found there. |
| Earlier Lubin--Tate packets | Exact multibranch interpolation cutoffs, contact-depth bounds, carry criteria, and all-precision formulas at small contact depths. | A possible alternative research route, unrelated to the chosen theorem. |

The closest local-jet source was read in full because it was considered as
an alternative direction: it gives the exact cutoff in terms of the pole
order of the reciprocal Lagrange denominator, then sharp bounds and a
base-p carry criterion. That direction was not selected.

## What the comparison supports

No inspected packet description or searched TEX source states the following
combination:

1. Couple monic real-rooted input polynomials by a connected weighted graph
   using `prod(F_i) det(L + diag(F_i'/F_i))`.
2. Identify that polynomial exactly with the characteristic polynomial of
   a compression modified by the graph pseudoinverse.
3. Express an edge-weight change as a rank-one positive update with
   effective-resistance denominator `1 + h R_ij`.
4. Deduce an exact resistance formula for the sum of output roots and
   account for repeated or shared input roots by a complementary-nullity
   formula.
5. Apply the zero-reality and collision statements to the completed
   zeta/Dirichlet functions after the supplied RH/Dirichlet-GRH input.

This establishes nonduplication relative to the material screened at the
pinned repository snapshot. It does **not** establish worldwide priority,
and it does not certify the correctness of the earlier packets.

## Classical frameworks that must be credited

* J. Borcea and P. Branden, *Applications of stable polynomials to mixed
  determinants: Johnson's conjectures, unimodality, and symmetrized Fischer
  products*, arXiv:math/0607755. Determinants formed from Hermitian matrices
  and diagonal half-plane variables are part of established stability
  theory. The basic reality-preservation argument is not itself a new
  theorem.
  <https://arxiv.org/abs/math/0607755>
* R. Pereira, *Differentiators and the geometry of polynomials*, J. Math.
  Anal. Appl. 285 (2003), 336--348, DOI 10.1016/S0022-247X(03)00465-7.
  Compression of a diagonal root matrix gives the zeros of a derivative.
  The one-vertex specialization is classical.
  <https://doi.org/10.1016/S0022-247X(03)00465-7>
* P. Chebotarev and E. Shamis, *Matrix-Forest Theorems*,
  arXiv:math/0602575. The rooted-forest expansion of a Laplacian determinant
  is classical and should be explicitly attributed.
  <https://arxiv.org/abs/math/0602575>
* J. Reiffenstein, *Higher-order interlacing for matrix-valued meromorphic
  Herglotz functions*, J. Math. Anal. Appl. 514 (2022), 126260,
  arXiv:2108.10746. General matrix Herglotz interlacing is established.
  <https://arxiv.org/abs/2108.10746>
* S. Simonov and H. Woracek, *Local Spectral Multiplicity of Selfadjoint
  Couplings with General Interface Conditions*, Integral Equations and
  Operator Theory 96 (2024), article 18. This is a nearby general theory
  of multiplicities for selfadjoint couplings, not a source establishing
  the exact arithmetic graph formula by itself.
  <https://doi.org/10.1007/s00020-024-02767-6>

Targeted searches located these general precedents but did not locate the
exact graph compression and resistance identity above. The appropriate
claim is an independently derived, apparently unreported formulation
with provisional literature novelty, not a certified first discovery.

