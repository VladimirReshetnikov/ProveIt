# Source comparison and scope of the analysis

Date: 27 November 2026.

Repository: [VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt/tree/6d284fcf75bc3a91bb2e79ba7636f94724bff62c/Analysis/GeneralizedRiemannHypothesis).
Pinned commit: `6d284fcf75bc3a91bb2e79ba7636f94724bff62c`.
All paths below are relative to `Analysis/GeneralizedRiemannHypothesis/`.

## Corpus and review scope

The project describes a merged article incorporating 142 reports and 42 further
placed research reports. The pinned tree also contains ten ZIP archives in
`docs/incoming/`. The article's 20 section files and its README/root source were
retrieved; the relevant arithmetic and symplectic arguments were read closely.
The placed research tree and all ten incoming archives were inspected for
overlap with the two proposed extensions.

This is a focused mathematical investigation. It is not a complete audit of all
770 pages or all 997 statements described by the merged article. Retrieval of
a file, or a hash match, does not establish that all its mathematics was checked.

`source_inventory.tsv` records 39 retrieved source files and archives, including
all ten incoming ZIPs, whose Git blob SHA-1 values match the pinned repository.
For text responses with one transport-added terminal newline, the terminal
newline was removed only when this recovered the exact recorded Git blob hash.
The manifest makes those cases explicit.

## Arithmetic dependencies and additions

| Source | Existing result used or compared | Contribution in the new note |
|---|---|---|
| `Article/sections/dir.tex`, `dir:lem:bias` | Arbitrarily small character bias for the C(log q)^2 prime pool under Dirichlet GRH | Included with a smooth-cutoff proof; not claimed new |
| Same, `dir:thm:quotient` | The obstruction lives in a quotient of order at most floor(1/a) | Retained as the structural starting point |
| Same, `dir:thm:disjoint-growing`, `dir:thm:disjoint-mixing` | Arbitrary-density quotient laws and quadratic/cubic mixing in the stated ranges | Extended to a complete sparse-quota classification at every fixed positive retained density |
| `Research/grh_quadratic_fibre/quadratic_fibre.tex` | Quadratic transition and scalar finite-population correction | Extended to arbitrary finite abelian quotients with a uniform signed-measure expansion |
| `docs/incoming/grh_quarter_density.zip` | Exact C4 and C2 x C2 support conditions and independent-exception coupling bound t(t-1)/(2m) in TV | No new claim about exact quarter-density support; the new estimate uses ht/m bounded and does not require t=o(sqrt(m)) |

The principal addition is a necessary and sufficient sparse mixing criterion,
complete classification of normalized pointwise limit profiles, and realization
of every allowed profile, including exact reciprocal-density endpoints. A
prefactor-free character estimate is needed when the effective defect rate
tends to infinity arbitrarily slowly. The finite-population expansion supplies
the explicit 1/h correction and O(h^-2) remainder.

The arithmetic note uses precisely the Dirichlet GRH statement exported by the
supplied project. It uses no simplicity or independence assumption on zeros,
and no GRH for a broader class of L-functions. The finite probability results
are unconditional. We did not rerun the upstream Lean build.

## Symplectic dependencies and additions

| Source | Existing result used or compared | Contribution in the new note |
|---|---|---|
| `Article/sections/spn.tex`, `spn:thm:complete-law`, `spn:prop:residual` | Finite-field compression and residual-Gram reduction | Used as the starting direction and rederived for local rings |
| Same, `spn:thm:padic` | Exact local theorem for a source with one symplectic pair | Extended to arbitrarily many source and target pairs in the stated stable range |
| Same, `spn:thm:padic-tangent`, `spn:thm:padic-lifting` | Tangent/lifting tools and general local error bounds | Combined smooth kernel-zero and kernel-one contributions give an exact sign and exact TV equality |
| Same, `spn:q:symplectic` | Open question on multi-pair local laws and first-digit persistence | Answered for n>=a+b+min(a,b)-1; optimal range remains open |
| `docs/incoming/grh-two-open-questions.zip`, `symplectic/symplectic.tex` | Finite-field singular-residual optimal test, limiting profile, and O(ab) rank chain | Explicitly credited; the new claim is persistence at all DVR precisions |
| Incoming rectangular/uniform symplectic reports | Stronger finite-field laws across aspect ratios | No claim to those finite-field results; local precision is the extension |

The companion also establishes the exact Fourier formula for alternating Gram
densities, a conductor recursion, the bounded-density threshold c>=s-1 for
s>=2, and the sharp uniform convergence exponent 2c-2s+3. These statements and
the local testing result include residue characteristic two and arbitrary
ramification. They are unconditional.

## Incoming archive inventory

The ten inspected archives at the pinned revision are:

- `dirichlet_li_recovery.zip`
- `gaussian-singular-moduli.zip`
- `grh-two-open-questions.zip`
- `grh_quarter_density.zip`
- `grh_uniform_extensions_2026-11-27.zip`
- `grh_zero_filter_tradeoff.zip`
- `prime_cubature_grh_2026-11-27.zip`
- `prime_legendre_codes_2026-11-27.zip`
- `rectangular_symplectic_blocks.zip`
- `uniform_symplectic_blocks.zip`

The incoming symplectic and quarter-density reports are material predecessors
and were incorporated into the papers' comparisons. Exact hashes are recorded
in `source_inventory.tsv`.

## Prior literature and historical priority

Both manuscripts cite primary mathematical literature relevant to their
methods. Finite-group character formulas, hypergeometric/binomial and Poisson
approximation, local-field lifting, and p-adic random-matrix limits all have
substantial prior literature. Those general methods are not claimed as new.

The targeted source and literature checks did not locate the exact combination
of statements proved in the two notes. This supports treating them as proposed
research contributions relative to the inspected collection. It is not a
worldwide priority certificate; expert review and a broader literature search
would be needed for a publication claim.

## Validation and formalization status

The two papers contain written proofs. Separate agents reviewed the mathematical
arguments independently of the drafting agents. Those reviews are AI-assisted
internal reviews, not external peer review or a proof-kernel certification.
The exact scripts test finite identities, signs, normalizations, and examples;
they do not prove the infinite arithmetic or local-ring families by enumeration.
No new Lean theorem or axiom was introduced, and no claim of formal verification
is made for these new results.
