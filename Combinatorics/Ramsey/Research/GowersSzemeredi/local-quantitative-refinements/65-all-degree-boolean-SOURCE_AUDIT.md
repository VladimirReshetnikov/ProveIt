# Source audit and novelty boundary

## Scope of inspection

The target is the `Combinatorics/Ramsey` subtree of
`VladimirReshetnikov/ProveIt`, particularly the Gowers Section 17
selected-frequency/phase-removal stage. Repository contents were read through
the GitHub connector. Relevant prior manuscripts were found and read through
the user's Library; they were not inferred from filenames alone.

The target subtree and its research inventory were inspected before choosing the
Boolean phase-integration problem. The inventory already contains many local
refinements, so the present package does not re-present the existing cubic or
canonical-family results as new.

## Repository interface snapshot

The two relevant interface files were read at the explicit commit

    8c40adc24df2e6f338cea728887772aead4bf144

with these returned Git blob identifiers:

| Path under `Combinatorics/Ramsey/Lean/GowersSzemeredi/` | Git blob |
| --- | --- |
| `Sections17_18.lean` | `18495f50475835ca1c497d85b0052215f865b8ca` |
| `Definitions.lean` | `97113b7afa6925a2dd4b76641eeaeff09597ab6a` |

`Sections17_18.lean` records `proposition_17_2` as a proposition-valued
definition with prime cyclic modulus, factorial invertibility, and phase degree
at most `k+1`. Its header explicitly distinguishes statements from proofs.
No trusted Lean theorem was inferred from the existence of that definition.

`Definitions.lean` was read through the polynomial/multilinear definitions.
Its `IsMultilinear` includes lower-order and constant square-free monomials.
The paper delivered here uses actual homogeneous multilinear maps. Its Fourier
averages are normalized and its ambient group is a Boolean vector space.
These differences are stated explicitly in Section 10 of the article.

The aggregate research README and `43-boolean-phase-FORMALIZATION.md` were
also inspected. Their inspection was separate from the pinned interface reads.
No claim of a complete checkout or repository-wide build is made.

## Decisive preceding manuscript

Title:

> Exact Boolean Obstruction Energies: Derivative periods, sharp quartic–sextic
> integration, and dimension-free higher-degree extremizers.

It is dated 6 October 2026 and was prepared with ChatGPT for Vladimir Reshetnikov
and ProveIt. The complete 1,512-line TeX source was read from the Library entry
`article(20261007-014512).tex`; the title disambiguates the generic filename.
Its corresponding PDF is 23 pages. Its own recorded comparison snapshot is

    5c9a442d263632fdcd4e9690154c12c2dcc70b53

which is not claimed to be this package's source revision.

Relevant prior results:

- Exact canonical energy `M(C_d)=1-(d+1)/2^d` in every degree and dimension.
- Boolean integration criterion and an explicit coordinate primitive.
- Cubic projective/spectral bound and the shear method.
- Pure-defect/canonical recognition and first-slot radical observations.
- Universal nonintegrable bound `1-min(d+1,7)/2^d`, exact only through degree six.

Relevant explicit questions:

- Research Question 1: whether the septic maximum is `15/16`.
- Research Question 2: whether the canonical formula is universal in all degrees.
- Research Question 4: endpoint tensors and maximizing functions in degrees five
  and six, and phase stability.

The new article answers Questions 1 and 2, and the tensor part of Question 4.
It does not claim to answer the function/phase-stability part.

## Earlier Boolean manuscript

*Sharp Boolean Phase Integration from Gowers Derivative Spectra: Exact cubic
obstruction ranks, repeated-variable certification, finite-abelian
orthogonality, and a quartic reduction*, dated 6 October 2026, was surfaced in
the Library as `boolean_phase_integration.tex`. Relevant source information and
its formalization notes were inspected. The current package does not claim a
full independent reread of this earlier manuscript; the needed results are
reproved directly, and their presentation in the newer manuscript was read.
Its own comparison pin is `797aa3cfe967349322b806692a500f677f7047cf`.

## Primary external sources

1. W. T. Gowers, *A new proof of Szemerédi's theorem*, GAFA 11 (2001), 465–588.
   DOI: `10.1007/s00039-001-0332-9`.
   The public PDF and the page images around Lemma 17.1 and Proposition 17.2,
   printed pages 577–578, were consulted. The connection is the
   selected-frequency-to-phase step, not an unchanged theorem over the same
   ambient group.

2. Jonathan Tidor, *Quantitative bounds for the U^4-inverse theorem over low
   characteristic finite fields*, Discrete Analysis 2022:14, 17 pp.
   DOI: `10.19086/da.38591`; arXiv `2109.13108v2`.
   The primary paper and page images of Definition 3.1 and Proposition 3.5 were
   consulted. The nonclassical integration framework is established background,
   not a discovery of this package.

External targeted searching did not establish publication priority for the new
extremal formulation. The article therefore makes a precise comparison with the
inspected project questions and does not claim an exhaustive literature review
or resolution of a famous published open problem.

## What is new here

The exact identity

    {z : T_z is integrable} = first-slot radical of Phi_T

makes the measure of integrable contractions exactly `2^(-r)`. Once radical
codimension one is isolated as the canonical case, all other nonintegrable
tensors have at least a `3/4` fraction of nonintegrable contractions. Inserting
the sharp preceding-degree bound closes the universal induction and supplies a
strict noncanonical gap. It is this use of the preceding-degree *extremal
bound*, rather than a fixed higher-order support coefficient, that is decisive.

The resulting new conclusions are the all-degree universal maximum, complete
endpoint tensor classification, radical-sensitive and recursive caps, a finite
rigidity window, explicit endpoint-class counts, repair geometry, and the
stated amplitude and robustness consequences. Elementary corollaries are
presented as consequences rather than independent breakthroughs.

## Boundaries

No new global Szemerédi estimate, general low-energy inverse theorem,
unsymmetric certification threshold, mixed-function theorem, or odd-prime
analogue is asserted. The source files in the archive are new deliverables;
prior manuscripts and third-party paper PDFs are not redistributed.
