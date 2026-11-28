# Source audit and novelty boundaries

## Pinned source

Repository: VladimirReshetnikov/ProveIt

Commit: 42efb893353a150857f5c8e2f9e7732d0d46f15f

[Pinned GRH directory](https://github.com/VladimirReshetnikov/ProveIt/tree/42efb893353a150857f5c8e2f9e7732d0d46f15f/Analysis/GeneralizedRiemannHypothesis/)

The full Git tree metadata for the article and current incoming directory
is in source_manifest.json. The 44 downloaded article text files were
compared against their exact Git blob SHA-1 identities; all matched.
The per-file hashes are in retrieved_article_hashes.json.

All 26 current incoming ZIP archives were inventoried and their text/code
extracted for comparison. Their exact Git blob hashes also matched; see
incoming_archive_hashes.json. Paths beginning docs/incoming below are
relative to Analysis/GeneralizedRiemannHypothesis/. No full mathematical verification of the
982-page merged collection is claimed.

## Input theorem inspection

The article README reports 209 merged research reports, 982 pages, and
1,321 numbered mathematical results. Its status columns are overlapping;
they must not be interpreted as a disjoint partition. The README
explicitly says the merge is not an independent review or recomputation.

The vendored upstream development is pinned to:

    lsernau/grh-lean
    72fead102f663d5c7a407964a13dc0cf9d977207

The files read include its README, grh/README.md, grh/src/Statements.lean,
and grh/src/Main.lean, together with the ProveIt Lean README.

The exported statements concern:

- the Riemann hypothesis for the Riemann zeta function;
- Dirichlet L-function nonvanishing strictly to the right of 1/2;
- Dirichlet L-function zero location in the open critical strip;
- its restriction to primitive Dirichlet characters.

They do not assert zero simplicity, noncoincidence of different spectra,
or a general automorphic/Artin GRH. Main.lean exports results derived
through New.grh. This source inspection did not rebuild the imports or
check the entire kernel dependency closure.

No conclusion in the new report relies on a claim that such a rebuild
was performed. The only GRH-dependent application is the identification
of the ordinate-built Poisson processes with Li-coefficient semigroups.

## Comparison with the current reports

### Four frequencies

Relevant prior files:

- Article/sections/fil.tex — two-frequency exact results and wide-step
  asymptotics.
- docs/incoming/kozma_oravecz_three_frequency_2026-11-28.zip,
  three_frequency_gaps.tex — all three-frequency integer-ratio cases.
- docs/incoming/positive-fourier-zeros.zip,
  positive-fourier-zeros/kozma/gaps.tex — an algebraic rule for general
  three-frequency progressions, and a question about four or more
  frequencies.

The new assertion treats four frequencies for every integer ratio,
with a certified analytic branch, exact duality, nonattainment, and
uniqueness. The even-ratio half-period case is elementary and is
included for completeness. The odd-ratio branch is the substantive
extension.

Primary question:

G. Kozma and F. Oravecz, *On the gaps between zeros of trigonometric
polynomials*, Real Analysis Exchange 28 (2002/03), 447–454, Question 1.

https://arxiv.org/html/math/0601021v1

Their question asks for the maximum zero-free interval when the
arithmetic-progression step b is at least twice the starting frequency N.
The new family has b=mN and four positive frequencies. The result is an
exact contact-system characterization; no elementary closed formula for
the arbitrary progression is claimed.

### Ehrhart critical windows

Relevant prior files:

- docs/incoming/multipartite-ehrhart.zip,
  multipartite-ehrhart/zeros.tex and combinatorics.tex.
- The concluding questions in multipartite-ehrhart.tex.

That report gives the matching-deletion identity and strict first-order
regimes around c* sqrt(d) in even dimension and 2 c* sqrt(d) in odd
dimension. It explicitly excludes the multiple-root equality cases
and asks for the local expansions and effect of rounding.

The new report supplies the two distinct critical exponents, normal
forms, local double-root parameters, and rounding conclusions. It also
includes a direct lattice-counting proof of the exact matching-deletion
identity, so that this identity is not imported solely from an unchecked
report.

The result is local in a fixed index j. It neither locates the first
off-line root globally nor settles the all-width complete-bipartite
canonical-line question.

Analytic primary references:

- NIST DLMF, Section 15.8:
  https://dlmf.nist.gov/15.8
- Flajolet and Sedgewick, *Analytic Combinatorics*, Chapter VI:
  https://algo.inria.fr/flajolet/Publications/book.pdf
- Higashitani, Kummer, Michałek, *Interlacing Ehrhart polynomials of
  reflexive polytopes*:
  https://doi.org/10.1007/s00029-017-0350-6

### Continuous mixtures and minimal counters

Relevant prior files:

- Article/sections/rec.tex and spn.tex.
- docs/incoming/cycle-complements-and-dirichlet-zero-matching.zip,
  cycle-complements-and-dirichlet-zero-matching/
  03-hard-distance-matching/matching.tex.
- The finite-observation and critical-recovery incoming reports.

The binary Hellinger exponent of order T log T, including bounded
microscopic coarsening, is already present. It is explicitly not claimed
as a new result.

The new assertions are a lower matrix bound uniform over all coefficient
vectors and all bounded microscopic partitions, continuous-mixture
minimax estimation, selection of exactly d independent ordinary count
channels (d−1 with known total), and a growing-resolution obstruction
for the leading information scale.

Primary analytic input:

E. Bombieri and A. Perelli, *Distinct zeros of L-functions*, Acta
Arithmetica 83 (1998), 271–281.

https://doi.org/10.4064/aa-83-3-271-281

Theorem 2 supplies the joint short-interval central limit theorem.
The hypotheses are verified for Dirichlet L-functions on page 273.
The first-moment bound used for growing bins additionally uses the
L1 Dirichlet-polynomial approximation on page 279 and bounded second
moments from Lemma 2. Weak convergence alone would not justify that
first-moment step.

## Ideas investigated but excluded

- The higher-rank Gram exponent of order n^(3r−2) was found already in
  the current gram_column_number report and is not represented as new.
- No general five-frequency or arbitrary-ratio theorem was proved.
- No all-width complete-bipartite canonical-line theorem was proved.
- No bounded additive improvement to the positive-filter support excess
  was proved.

## Review and evidence

The three mathematical arguments underwent independent cross-review.
That review clarified d≥2 in the Ehrhart family, the odd-m scope of the
eight-atom theorem, the definition of support length by a containing
arc, and the scale-specific meaning of information collapse.

The final packaged witnesses were freshly replayed. See validation/
and the JSON reports in checks/. The computational proof status differs
between exact interval certificates, finite algebra checks, and
illustrative floating-point calculations, as explained in the paper.

Targeted searches of the inspected sources and primary literature did
not locate the exact new statements. This is not an exhaustive
certification of global publication priority.
