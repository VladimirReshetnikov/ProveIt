# Source audit for Report179

Audit date: 3 October 2026. All comparisons were read-only. This is a bounded
source and overlap review, not a global historical-priority determination.

## Sequence and exact prior results

The official OEIS source record for [A328716](https://github.com/oeis/oeisdata/blob/main/seq/A328/A328716.seq)
was inspected during the source review. It gives the diagonal Bessel coefficient
formula, attributed to Ilya Gutkovskiy on 26 October 2019, and the leading
equivalent with numerical even/odd constants, attributed to Vaclav Kotesovec on
27 October 2019. The report credits both. The twenty recorded initial terms
were independently regenerated exactly. No proof, analytic Bessel definitions of
the numerical leading constants, correction series, or asymptotic literature
citation was present in that inspected record. Absence from one entry is not
absence from the literature.

The ordinary A328716 OEIS webpage did not load through one retrieval route.
The official source repository supplied the record; a later writer's attempt
to re-open the GitHub record returned a cache miss. Those retrieval failures
were not treated as evidence about the sequence. The source review observed an
internal last-change date of 27 October 2019 and a repository file modification
date of 24 November 2024; these are record metadata, not a comprehensive history.

The live [A328718](https://oeis.org/A328718) entry was read and independently
reopened. It defines the length/dimension array and identifies A328716 as its
diagonal. The entry is by Seiichi Manyama; its lattice-walk interpretation is
attributed to Alois P. Heinz. Its fixed-dimensional row asymptotic comment is a
different regime. Report179 does not claim to solve an open problem from that
comment or derive fixed-dimensional behavior by substituting into a
proportional-dimensional theorem.

## Classical primary sources actually inspected

1. Ira Gessel, Jonathan Weinstein, Herbert S. Wilf, *Lattice walks in Z^d and
   permutations with no long ascending subsequences*, Electronic Journal of
   Combinatorics 5 (1998), R2, 11 pages.
   [Primary journal PDF](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v5i1r2/pdf).
   The full paper was inspected. Equation (2), pp. 2-3, gives the Bessel-product
   walk exponential generating function. Adding the single zero-step
   exponential factor is an elementary extension. The paper's later
   permutation/Toeplitz results concern a different asymptotic framework; the
   report does not claim that its Bessel encoding is new.
2. Philippe Flajolet and Robert Sedgewick, *Analytic Combinatorics*, Cambridge
   University Press, 2009.
   [Author-hosted book PDF](https://algo.inria.fr/flajolet/Publications/book.pdf).
   The complete book was materialized for inspection. The full statement and
   proof of Theorem VIII.8, pp. 587-588, and the vanishing-multiplier remarks and
   Note VIII.37 on p. 589 were read. The theorem explicitly includes full
   descending-power expansions and compact coefficient-ratio uniformity.
   Period-two extraction, or the report's two-arc argument, handles even
   support. Generic full expansions, saddle perturbation, and the possibility
   of vanishing amplitudes are classical, and the report states this plainly.
   The book PDF is not redistributed.

## Bounded earlier-report comparison

Read-only ProveIt code searches were pinned to commit
83befe707f2840c2b53e0606701d8a2b28598e47. Queries included A328716, A328718,
0.804710405919520, the BesselI diagonal formula, and lazy closed walks. No
matching family-specific report was found in inspected results. A broader
328716 search returned incidental numeric strings. These bounded results do
not certify repository-wide absence.

Relevant nearby content was actually read rather than relying only on search
snippets. An A039831 report analyzes a moving maximum coefficient and two
Fourier peaks, a different combinatorial problem. A047909/A268485 and the
A108242 regular-cyclic-word family were rejected as already substantially
covered by existing reports. Report169's packed-matrix A261781/A261784 family
was also excluded. Search misses for known complete duplicates demonstrate why
a failed exact-ID or ranked earlier-report search cannot certify novelty.

The available earlier-report searches used exact identifier, full-content,
title, and semantic queries. These are bounded ranked/fuzzy retrievals, not an
exhaustive corpus proof. No private query receipts or unrelated source material
are included in this package.

Alternative-name searches for Bessel distributions, conditional occupancy,
lattice bridges, occupied directions, and Poisson limits found general related
literature but did not identify the complete family-specific theorem package.
This was a limited search, not a settled priority result. Individual probability
refinements could have other formulations or antecedents not located here.

## What is established

The article provides self-contained mathematical arguments for the exact model,
all-fixed-order expansion and coefficient formula, absolute complex marked
remainder, weighted probability refinements, occupation fluctuation and mean
offset formulas, parity inverse brackets and eventual width-one bound, and
compact proportional-ratio extension. Independent mathematical review and finite
exact code checks were used as quality gates. They do not establish historical
novelty, effective numerical inverse thresholds, or interval-certified error
constants. No external record was changed or submitted.
