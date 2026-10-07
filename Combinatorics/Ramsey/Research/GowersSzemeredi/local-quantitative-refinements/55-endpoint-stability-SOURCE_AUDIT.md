# Source and novelty audit

Prepared in October 2026 during the requested Ramsey research task.
This is a provenance note, not a comprehensive literature review or a priority
certificate.

## Repository inspected

Repository: `VladimirReshetnikov/ProveIt`.
Requested area: `Combinatorics/Ramsey`.

Pinned comparison reference:
`128f514afce0bf7eb48133fb30dd3f8e034ea3a2`.
The default branch moved during the investigation. Earlier search results also
referred to `6a6d7961c3c261da7dc18def13fff30b12dd5c04`; these are not silently
identified with one snapshot.

Read or searched through the GitHub connector:

1. The Ramsey root and Research tree, to locate the manuscript and formal projects.
2. `Research/GowersSzemeredi/local-quantitative-refinements/README.md`, including
   the thematic summary and source guide. Its first 195 lines were also fetched
   explicitly at the pinned reference.
3. Search results for `lemma_16_10` and the associated proof-status warnings.
   No claim to solve that entry is made.
4. Searches for `Eisner`, `near-maximal`, `extremisers`, and `near-extremisers`.
   Some searches returned no matches. That is not a proof of absence.
5. `Research/GowersSzemeredi/local-quantitative-refinements/45-rigidity-gaps-review_energy.md`
   at the pinned reference. This concerns ordered additive set energy, not the
   phase-distance modulus developed in this package. Its own review-status
   qualifications were respected; it was not treated as an external referee report.

The pinned README explicitly identifies prior exact fourth-order centered cube
expansions (sources 03, 08, 09), fifth-order/torsion expansions (09 and later routes),
and other moment-stability and energy-rigidity results. Consequently the four-vertex
census and the general strategy of a centered cube expansion are **reused background**,
reproved here for a self-contained article, not claimed as wholly new discoveries.

The proposed additions relative to the material inspected are the sharp uniform
phase-distance expansion through second order, the bounded-complex cancellation
that controls the fifth term at cubic scale, the continuous two-torsion spectral
profile, and the tangent classification for second-order saturation. It remains
possible that a formulation appears elsewhere in the repository or literature.

## Primary scholarly sources

### Gowers

W. T. Gowers, *A new proof of Szemerédi's theorem*, GAFA 11 (2001), 465–588.
DOI: https://doi.org/10.1007/s00039-001-0332-9
Full paper: https://www.cs.umd.edu/users/gasarch/TOPICS/vdw/sz-thm-gowers-proof.pdf

The full parsed paper and selected page images were inspected. The paper provides
the uniformity, cubical-difference, and extraction/integration framework. The
article does not assert that its endpoint theorem replaces the full inverse steps
or improves a global Szemerédi bound. Bibliographic metadata was corroborated by
Cambridge's publication listing and primary-paper references.

### Eisner–Tao — the essential imported theorem

T. Eisner and T. Tao, *Large values of the Gowers–Host–Kra seminorms*,
Journal d'Analyse Mathématique 117 (2012), 133–186.
DOI: https://doi.org/10.1007/s11854-012-0018-2
Version consulted: https://arxiv.org/html/1012.3509v2
Record: https://arxiv.org/abs/1012.3509

Theorem 1.1 provides uniform qualitative entry into a neighborhood of a polynomial
phase for L-infinity-bounded functions on compact abelian groups. Only its
finite-group consequence is imported. Remark 1.6 states that polynomial rates can
be made effective but does not optimize or display them. The manuscript does not
claim to provide a new proof of this entry result, nor does it extract its numerical
threshold. The explicit local theorem has separate hypotheses and proof.

### Kovač–Rogers — contemporary comparison, not a proof input

V. Kovač and K. M. Rogers, *Estimates for L^p variants of Gowers norms*.
Version consulted: https://arxiv.org/html/2609.08916v1
Record: https://arxiv.org/abs/2609.08916

The preprint studies generalized L^p functionals and near-extremizers. It is cited
for the contemporary context. No result from it is used in the proof of the sharp
finite-group phase-distance expansion, and the present task did not establish a
comprehensive theorem-by-theorem nonoverlap comparison.

### Bao–Briët–Castro-Silva–van Dordrecht–Helsen — extension direction

Z. Bao, J. Briët, D. Castro-Silva, P. van Dordrecht, and J. Helsen,
*On Clifford hierarchy testing and near-extremizers of noncommutative uniformity norms*.
Version consulted: https://arxiv.org/html/2605.26983v1
Record: https://arxiv.org/abs/2605.26983

The introduction and main near-extremizer theorem were inspected. This supplies a
concrete noncommutative comparison problem for the further-research section. The
scalar Fourier calculation in this package is not claimed to prove an analogue
for Pauli uniformity norms or Clifford hierarchy testing.

## Search limitations

Targeted public-web searches included combinations of “Gowers”, “near-extremisers”,
“sharp stability”, “second order”, and “distance polynomial phases”. Several broad
queries returned poor or unrelated matches; those were not used as mathematical
sources. The inspected primary sources do not establish publication priority for
this package. No assertion that a famous historical open problem has been solved
is made.

## Computational and formal status

All claimed executed computational checks are recorded in the JSON output and can
be reproduced from the included script. Integer/rational checks and floating tests
are distinguished there. They do not prove the universal theorems.

No external referee, human peer review, independent agent review, or Lean
verification took place as part of this package. The proof checklist records the
mathematical arguments, not a certification by another party.
