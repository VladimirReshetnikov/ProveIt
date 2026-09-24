# Primary sources and status check

Checked September 19, 2026.

## Initial conjecture

Yan-Ting Xie and Shou-Jun Xu, *Ultra log-concavity and real-rootedness of
dependence polynomials*, arXiv:2408.09152v1 (August 17, 2024).

- Record: https://arxiv.org/abs/2408.09152
- Paper: https://arxiv.org/pdf/2408.09152
- Printed page 3: ordinary, ordered, and ultra log-concavity definitions.
- Printed page 14: additive augmentation axiom and l-matroid terminology.
- Printed page 15: parameter-two Conjecture 4.4 and the rank-three Example 4.5.
- Printed page 16: rank-dependent Conjecture 4.8, with the sequence indexed
  through the ground-set size n.

The conjecture page and augmentation page were visually checked in the PDF.
The displayed augmentation condition (*) says x in T, without explicitly
removing S. The report uses x in T\S throughout. Its counterexamples satisfy
this stronger convention, so the literal weaker reading does not remove them.

The arXiv record still lists only v1. That fact alone does not establish that a
conjecture is still open.

## Prior disproof located during the investigation

Alex Chengyu Li, *Additive Augmentation Gaps Do Not Force Log-Concavity* (2026).

- Author overview:
  https://crabresearch.com/research/augmentation-gap-log-concavity?lang=en
- DOI: https://doi.org/10.2139/ssrn.7434141
- SSRN: https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7434141
- Archive link exposed by the overview: https://doi.org/10.5281/zenodo.22505877

The overview reports first public release September 6, 2026 and revision
September 18, 2026. It advertises a rank-four, thirteen-element example with
sequence 1,13,25,7,2 and constant-augmentation-parameter asymptotic families.
The SSRN indexed record reports a six-page working paper posted September 14.

The overview and bibliographic/search records were retrieved. Attempts to fetch
the full SSRN PDF returned an access error, and the linked Zenodo pages could
not be retrieved in the session. The report therefore credits the advertised
prior disproof but makes no unsupported claim that the full manuscript lacks
any particular refinement developed here. Its advertised formalization was not
inspected or independently run.

The rankwise minimum-size problem became the target after this status correction.
No first-disproof claim is made; no exhaustive historical-priority claim is made
for the refinements either.

## Shadow theorem

Boris Bukh, *Multidimensional Kruskal–Katona theorem*, arXiv:1009.2375v2 (2011).

- Record: https://arxiv.org/abs/1009.2375
- Paper: https://arxiv.org/pdf/1009.2375

The introduction states the classical colex shadow theorem and its Lovász
version. The original Kruskal and Katona bibliographic details in the report
were verified against Bukh's reference list. The argument here uses the exact
canonical-binomial shadow bound, not the weaker continuous Lovász bound.
For the small sizes needed, the supplied code also verifies the relevant shadow
bounds independently by enumerating uniform families.
