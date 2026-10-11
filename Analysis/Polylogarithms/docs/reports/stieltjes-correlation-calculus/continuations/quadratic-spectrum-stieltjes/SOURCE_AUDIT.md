# Source audit

Repository: VladimirReshetnikov/ProveIt.
Pinned commit: `446dca9bd65c20e409d1d2561d4ffad408103e2a`.
Commit timestamp: 2026-10-11T05:06:38Z (10 October in America/Los_Angeles).

## Inspected scope

The manuscript main file and preface; the research-status chapter;
selected early and central sections of the integration chapter; the stated
S6 target and formal presentation of the full-Cayley obstruction; the
arithmetic spectral-jets section on periodic weights and arithmetic poles;
the complete theorem/argument section of the rational Herglotz classification;
the intake README and incoming directory catalogue. This is not an audit of
all dependencies of every theorem encountered.

Public classical sources were NIST DLMF sections 5.5, 5.15, 10.32, 10.39,
20.7, 25.11, and 25.12. Dowker's arXiv:1412.0549 landing page and abstract
were checked for subject, attribution, and corrected-version metadata.
The defect formula in the article is proved independently, not imported
from an unread full-text theorem.

## Uninspected incoming archives

Only names and metadata were read for:

- ProveIt_Bernoulli_Tornheim_Digamma_2026-10-11.zip
- ProveIt_Cubic_Tail_Descent_2026-10-10.zip
- ProveIt_Determinantal_Harmonic_Resonance_2026-10-10.zip
- ProveIt_Differential_Polygamma_and_Lerch_Jets_2026-10-11.zip
- ProveIt_Multishift_Reflection_2026-10-10.zip
- ProveIt_Polygamma_Tail_Identities_2026-10-11.zip

Their contents were not inspected. No conclusion about their results or
errors follows from the filenames. Library retrieval returned other related
prior reports, not these requested archive interiors; those search snippets
were not used as substitutes for the missing contents.

## Proposed correction

The research chapter still advertises the general J(p/q) symbol classification
as an open direction. At the same pin, the report
`Analysis/Polylogarithms/docs/reports/herglotz-rational-classification/sections/04-classification.tex`
already states and argues a complete formal classification. Synchronize the
status after normal integration review, and keep constructive evaluations and
numerical period questions distinct. Not all prerequisite symbol-theory lemmas
were independently re-audited in this session.

No new counterexample to an analytic formula in the inspected material was
established. The pole, parity, holomorphy, and convergence warnings in the new
article describe safeguards in its own derivation, not defects attributed to
unread material.

## Contribution boundary

The package gives new derivations and explicit continuation identities for
integration. It makes no exhaustive literature-priority claim. It does not
prove S6, any revised S8 conjecture, transcendence or period independence,
nor proof-assistant correctness. Classical inputs and the already existing
first-anomaly framework retain attribution.
