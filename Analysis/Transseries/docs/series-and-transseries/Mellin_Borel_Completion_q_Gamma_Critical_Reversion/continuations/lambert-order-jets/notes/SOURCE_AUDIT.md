# Source audit and novelty boundary

Date: 12 October 2026.

## Detailed pinned source

Repository: `VladimirReshetnikov/ProveIt`.
Commit: `7bd1ce58abe522b83cd3368bbafa1be97837b75d`.

Reviewed source:
`Analysis/Transseries/docs/series-and-transseries/Mellin_Borel_Completion_q_Gamma_Critical_Reversion/critical_stokes_q_reversion.tex`.

The GitHub connector returned the source at the pinned commit. Inspected
ranges included 1–220, 300–650, 610–860, and 915–1025. Some tool responses
were truncated; the review is limited to the visible passages, especially
the scope, q-product Borel kernel, Mellin completion proof, and rational
weight criterion. This is not a claim to have reviewed every line in those
nominal ranges or all results of that source.

The source's simple-pole kernel and separation of the linear median from the
physical exponential correction are consistent with the order-one background
used here. Its rational-weight criterion already uses Fourier and Möbius
inversion. The present report does not present these mechanisms as newly
invented, does not re-claim its asserted resolutions of Fantini–Rella
conjectures, and does not rely on those resolutions as assumptions.

The new report's distinct focus is the all-m fixed-parity order derivative,
its exact double-pole completion, the factor-pi*i activation identity, real
atomic rigidity without rational shifts, sharp action detection, and the
complete general-measure one-jet kernel. Their first occurrence anywhere in
the literature has not been established.

## Repository indexes

Read on live `main` on 12 October 2026:

- `Analysis/Polylogarithms/README.md`, initial 170-line range: project status,
  scope, canonical manuscript description, and claim-status discipline.
- `Analysis/Transseries/README.md`: project organization and scoped Lean
  infrastructure; none of that infrastructure formalizes the present proofs.
- `docs/incoming/README.md`, initial 180-line range: intake/evidence protocol
  and placement conventions.
- Listings for the three user-specified directories; searches for related
  q-product, Mellin, Borel, and order-derivative material.

Search hits and tree inventories are discovery evidence, not proof review.
The full combined Polylogarithms manuscript and the entire Transseries
collection were not read or audited.

## Incoming archives: inventory only

The listing contained these five ZIP archives:

- `ProveIt_Resonant_Polylog_Transseries.zip`
- `ProveIt_Resonant_Polylogarithm_Inversion_2026-10-11.zip`
- `Resonant_Polylogarithm_Transseries.zip`
- `polylogarithm_resonance_and_inverse_transseries.zip`
- `polylogarithm_transseries_research.zip`

Their filenames and metadata were available, but their binary contents were
not obtained and unpacked in the working runtime. No assertion about their
complete theorems, errors, or uniqueness is made. This limitation is why the
article does not claim an exhaustive de-duplication against the incoming
queue. No archive was modified or deleted.

## Primary literature inspected

D. Dorigoni and A. Kleinschmidt, *Resurgent expansion of Lambert series and
iterated Eisenstein integrals*, arXiv:2001.11035 (2020). The scalar Lambert
analysis, including the odd-integer disappearance of the asymptotic tail
while exponential terms survive, was inspected in the PDF. This earlier
phenomenon is explicitly credited, not claimed as new.

V. Fantini and C. Rella, *Modular resurgence, q-Pochhammer symbols, and quantum
operators from mirror curves*, arXiv:2506.08265v2, 1 April 2026. The scope and
q-product summation material were inspected, and printed page 17 was visually
checked for Conjecture 5 and equation numbers. The absence of a search hit
for the word “derivative” is not used as proof of novelty.

NIST DLMF, Sections 24.8, 25.4, 25.11, and 25.12, supplies the classical
Bernoulli, zeta, Hurwitz-zeta, and polylogarithm identities cited in the paper.
The analytic proof uses the displayed functional equations, not a secondary
summary of them.

## Correction outcome

One version-specific cross-reference mismatch was confirmed; see
`CROSS_REFERENCE_CORRECTION.md`. No newly established mathematical defect
in the inspected q-Gamma completion proof is claimed. The ordinary-PV error
for double poles, the fixed-parity differentiation requirement, and the
Lebesgue blind component are safeguards proved for the new extension, not
accusations against unread repository material.
