# Source audit and priority boundary

## Repository pin

`0c740647c48baec7f0b4192723e977d69917dd52`

Connected GitHub reads established this snapshot. Repository search was used
for path discovery; the principal source claims were fetched at the pinned
revision rather than inferred from search-result fragments.

## Canonical material inspected

- `Analysis/Polylogarithms/docs/manuscript/README.md`.
- `Analysis/Polylogarithms/docs/manuscript/chapters/04-cyclotomic-quotients.tex`,
  including the formal restricted quotient, the S6 candidate, and its
  equivalent-basket identity.
- `Analysis/Polylogarithms/docs/reports/stieltjes-correlation-calculus/continuations/mellin-lerch-dilation/sections/06-audit-research.tex`,
  including its explicit same-direction product-integral and harmonic
  derivative/primitive compatibility questions.
- The incoming directory inventory and the relevant beginning of its README.

The canonical source reports S4 proved and the current S6 and revised S8
candidates still conjectural. This delivery does not alter those statuses.
An identity between two candidate residual presentations is not a proof that
either residual vanishes.

## Accessible incoming source copies

Relevant text was inspected from Library copies of these listed archives:

- `ProveIt_Bilinear_Mellin_Hurwitz_2026-10-10.zip`: especially the main scope
  and sections 07 (reciprocity), 08 (Stieltjes), and 09 (audit/research).
- `ProveIt_Unequal_Twist_Jets_2026-10-10.zip`: its scope, principal statement
  overview, integer-order/nonclosure distinctions, and research headings.
- `ProveIt_Nonlinear_Stieltjes_Transport_2026-10-10.zip`: its abstract and scope
  establishing the distinction between finite-part transport and ordinary
  convergent convolution.

These are targeted readings, not exhaustive audits of all their proofs and
code. The Library copies had the listed archive names and reported sizes;
no additional byte-for-byte comparison with the pinned Git blobs is claimed.
The original archives are not redistributed in this delivery.

## Listed but not inspected

The binary contents of the following incoming archives were not inspected:

- `ProveIt_Cubic_Harmonic_Mixed_Orders_2026-10-11.zip`
- `ProveIt_Exact_Resonant_Identities_2026-10-11.zip`
- `ProveIt_Independent_Orders_2026-10-11.zip`

Their filenames do not establish their mathematical contents. This limitation
prevents a claim that every result here is absent from all current incoming
material. Reconcile statement-level overlap before assigning priority labels.

## External primary / authoritative references

- NIST DLMF §§5.5, 5.12, 25.2, 25.11, 25.12, and 25.14, consulted online.
  The one-factor Mellin–Barnes representation already appears as 25.14.8.
- J. P. Selvaggi and J. A. Selvaggi, *The Application of Real Convolution for
  Analytically Evaluating Fermi–Dirac-Type and Bose–Einstein-Type Integrals*,
  Journal of Complex Analysis 2018, Article ID 5941485,
  DOI 10.1155/2018/5941485. Its convolution/Laplace methodology is an antecedent.

This is a targeted literature check, not an exhaustive priority search.
The paper credits classical mechanisms and proves its own exact
specializations instead of presenting standard transform identities as new.

## Audit outcome

No newly identified false equation in the sampled source is asserted.
The safeguards in the article address invalid possible simplifications:
separated resonance values, an intermediate first-moment factor error in this
work, separate branch assignments, integer-only differentiation, and expansion
of individually divergent remainder pieces.

The all-order reciprocal geometry is different from the same-direction
rational Mellin kernel. The new report must not be cited as solving the latter
in its full arbitrary-order, two-scale generality.
