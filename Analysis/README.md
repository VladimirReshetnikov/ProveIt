# Analysis

Analysis developments: formal Lean and Coq projects, and research corpora that
are not (yet) formalized.  The exact identity projects have paired Lean
and Coq proofs; the Fabius project is currently a Lean statement formalization.

- [`TrigonometricIdentities/`](TrigonometricIdentities/) contains the
  eleven-term arctangent-square identity and the golden-ratio sine identity.
- [`ExponentialIdentities/`](ExponentialIdentities/) contains the exact floor
  certificate for the five-level tiny-exponent tower.
- [`Transseries/`](Transseries/) develops asymptotic scales, power-logarithmic
  monomials, well-based supports, and differential blocks independently of the
  Fabius function. Its two inversion volumes and verification material live
  alongside the Lean library.
- [`FabiusFunction/`](FabiusFunction/) defines the bounded Fabius function,
  its signed global extension, exact rational dyadic arithmetic, and the
  statements of every result in arXiv:1702.06487v3.  Proofs are the next
  formalization phase.
- [`Polylogarithms/`](Polylogarithms/) collects Vladimir Reshetnikov's PolyLog
  research programme in a collective 298-page [unified manuscript](Polylogarithms/docs/manuscript/polylogarithms.pdf), with source drafts moved from the private Smithereens repository: eight
  articles and thirty-one reports, supplemented by eleven continuation packages,
  on multiple polylogarithms at roots of unity,
  the polylogarithm–polygamma bridge, the Γ-value lattice, polygamma at CM
  points, generalized Stieltjes constants and their antiderivatives and
  parameter derivatives, polylogarithm ladders, Clausen values and the
  Herglotz function. Results are classical, derived or numerically verified,
  as each document states; nothing is formalized. External continuations are
  merged by thematic spine under `docs/reports/`, each with an `OVERVIEW.md`
  reconciliation note: five reports from batch 138 of
  [`docs/incoming`](../docs/incoming/README.md) (`06039f479`) and
  `gaussian-parity-reductions` from batch 139 (`d4dead2c6`). The five batch-141 packages are integrated in the canonical manuscript,
  including the exact S4 proof, conductor descent and trace jets, complementary
  depth and rigidity, and sharp moment/Herglotz asymptotics. Its author is
  ProveIt Contributors. The project README's "Status of claims" records
  the source-specific corrections and remaining conjectures.
- [`ErdosSimilarity/`](ErdosSimilarity/), opened on 7 October 2026, holds one
  research report,
  [`Research/uniform-geometric-avoidance`](ErdosSimilarity/Research/uniform-geometric-avoidance/README.md),
  from four manuscripts. The first gives a closed set of measure at least
  `1 − ε/2` in every unit interval that omits infinitely many terms of every
  progression `x + s qⁿ` (`s ≠ 0`, `0 < q < 1`) at once, which answers
  Question 1 of Burgin–Goldberg–Keleti–MacMahon–Wang negatively. The other
  three (batch 138, `cd984a34c`) prove independently one common avoiding set
  for every convergent, non-eventually-constant real C-finite sequence,
  which answers the report's Question 5; the fourth adds a supergeometric
  theorem. A README of reconciliation notes (`3d0303836`) relates the four;
  no further write is planned. The report adapts an external
  openai/math construction under a nested Apache-2.0 licence, keeps its
  delivered layout, and is not formalized.

The Coq developments are mathematical ports rather than generated
translations. The tiny-exponent proof uses `coq-interval`; the trigonometric
proof derives the exact constants needed by the identity.
