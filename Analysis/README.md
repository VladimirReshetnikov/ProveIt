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
  research programme in a 204-page [unified manuscript](Polylogarithms/docs/manuscript/polylogarithms.pdf), with source drafts moved from the private Smithereens repository: eight
  articles and thirty-one reports, supplemented by six continuation packages,
  on multiple polylogarithms at roots of unity,
  the polylogarithm–polygamma bridge, the Γ-value lattice, polygamma at CM
  points, generalized Stieltjes constants and their antiderivatives and
  parameter derivatives, polylogarithm ladders, Clausen values and the
  Herglotz function. Results are classical, derived or numerically verified,
  as each document states; nothing is formalized.
- [`ErdosSimilarity/`](ErdosSimilarity/), opened on 7 October 2026, holds one
  research report, `Research/uniform-geometric-avoidance`: a closed set of
  measure at least `1 − ε/2` in every unit interval that omits infinitely
  many terms of every progression `x + s qⁿ` (`s ≠ 0`, `0 < q < 1`) at once,
  which answers Question 1 of
  Burgin–Goldberg–Keleti–MacMahon–Wang negatively. It adapts an external
  openai/math construction under a nested Apache-2.0 licence, is placed with
  its delivered layout (its write is pending) and is not formalized.

The Coq developments are mathematical ports rather than generated
translations. The tiny-exponent proof uses `coq-interval`; the trigonometric
proof derives the exact constants needed by the identity.
