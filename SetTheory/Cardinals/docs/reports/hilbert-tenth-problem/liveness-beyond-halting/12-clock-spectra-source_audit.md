# Source and contribution audit

Audit date: October 2, 2026.

## Repository anchor

Repository: https://github.com/VladimirReshetnikov/ProveIt

The research target is the question `lbh:q:spectra` in:

`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/liveness-beyond-halting/article.tex`

Inspected revision: `e58b724c25bd34533b7a5834cfcbe873dfa01288`.
Blob: `b291e1a88e30a97d149d72f3e8985023ca408ee5`.

This report already covers recurrence classifications, computable deadline
characterizations, c.e. clock cones, finite counter-machine quadratic laws,
finite two-stack quartics, and exact affine realizations. Those broad themes are
not claimed as discoveries of the present manuscript. Its stated question about
spectra beyond c.e. cones, particularly least degrees, is the specific extension.

The main HilbertTenthProblem README was also read through the GitHub connector:

`Computability/HilbertTenthProblem/README.md`

It was read on the default branch, not as a frozen file at the above report
revision. It distinguishes external-horizon constructions from its fixed universal
polynomial bounds. No numerical result from that evolving README is used as a
premise of a mathematical proof here.

A targeted code search for `self-modulus` returned only an unrelated Fabius
function source at the time of inspection. This was a narrow duplication check,
not a complete repository audit or evidence of literature-wide novelty.

## Primary mathematical sources inspected

1. Peter Gerdes, *Harrington's Solution to McLaughlin's Conjecture and Non-uniform
   Self-moduli*, arXiv:1012.3427. The inspected PDF is dated August 23, 2021.
   Section 4 discusses unique-path/uniform-modulus relationships, jump moduli,
   and the distinction from nonuniform self-moduli.
   https://arxiv.org/abs/1012.3427

2. Benoit Monin and Ludovic Patey, *Pi^0_1 Encodability and Omniscient Reductions*,
   arXiv:1603.01086. Corollary 2.2 is the modulus/hyperarithmetic equivalence
   used in the final sentence of the least-degree theorem. The PDF page was
   visually inspected as well as text-read.
   https://arxiv.org/abs/1603.01086

3. J. R. Shoenfield, *On degrees of unsolvability*, Annals of Mathematics
   69(3):644–653 (1959), DOI 10.2307/1970028. Bibliographic record inspected;
   credited for the classical limit-computability background. The proof here
   uses the displayed convergent approximation directly.

4. R. M. Friedberg, *Two recursively enumerable sets of incomparable degrees of
   unsolvability (solution of Post's problem, 1944)*, PNAS 43(2):236–238 (1957),
   DOI 10.1073/pnas.43.2.236. Bibliographic record inspected; the classical
   existence of incomparable c.e. degrees is an external input to the explicit
   two-cone nonprincipal example, not a new priority construction in this package.

The recent preprint *Listing the hyperarithmetical functions*, arXiv:2605.21194,
was also consulted during the literature check. No theorem of it is required by
the manuscript. This audit does not assert that all relevant literature was found.

## What is proved independently in the manuscript

- The tree explorer's clock/path-bound equivalence with runtime explicitly paid.
- The normal form by upward effectively closed Baire-space classes.
- The first-match recursive singleton, with degree exactly that of the limit.
- The deferred exact-halting-time tree for the explicitly defined jump hierarchy.
- Effective union of clock spectra.
- The self-modulus consequence of leastness (hyperarithmeticity then uses the
  external modulus theorem).
- The guarded-affine sign gadget and complete finite quadratic zero-set bijection.
- The step-for-step rational affine encoding on finite rational input codes.

The claims are constructive extensions/integrations in the context of the stated
repository question. Classical ingredients are not assigned new priority.

## Verification boundary

Finite exact Python tests and direct evaluation of the exported polynomial were
run successfully. Assistant-side review of the proof arguments included the
all-deadlines compactness condition, unknown-oracle-query deferral, and natural
rather than signed witness domain. No Lean/Rocq verification or independent
referee review was performed. The numerical universal interpreter is not supplied.
