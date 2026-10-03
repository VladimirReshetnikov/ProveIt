# Source and scope audit

## Pinned repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Commit inspected: `e8bb0931d67f80d9fce87a8cddb0f661ff19f956`.
Inspection date: September 30, 2026.

This was a focused inspection of the Computability branches, not an exhaustive
review of every file in the repository. No repository contents were modified.
The compiled article and new executable artifacts are local deliverables.

## Inspected paths and what they establish

1. `Computability/HilbertTenthProblem/README.md`
   Describes the corrected Jones papers, MRDP in both directions, universal
   equations, register-machine encodings, and certificate optimization work.
   It distinguishes the optimized straight-line result from formalized results.

2. `Computability/HilbertTenthProblem/Lean/STATUS.md`
   The inspected status entries describe the MRDP, bounded-quantifier,
   exact-iteration, primitive-recursive, and finite-polynomial interfaces.
   This is repository-reported status; the full build was not independently rerun.

3. `Computability/HilbertTenthProblem/Lean/Diophantine/Common/DiophantineTrace.lean`
   The source was read. It contains `boundedForall_dioph`, `exactIter_dioph`, and
   `existsExactIter_dioph`, with the PAListCoding cipher closure contracts supplied.
   These statements concern Diophantine existential representability; they do not
   themselves claim a bijection between executions and arithmetic witnesses.

4. `Computability/CombinatoryLogic/README.md`
   Describes scoped lambda syntax, SK/SKI/Iota compiler simulations, the pure-Iota
   versus runtime distinction, and exact recursive-function equivalences for a
   separately specified weak-call-by-value model. The README expressly says that
   the forward simulations are not claimed fully abstract or reduction-reflecting,
   and that some bridges between the different lambda models remain obligations.

5. `Computability/CombinatoryLogic/Coq/SKPolynomial.v`
   The source was read. Its "polynomials" are applicative SK syntax with variables,
   not Diophantine integer polynomials. It defines contextual K/S reduction and
   proves bracket-abstraction properties. The present natural-code compiler is
   not inferred merely from that filename.

Pinned files can be accessed by placing their path after:
https://github.com/VladimirReshetnikov/ProveIt/blob/e8bb0931d67f80d9fce87a8cddb0f661ff19f956/

## Primary literature consulted

- Larchey-Wendling and Forster, *Hilbert's Tenth Problem in Coq* (FSCD 2019),
  https://doi.org/10.4230/LIPIcs.FSCD.2019.27 .
  Already includes FRACTRAN in a complete mechanized MRDP development.
- Jones and Matiyasevich, *Register Machine Proof of the Theorem on Exponential
  Diophantine Representation of Enumerable Sets* (1984),
  https://doi.org/10.2307/2274135 .
- Lohrey, Stober, and Weiss, *The Power Word Problem in Graph Products* (2024),
  https://doi.org/10.1007/s00224-024-10173-z .
  Uses the established forbidden-factor characterization of trace normal forms.
- de Colnet, Meel, and Mathur, *Counting and Sampling Traces in Regular Languages*
  (POPL 2026), https://doi.org/10.1145/3776723 and
  https://arxiv.org/abs/2512.00314 .
  The input is an explicitly represented regular language, not necessarily
  trace-closed; this differs from the succinct trace-closed net setting here.
- Cantone, Cuzziol, and Omodeo, *On diophantine singlefold specifications* (2024),
  https://lematematiche.dmi.unict.it/index.php/lematematiche/article/view/2703 .
  Provides context for the unresolved univocity/exponentiation issue.

The article bibliography contains the full conventional references used in the
text. No quotation of a long source passage is included.

## Contribution classification

Established or elementary background:
MRDP existential representability, sum-of-squares combination, circuit
quadratization, the forbidden-factor normal-form criterion, pairing, and the
universal-halting reduction of the general finite/single-fold question.

Constructions developed and fully proved in this package:
the displayed trace-quotient Petri compiler and its exact counts/height;
the explicit deterministic-memory lower-bound family and Petri realization;
the canonical linear-scan FRACTRAN certificate and first-halting extension;
the context-local fixed-schedule SKI compiler and size/height estimates;
and their witness-faithful composition and counting consequences.

Priority limitations:
these formulations have not been certified as globally first in the literature.
The research contribution should be evaluated at the level of the concrete
witness bijections and resource bounds, not as a claim that the classical
representability of these substrates is new.

Not accomplished:
fixed-arity single-fold or finite-fold representations for universal unbounded
computation; new universal-variable records; an efficient general solver;
full abstraction of the repository compiler chains; a new proof-assistant
formalization or a rerun of the repository build.

## Artifact checks

The new Python suite was run successfully with exact integer arithmetic.
An independent standalone verifier was run on every exported JSON example.
The article was compiled with pdfLaTeX, inspected for warnings and overflow, and
rendered with Poppler for visual review. These checks are separate from, and do
not replace, the mathematical proofs in the article.
