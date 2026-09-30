# Proof audit and verification boundary

Date: 30 September 2026.

This document records an internal mathematical and implementation review. It
is NOT a report of independent peer review or kernel verification.

## Established within the manuscript

1. **Exact quadratic local compiler.** A sum of affine squares plus
   nonnegative zero-test products vanishes on natural coordinates exactly
   for one enabled labelled edge. Natural selectors summing to one are
   one-hot. Natural target counters enforce decrement positivity. Target
   tags distinguish parallel edges. Source tags are intentionally ignored.

2. **Coefficient and size bounds.** All expanded monomial types are covered.
   Selector cross coefficients are twice
   `1 + same_source + same_target + dot(delta_a, delta_b)`.
   Unit updates give height <= 8. Parallel identical increments attain 8.
   This is sharpness for the given compiler, not an absolute height optimum.
   The linear-size bound is for a factored circuit, not the expanded list.

3. **Affine lower obstruction.** For a nonempty graph in dimension at least
   two, finite fibers force all target coefficients to have the same nonzero
   sign. A uniform bound on fiber size then prevents any unbounded source
   contribution to the target total. All targets lie in a fixed finite box.
   Dimension one is functional and recurrence is arithmetic. The proof
   requires a global uniform branching bound and no side conditions on the
   natural state space.

4. **Recurrence completeness.** The recursive-tree normal form is explained
   through Skolem functions and finite oracle computation transcripts.
   Unary guesses turn natural branching into binary branching. Infinitely
   many events force infinitely many completed guesses. A run that guesses
   forever inside one stage emits no further events.

5. **Deadline compactness.** The finite tree checks every deadline that has
   elapsed, not only the kth visit total. Its arbitrarily long prefixes have
   one infinite compatible branch by König's lemma. Decidability of each
   finite search uses a complete finite successor list, not merely a
   decidable relation with bounded fibers.

6. **Sigma^0_3 classifications.** A single program index for a proposed
   computable deadline, or a proposed computable state sequence, is chosen
   before all finite checks. This guarantees compatibility. The lower-bound
   program guesses one finite natural a, then searches successively for
   witnesses to R(n,a,b,c). Every successful run of this reduction is
   computable once its finite a is fixed.

7. **Strict separations.** The binary diagonal tree is decidable because
   only bounded simulations are performed at a finite stage. It has a branch
   but no computable branch. All its finite-depth choice computations finish,
   so their finite maximum yields a computable deadline. The halting-time
   tree likewise uses bounded tests. Every branch bounds all diagonal
   halting times, so none has a computable majorant. Unary guessing makes
   every chosen value no larger than the corresponding event time.

8. **Faithful simulation.** Positive finite blocks, recognizable boundaries,
   event reflection, and no infinite unfinished blocks are explicit
   requirements. Effective finite branching permits a computable maximum
   simulation time over all histories of any fixed horizon. This is the
   crucial step for preservation of computable deadline existence.

9. **Weak fairness.** Only the designated action mu is required to be fair.
   It is enabled at all live configurations. Taking it in the wrong control
   or while locked enters a state with no continuation. A successful mu
   step locks, so an original transition must occur before another successful
   mu step. Branching rises from two to three; binary preservation is NOT
   claimed for this construction.

10. **Finite-certificate obstruction.** A computably checkable complete
    finite positive certificate family would enumerate the accepted inputs.
    Hierarchy strictness excludes this for Rec, CB, and CP. This is a
    uniform-completeness obstruction, not a claim that individual programs
    cannot have finite recurrence proofs.

## Classical background relied upon

- Effective coding of finite strings, machines, and computation transcripts.
- Halting undecidability and the arithmetic/analytic hierarchy strictness.
- Classical finite-counter universality; an operational two-stack compiler
  sufficient for this manuscript is explained in the article.
- König's lemma, used as an existence theorem, not a computable-selection
  principle.
- MRDP for the ordinary Diophantine representation of finite hit and other
  computably enumerable finite predicates.

General high undecidability of recurrence and fairness is classical, notably
in Harel's work. The exact normal form and refinements in this manuscript
have not undergone an exhaustive literature-priority search.

## Actually executed

`python code/verify.py` on Python 3.13.5:

- 302,498 exact local-equivalence checks;
- 27,652 sparse-versus-factored checks;
- 5,152 legal transitions specifically exercised;
- 169 coefficient tables;
- 41 finite-visit example runs;
- 576 affine-fiber growth examples.

All passed. The tests include exhaustive small coordinate ranges, deterministic
random sampling (seed 20260930), malformed controls/selectors, target
mutations, zero/decrement guards, and parallel labelled edges.

The PDF was compiled with pdfLaTeX/latexmk and rendered with Poppler for visual
inspection. Compilation warnings and page checks are recorded separately in
`verification/pdf_check.json` after the final build.

## Not executed or not claimed

- No Lean/Rocq proof of any new theorem was compiled.
- The ProveIt repository was inspected but not rebuilt or axiom-audited.
- The universal interpreter is not instantiated as a complete numerical edge
  table; no numerical universal dimension is given.
- Finite tests do not verify any infinite-path or noncomputability theorem.
- No named published open problem, finite-fold MRDP conjecture, single-fold
  MRDP conjecture, minimal-register problem, or absolute height optimum is
  claimed solved.
- These are relational dynamics on natural coordinates, not deterministic
  polynomial maps on real space. The continuous relaxation is not equivalent.
