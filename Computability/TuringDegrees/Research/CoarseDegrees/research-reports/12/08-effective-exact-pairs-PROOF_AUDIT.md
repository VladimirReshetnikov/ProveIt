# Proof audit

This file records a self-audit of the delivered mathematical argument. It is
not an independent referee report or a proof-assistant certificate.

## Dependency map

1. **Core is a countable ideal (Lemma 2.2).**
   Uses only countability of oracle programs, downward closure, and finite joins.
2. **Spectrum identity (Lemma 2.3).**
   Uses sparse coding on a computable density-zero set and the equality of coarse
   description classes under density-zero changes.
3. **Computable normal form (Theorem 3.2).**
   Uses exact dyadic column counts, bounded-linear restriction to a column,
   majority recovery on geometric blocks, and a finite-initial-columns plus
   small-tail estimate. No imported deep theorem.
4. **Finite-extension lemma (Section 4).**
   Uses finite oracle-use semantics. Fixed complete rows are computable in a
   finite generator join; arbitrary finite answers in an unfixed row can always
   be realized by a finite variant of that row.
5. **Effective perfect family (Theorem 1.2, proved in Section 5).**
   Uses the finite-extension lemma and an explicit finite level construction.
   All decisions are made by H = join_m (B_m'). No generic totality oracle or
   abstract effective perfect-set theorem is assumed.
6. **Core realization (Theorem 1.1, proved in Section 6).**
   Lower inclusion: row-majority normal form and nonuniform finite corrections.
   Upper inclusion: the constructed pair has exactly the prescribed common
   lower cone. This route is self-contained in the manuscript.
7. **Alternative realization proof (Section 6.1).**
   Imports HJKS Theorem 3.7, cone-avoiding compactness. This is a second proof and
   is not an assumption in the finite-extension route.
8. **Spectrum factorization (Theorem 7.1).**
   Uses the normal form and the classical limit lemma, proved in Appendix A.
9. **Order embedding (Theorem 7.3).**
   The sufficient direction is a displayed total functional on descriptions.
   The necessary direction uses relative Friedberg inversion, proved in
   Appendix B, and the spectrum factorization.
10. **Prescribed-jump exact pairs (Theorem 7.5).**
    Uses the effective-family theorem, H_W =_T H_A join C, H_A <=_T B',
    and the necessary jump lower bound in the factorization theorem.
11. **Continuum many no-least classes (Corollary 7.6).**
    Uses the embedding above B'', principal/nonprincipal core dichotomy,
    strictness of the jump, and countability of each Turing degree class.

## Quantifier checks

### A generator is recovered nonuniformly

For every description D and every n there is a Turing reduction of A_n to D.
The reduction can hard-code that row's finite error set. This does not provide
one effective sequence of reduction indices and does not imply that D computes
the entire uniform join B. Proposition 8.1 proves that one fixed functional
extracting a fixed noncomputable set from *all* descriptions is impossible.

### Every row has finitely many errors, but their union can be infinite

For each fixed number m of columns, the number K_m of errors there is finite.
All remaining errors are in a tail of density 2^(-m). Taking a limit in N first
and then in m proves density zero. There is no interchange of these quantifiers.

### The construction uses jumps of finite joins

H_A is join_m (join_{n<m} A_n)', not join_n A_n'. A uniform bound by B' follows
from uniform projection and jump monotonicity, not from distributing a jump
over a join. In the interleaved construction finite constant rows have to be
accounted for uniformly; they add the oracle C, not C'.

### Negative decisions do not assert partiality

When there is no cross-disagreement, the common total output, if it exists, is
computed by searching one side's finite traces. No algorithm decides whether a
functional is total. For an individual jump bit, only existence of a halting
trace on one designated input is decided.

### The perfect-family bound includes its parameter

D_P' <=_T H_A join P. Only computable P give D_P' <=_T H_A. The finite branching
construction is H_A-computable, but this does not make all of its paths
H_A-computable. The common error envelope is H_A-computable because a row is
fixed at one finite level and only finitely many masks occur at that level.

### The mask obstruction includes equality with the core

The hypothesis is Low(D) intersect Low(E) = Core(X). A common computable null
mask then gives a coarse description W computed by both, so its degree
principally generates the core. Without the equality with Core(X), the
conclusion about the entire pair intersection would be invalid.

### The upper-cone hypothesis in order reflection is real

For E >=_T B', jump inversion produces D >=_T B with D' =_T E. Computing B is
what ensures that D solves the base row problem. The proof does not discard
this hypothesis or infer a general nc/uc equivalence from equal spectra.

## Literature and novelty

- The core notion and cone-avoiding compactness are from HJKS.
- The row-finite no-splitting mechanism is classical exact-pair machinery;
  Franklin and Solomon give a primary-source exposition in a different setting.
- The dyadic jump-cone special case was already developed in ProveIt and is
  connected to Jockusch--Schupp's work.
- The repository already contains perfect exact-pair existence for arbitrary X.
- The countable-core classification answers a question explicitly unclassified
  in the inspected synthesis. Its short derivation from known compactness is
  included precisely to avoid overstating originality.
- Priority for the full package of normal form, effective bounds, rich fibres,
  and prescribed common jumps has not been established by this review.

## What is not proved

- A classification of every upward-closed degree spectrum.
- Absence of minimal spectrum members. Absence of a least member is different.
- The general effective-dense least-representative problem.
- Optimality of the upper-cone threshold or construction oracle.
- Arbitrary prescribed sublinear counting budgets for these general cores.
- A verified Lean/Rocq implementation.

## Executed checks

`code/verify.py` passed 552,927 finite cases; see `data/verification.json`.
The PDF was compiled with pdfLaTeX, cross-references were resolved, and rendered
pages were inspected. The delivered build has no LaTeX undefined-reference,
overfull-box, or underfull-box warnings. These checks address finite arithmetic
and document quality, not the validity of the infinitary theorems.
