# Proof audit

The paper contains conventional proofs, not proof-assistant certificates.
This ledger records the mathematical obligations that were checked in the
construction. The names below refer to theorem headings, not page numbers.

## Dependency structure

1. **Descriptions stay in the class.** Density-zero disagreement preserves
   the entire coarse-description class; the identity functional supplies both
   uniform reductions. A non-coarsely-computable target has no computable
   representative in either coarse-equivalence class.
2. **Explicit diagonal set.** A positive finite convergence formula makes A
   c.e. Each column is either the complement of a total binary computation or
   a finite set. A column of fixed positive density defeats each computable
   candidate description. Finite unions of columns are individually computable.
3. **Two-reservoir lemma.** Search for finite cross-disagreement. If none exists,
   any common total output is computed by searching for the first convergence
   on one side and comparing it with the actual convergence on the other side.
4. **Perfect fusion.** At each level split nodes, process finitely many pairs
   and functional indices, pad prefixes, and increase the protected region.
   All reservoir restrictions preserve earlier conclusions.
5. **Counterexample.** Vanishing tail density makes every branch a coarse
   description. The pair requirements force every common lower total function
   to be computable. Non-coarse-computability excludes computable branches and
   hence excludes a least representative.
6. **Jump bound.** The second jump chooses ordinary indices for the protected
   pieces; the first jump decides cross-disagreement relative to those indices.
   Computable branch labels yield descriptions below the second jump.
7. **Prescribed infimum.** Relativize the diagonal set and the fusion lemma;
   add an even-coordinate robust block code for Z. All representatives compute
   Z, none is below Z, and a pair of descriptions has meet exactly deg(Z).
8. **Characterization.** Upward closure and robust decoding identify precisely
   the nonuniform coarse classes whose spectrum is a principal upper cone.

The older HJKS theorems are used only for a historical cross-check and the
observation that the bare negative answer was already implicit in the
literature. They are not dependencies of items 2–7.

## Quantifier and implementation checkpoints

### Individual computability is not a uniform index sequence

For each fixed k there EXISTS an ordinary index for A restricted to P_k.
There need not be an ordinary computable function taking k to that index.
The computable-common-output argument hardcodes one fixed index and finitely
many fixed prefixes. The level construction is permitted to choose such
indices noncomputably. Its stated effective realization uses 0''.

For the relative construction, replace "ordinary computable" by "computable
in Z" and the selector by Z''. The predicate that a column computation is
binary-total is Pi^0_2(Z), not Sigma^0_1(Z).

### The first-convergence search is a genuine computation

The admissibility test queries only a fixed computable protected piece
(or its Z-computable counterpart), never the full noncomputable target.
The search halts only under the hypothesis of an actual common total output.
No claim is made that every functional is total on the whole reservoir.

A candidate finite extension on the left need not be compatible with the
actual left oracle. This is harmless: the actual right oracle supplies a
finite convergent extension for comparison, and the no-cross-disagreement
hypothesis quantifies over every admissible pair independently.

### Earlier decisions persist

Finite disagreements persist by finite use. A no-disagreement assertion
persists under restriction to smaller reservoirs. Increasing protection
prescribes only coordinates beyond the current prefix; it never repairs or
changes earlier bits. Therefore no finite-injury assumption is hidden in the
induction, and every stage finishes after finitely many tasks.

### Density uses two successive limits

For every fixed k and every branch X:

    X triangle A is contained in [0,L_k) union Q_k.

For dyadic columns:

    rho_N(X triangle A) <= L_k/N + 2^(-k).

First take N to infinity with k fixed, then k to infinity. There is no
claim of a computable convergence rate independent of the selected lengths.
The bound is uniform in branches, but the sequence of lengths can be
noncomputable.

### Every pair requirement is met

Two distinct branches have distinct labels from some level onward. Given
any two functional indices, choose a later stage at which both are at most
the stage number. Its finite task list contains those labels and indices.
If the final total outputs coincide, that task cannot have chosen a
permanent disagreement; it must have certified computability of the common
output. This covers all total functions, not merely binary-valued ones.

### Perfectness and complexity are separate

At every level, fresh free positions exist because Q_k is infinite.
Incompatible splits give injectivity, growing prefix lengths give continuity,
and the nested union-of-cylinders description gives closedness. Later splits
show there are no isolated points.

Only computable-label branches are asserted to be below 0'' (or Z'').
An arbitrary branch U satisfies X_U <=_T U join 0'' in the effective version.
The uncountable family is not asserted to consist of 0''-computable reals.

### Block decoding is nonuniform exact decoding

An incorrect block majority causes prefix error at least 1/4. Thus the
majority sequence eventually agrees with Z. A finite correction table proves
Z <=_T D for each individual coarse description D; the proof does not give a
uniform method for finding that table from D. This is sufficient for the
lower-bound argument and for the nonuniform characterization.

### The relative spectrum really has a greatest lower bound

Every representative computes some coarse description of A_Z, which decodes
Z. Hence deg(Z) is a common lower bound of the whole spectrum. The spectrum
contains two descriptions with meet deg(Z), so no larger common lower bound
exists. No representative can have degree deg(Z), since it would give a
Z-computable coarse description of the relative diagonal set through its
odd-coordinate projection.

## Claims deliberately NOT made

- That a class with no least representative has no minimal representatives.
- That the minimal pairs constructed are minimal pairs of coarse degrees.
- That every arbitrarily well computably approximable set satisfies the
  protected-column hypotheses of the fusion theorem.
- That the upper bound 0'' is optimal, or that the witnessing descriptions
  are c.e. (the target A is c.e.).
- That the same identity-of-description-classes proof works for effective
  dense reducibility.
- That the robust-block characterization has been proved for uniform
  coarse classes by the nonuniform argument in the paper.
- That finite simulations prove oracle noncomputability or infinite results.
- That originality or expert acceptance has been established.

## Finite checks actually run

Python 3.13.5, standard library only. The checked finite product model has
65,536 pairs of four-entry partial output tables; 64,350 admit cross
disagreement and 1,186 do not. The no-disagreement cases also passed
35,580 one-side restriction checks. Dyadic counting passed 53,248 direct
count comparisons; density budgets passed 16,128 checks. Full counts,
including coding, machine execution, and column stopping, are in
`checks/results.json`.

The finite product model is a one-input abstraction. It is not a bounded
simulation of arbitrary Turing functionals and does not certify their
infinite minimal-pair behavior.
