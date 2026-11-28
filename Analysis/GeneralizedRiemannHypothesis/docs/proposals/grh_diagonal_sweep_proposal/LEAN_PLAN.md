# Integration plan (not a compiled Lean patch)

Baseline: ProveIt commit `835c3695d07c0f77060c5cc63f92eeb52a7d21c2`, under `Analysis/GeneralizedRiemannHypothesis/Lean/grh/src/New/Determinant/AuxiliaryForms/`. The report supplies the paper proofs; new helper names below are suggestions.

## Phase 1 — replace the global induction, preserve public statements

1. Keep the existing dependent `GridPath` type, constructors, append, `TwoGridPath`, and the local transfer lemmas in `Turns.lean` and `DiagonalTurns.lean`.
2. Define typed right and down runs (induction on length). Define the synchronized paths `P(j)` with both words `R^j D^(m-j)` and the active word `H(j,b) = R^j D^(m-b) R D^(b-j-1)`. Use bounded indices or explicit inequalities to avoid truncated-subtraction corner cases. Prove `P(0)=first`, `P(m)=last`, `H(j,j+1)=R^j D^(m-j-1) R`, `H(j,m)=R^(j+1) D^(m-j-1)`.
3. For `j<m`, instantiate the diagonal transfer with both prefixes `R^j D^(m-j-1)`. For `j+1≤b<m`, instantiate the off-diagonal transfer with `q=R^j D^(m-b-1)` and suffix `D^(b-j-1)`; this goes from `H(j,b)` to `H(j,b+1)` in one half. Induct on `b` (half false, then half true), holding the other half fixed. Both halves then equal `P(j+1)`.
4. Choose local scalar families once per square. Maintain the exact `TransfersPeriods` predicate, not a stronger pointwise equality. Stage `j` has factor `V` times `1` for each off-diagonal exchange; its scalar product ranges over `{(i,k) : min i k = j, i<m, k<m}`. Prove the partition by trichotomy of `i,k`; combine with `TransfersPeriods.trans` and the product lemma for `HasAbsUpToNormPower`. The outer induction starts with reflexivity and yields the transfer with `V^m` and every square counted once.
5. Restore `exists_transfersPeriods_first_last` through `.mono` and `V^m ≤ V^(m^2)` (for `m=0` both powers are 1). This port is independent of further parameter optimization.

Do not approximate the scalar or divide by an unspecified proportionality constant, which may vanish. Preserve the quantifier order in the source contracts.

## Phase 2 — sharpen the coefficient bound

In `DiagonalTurns.lean`, retain the actual cardinality of `Matrix (D.GridIndex false (j+1) j) Unit (gridModulus ϑ).ResidueRing` instead of immediately applying `vectorCountBound`. The matching lemma already provides that cardinality. Rewrite using the rank formula in `UpperBound/Objects/Parameters.lean` and the cardinality of a function space. Stage weight: `h^(r+(2*j+1)*t)`. Fold these weights and prove `∑_{j<m}(2*j+1)=m²` by induction. Keep a compatibility wrapper for the old diagonal theorem if necessary. Change `lastPathBound` only after checking its clients; otherwise use `IsPathDatum.mono` once.

## Phase 3 — optional endpoint count

In `GridFirstColumns.lean`, bound the quotient coset count by the product of the corresponding general linear group cardinalities, themselves bounded by the matrix-space sizes. Retain the rank-dependent exponent `A` in the report. In `PathData.lean`, prove the bijection between edge-supported tuples and the dependent product of matrix types indexed by the edge set, by restriction and zero extension. Apply `Fintype.card_pi` and the rank formula to obtain `h^B`. No independence of period values is asserted. Keep the old last-path summation bound by monotonicity if desired. This phase is independent of the sweep.

## Phase 4 — validate and measure

Search the full readable tree for each candidate retirement (`rg -n 'turn_induction|exists_turn|squares_eq|exists_corner_or_eq_down_or_eq|exists_transfersPeriods_of_turn' src`). Retain every lemma that still has a client; GitHub search is not a substitute for a local dependency check. Candidate deletions are arbitrary-path turn search and square-set machinery in `GridPaths.lean`, and the dispatcher/strong-induction proof in `DiagonalTurns.lean`. Local exchange and path-period arguments are expressly not deletion targets.

Follow the repository README for pinned Lean/Mathlib dependencies. Run `lake build`, `lake env lean scripts/PrintAxioms.lean`, and the repository's prescribed checks. Verify that `Statements.lean` and `Main.lean` are unchanged. Compare total lines, nonblank noncomment lines, and build time. This environment lacks Lean and the pinned dependencies: none of those build commands was run. Do not claim measured net savings until integration succeeds.
