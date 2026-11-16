# Proposed ProveIt integration

Baseline: `27a07921176bccbf630084b959700605783ff4aa`.

A suitable home for the packet is a new foundations category:

`Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/ipra_embedding_framework/`

This is a proposed placement of the delivered archive. The work here does
not depend on a repository commit or pull request being created.

The report is cross-cutting, so placing it entirely under algebra or analysis
would obscure the common finite-demand infrastructure. The existing packet
index should describe it as human proofs with partially compiled native Lean
components and a remaining deep formalization plan.

## Dependencies and reuse

- Target theory: `ConciseIPRA/Lean/ConciseIPRA/PR.lean` and `Deduction.lean`.
- Native transport after an actual derivation is complete:
  `ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean`.
- The three compiled standalone files use only `Std` and Lean's arithmetic
  tactic support, not Mathlib. Their Lake file can be used independently.
- `ObjectInterface.lean` requires the repository's ConciseIPRA library. It is
  explicitly an uncompiled integration outline, not one of the standalone
  checked modules.

## Suggested first complete object-theory theorem

Implement the hyperelliptic fiber bound first. It requires only exact finite
rational arithmetic, polynomial synthetic division, grouping a supplied point
list by abscissa, and a multiplicity counter. Its invariant is `N = C*Q`
together with degree accounting. The four-point cubic example is a small
end-to-end test.

Next implement restricted polynomial certificate soundness and the finite
algebra certificate bound. These can serve the existing algebraic and
coordinate-geometry packets. Then add the common-window selector and the
Gaussian-rational weighted-norm kernels.

## Existing difficulty reports addressed

1. `algebra/puiseux_ipra/evidence/scope_obstruction.md`: a supplied simple root
   and derivative gap allow a new positive input contract for Cauchy
   coefficients. The singular obstruction is retained.
2. `diophantine-number-theory/siegel_ipra/paper/05_general_route.tex`: the
   zero-count contract is supplied for odd-degree hyperelliptic evaluation
   systems; the finite-tuple approximation/covering theorem remains open.
3. `diophantine-number-theory/diophantine_ipra_2026-11-15/paper/02_roth.tex`:
   the existing finite-exception window idea is generalized to simultaneous
   variation and exceptional-set observations; no effective Roth cutoff is
   inferred.
4. Multiple analysis and geometry packets: finite observation contracts and
   restricted polynomial certificates expose reusable object-theory proof
   obligations instead of relying on native Lean theorem truth.

The new norm and finite-algebra arguments do not reuse an unverified global
theorem from these packets. The conditional covering corollary names its
remaining hypothesis explicitly.
