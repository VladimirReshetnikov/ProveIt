# Source audit

## Pinned repository state

The design was prepared against `VladimirReshetnikov/ProveIt` commit
`2ef31aa3e313d792df6b63bb28babfe48e1f982e` (16 November 2026).
The audit focused on:

- `Logic/PrimitiveRecursiveArithmetic/README.md`;
- `UNIFICATION-PLAN.md` and `ENDPOINTS.md`;
- `ConciseIPRA/Lean/ConciseIPRA/{Syntax,Deduction,PR}.lean`;
- `Derivations/README.md`, `Core/Basic.lean`, and `Core/Search.lean`;
- `Bridge/README.md` and its open-sequent API;
- the FINER, KIFC-S, CBIP, bounded-reflection, and scoped-certificate packets.

## Reused checked interfaces

DARC treats the following as upstream interfaces rather than reproving them:

1. ordinary scoped derivability `Prf PRAAx Gamma phi`;
2. substitution, weakening, simultaneous cut, and existential elimination;
3. quantifier-free induction through `PRA.qfInd` and `IPRA.ind`;
4. primitive-recursive pairing, finite sums, order, and bounded least search;
5. closed and open transport through `IPRABridge`.

The report distinguishes an upstream theorem interface from a theorem rebuilt
inside this artifact. No upstream Lake target was rerun in this runtime.

## Novel synthesis boundary

The new contribution is not another certificate checker. It is the use of one
least finite demand state to drive all of the following at once:

- certificate-field escape analysis;
- precision propagation;
- guard/apartness propagation;
- residual-producer exposure;
- pruning of the proof graph before object-proof assembly.

Earlier packets contain several components separately. DARC gives a single
formal invariant and a global compilation theorem whose endpoint is ordinary
`Prf PRAAx`.

## Explicit nonclaims

No total evaluator for arbitrary primitive-recursive programs is used. No
infinite path is inferred from finite-horizon paths. No regular name is inferred
without a tail modulus. No ordered root/eigenvector is selected through a
collision. No effective height bound follows merely from finiteness. These are
represented as guards or residual producer formulas.
