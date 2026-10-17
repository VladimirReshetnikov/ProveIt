# Internal stack tails have a numerical drain bound

[`ArithmeticStackTail254`](../../Lean/BusyBeaver/ZFC/ArithmeticStackTail254.lean)
represents repeated Cantor-tail extraction by a fixed Σ1/Δ1 graph. In every
IΣ1 model, for all internal streams `z` and iteration counts `k`, it proves

```text
tailIter(k,z) = 0  or  tailIter(k,z) + k <= z.

z <= k  implies  tailIter(k,z) = 0.
```

A positive stream's second Cantor projection is strictly smaller than the
stream code. This follows from Cantor reconstruction and the positive
triangular term. Zero is absorbing. Pointwise Σ1 induction on time, with
the original stream fixed, gives the bound. No interpretation as an external
finite list is required.

The module also proves exact zero/successor, semigroup, shift and cons laws.
These let a [bounded stack certificate](arithmetic_enumerator_soundness_plan254.md)
cover every stream entry: offsets beyond the stack's numeric code read truth
zero, certified by proof code 1.

The [fresh source/audit check](results/arithmetic-stack-tail254-verification.json)
passes fourteen axiom reports and fifteen callers, with standard axioms only
and zero warnings. It reuses eleven matched project prerequisites. The
[independent review](results/arithmetic-stack-tail254-review.json)
checks the full source, audit, final proof normalization and actual selected
providers. This module proves no runtime preservation or scheduler soundness.

The portable wrapper accepts a successful RefutationWord record as a provider
inventory, selecting only the eleven actual project prerequisites. Its
maintained-default preparation passes without invoking Lean.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_stack_tail254.py \
  --repo /path/to/Proofs --dependency-root /path/to/built/dependency-checkout \
  --refutation-evidence /outside/successful-refutation-word/verification.json \
  --output /outside/new-empty-stack-tail-check
```
