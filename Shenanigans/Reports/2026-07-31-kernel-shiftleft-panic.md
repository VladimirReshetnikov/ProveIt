# `Nat.shiftLeft` aborts the Lean kernel from one line of ordinary source

**Status:** robustness defect in the trusted kernel. **Not** unsoundness — the
kernel terminates rather than continuing with a wrong value. Reachable from
plain Lean with no metaprogramming, no `prelude`, no `unsafe`, and no
`native_decide`.

**Affected:** every toolchain tested — `v4.31.0`, `v4.32.0`, `v4.32.2`,
`v4.33.0-rc1`. Verified here with `elan run leanprover/lean4:<v> lean --trust=0`.

## Reproduction

```lean
example : (1 : Nat) <<< 4294967296 = 0 := rfl
```

```
INTERNAL PANIC: Nat.shiftl exponent is too big
```

`lean` exits 1 having printed nothing else. The same happens via `by decide` and
via the fully explicit `Nat.shiftLeft 1 4294967296`. It happens under
`--trust=0`, so this is the kernel, not the elaborator.

## Mechanism

`type_checker::reduce_nat` (`src/kernel/type_checker.cpp`) dispatches each
accelerated `Nat` operation to a helper. Two of the helpers bound the magnitude
of their argument; the shift helpers do not:

```cpp
#define ReducePowMaxExp 1<<24 // TODO: make it configurable

optional<expr> type_checker::reduce_pow(expr const & e) {
    ...
    if (v2 > nat(ReducePowMaxExp)) return none_expr();      // declines
    return some_expr(mk_lit(literal(nat(nat_pow(v1.raw(), v2.raw())))));
}
```

```cpp
if (f == *g_nat_pow) return reduce_pow(e);                       // guarded
if (f == *g_nat_shiftLeft) return reduce_bin_nat_op(lean_nat_shiftl, e);   // NOT guarded
if (f == *g_nat_shiftRight) return reduce_bin_nat_op(lean_nat_shiftr, e);
```

`reduce_bin_nat_op` whnfs both arguments, checks only that they are `Nat`
literals, and calls the runtime function. `lean_nat_shiftl` accepts a shift up
to `UINT_MAX` and above that calls `lean_internal_panic`, which aborts the
process — it does not raise a `kernel_exception`, so nothing upstream can catch
it.

Returning `none_expr()` (as `reduce_pow` does) is the correct behaviour: it
declines to use the accelerator, and the kernel falls back to delta-reduction,
which is sound and merely slow.

## Controls

Every control was run on `v4.32.2` with `--trust=0`.

| Term | Result |
| --- | --- |
| `(2 : Nat) ^ 4294967296 = 0 := rfl` | clean error: `exponent 4294967296 exceeds the threshold 256, exponentiation operation was not evaluated` |
| `Nat.shiftRight 12345 4294967296 = 0 := rfl` | **accepted** — correct answer |
| `(1 : Nat) <<< 10 = 1024 := rfl` | accepted |
| `(1 : Nat) <<< 16777216 = 0 := rfl` | clean type-mismatch error — the 2 MB value is computed correctly and is not `0` |
| `(1 : Nat) <<< 4294967296 = 0 := rfl` | **`INTERNAL PANIC`, exit 1** |

So the defect is specific to `shiftLeft` above `UINT_MAX`: the sibling operation
with the same magnitude problem (`pow`) declines gracefully, the sibling shift
(`shiftRight`) computes the right answer, and `shiftLeft` itself is correct
below the boundary.

## Why it is not unsoundness

This matters because the closest precedent,
[lean4#8554](https://github.com/leanprover/lean4/pull/8554), was a *soundness*
bug precisely because Lean's `panic!` does **not** abort — execution continued
with a default value, making `hasFVar` and friends non-conservative.

`lean_internal_panic` is the C++ runtime's abort, not Lean's `panic!`. It
terminates the process, so no wrong value ever reaches the environment. Checked
directly: bignum shift amounts (`2^64`, `2^100`) also panic cleanly rather than
being truncated or type-confused through `lean_unbox`, so there is no path to a
wrong literal here.

## Impact

Low severity but non-trivial, because the abort is uncatchable and the trigger
is a single line of ordinary source:

* it kills the language server, so the bug presents to a user as the editor
  dying with no diagnostic;
* it kills `lake build`;
* it kills `lean --trust=0`, i.e. the external-checking path, so a pipeline that
  compiles untrusted Lean is terminated rather than returning a verdict.

## Suggested fix

Mirror `reduce_pow`: bound the shift amount in `reduce_nat` and return
`none_expr()` above the bound. A threshold on the *result* size would be better
still, since `1 <<< 4000000000` is under `UINT_MAX` and merely allocates ~500 MB
instead of panicking.

## Provenance

Found by removing a cap in a local differential fuzzer. The harness at
[`../Audits/Lean/Fuzz/NatAcceleratorBoundaries.lean`](../Audits/Lean/Fuzz/NatAcceleratorBoundaries.lean)
compares every kernel-accelerated `Nat` operation against Lean's compiled
implementation at powers-of-two boundaries. Its first version capped the
`shiftLeft` exponent at 4096 specifically to avoid large allocations — which is
exactly why the defect was missed on the first pass. The cap is now set just
below `UINT_MAX` and the oversized case is a separate, explicitly documented
probe rather than something the fuzzer runs by accident.

39,510 other accelerator applications at those boundaries showed **no**
divergence from the compiled implementation.
