# Exact actual MP comparison in internal arithmetic

`ArithmeticControlCompare254` proves the actual destructive comparison used by
MP in every model of IΣ₁. Scratch1 and the cache may hold arbitrary internal
values. The comparison clears both fields and preserves every other field.
Equality enters the actual success push at control 6434; inequality clears the
cache and returns to the actual fetch test through the literal failure break.

If `a` and `b` are the original scratch1 and cache, and
`d = if a ≤ b then b-a else a-b`, the exact logical runtime is

```
3*a + 2*d + 2.
```

The joint decrement body takes `3*a+1` steps and leaves `d` in the cache.
Its proof fixes the original complete file and uses bounded Σ₁ induction on
an internal iteration counter `t ≤ a` and `t ≤ b`. The tail takes `2*d+1`
steps, reusing the checked literal cache-clear loop. All new controls and
continuations are bound to the actual program by walk and resolver equations.
No scratch cleanliness or standardness premise is required.

The first source and focused audit checks passed 14 ordered axiom probes and
18 callers with only `propext`, `Classical.choice` and `Quot.sound`, and no
warnings. Source checking took 7.702 seconds and the audit 2.341 seconds.
The guard matched 96 project prerequisites, six cached external boundaries and
215 inputs before and after checking. It recorded the fresh source object
before the audit and verified the same object afterward.

The two proof commands used one thread, 4 GiB, default Lean limits and a
120-second timeout. Dependencies, site guards and bootstrap proofs were not
rebuilt or replayed. The portable guard is byte-identical to the executed
guard. Its maintained-default preparation queried the compiler version and
compiled no proof. The source author and root reviewed the source and evidence;
no separate independent child review is claimed.

This completes the actual comparison helper. The full MP success push and
constructor sequence, AX, internal interpreter-to-Enum connection and final
PA equivalence remain open. The theorem does not assert a first-exit property,
an exact binary-step clock or a new machine state count.

```sh
python Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_compare254.py \
  --repo "$PWD" --dependency-root /path/to/pinned/Proofs \
  --pair-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-pair254-verification.json \
  --output /external/fresh/compare-check
```
