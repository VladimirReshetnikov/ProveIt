# Actual short MP unpair in internal arithmetic

`ArithmeticControlUnpairCore254` proves the actual MP unpair at controls
6393–6403, stopping at constructor entry6404. With scratch1=scratch2=0, the
whole-file endpoint sets scratch1 to `first(old WS)` and WS to `second(old WS)`.
Every other field is preserved, including scratch2=0.

The new `UnpairCoreShape` stops after restoring the second component. It
explicitly omits the output-transfer premises of the existing full NIP shape,
which cannot describe MP's `.decnz 1` exit. The two transfer loops reuse the
checked generic `MoveShape` contract. The Cantor walk fixes the original file
and input and uses bounded Σ₁ induction with an existential internal clock.

The module also composes the checked initial parameter push with this short
unpair. From MP entry6367 to constructor entry6404, it sets scratch1 to old TW
and TW to old param1 while restoring the original WS and preserving every
other field. Internal Cantor projection identities justify the cancellation.

The first source check passed in 8.626 seconds with no warnings. The first
audit failed on one `rfl` record-projection equality because it reached Lean's
default recursion limit. The source and its recorded object were frozen.
Changing that audit equality to `simp only [mpCore]` allowed an audit-only
continuation to pass in 2.368 seconds: 12 ordered probes, 18 callers, only
`propext`, `Classical.choice` and `Quot.sound`, and no warnings. The original
overall FAIL, exact source/audit/guard and all logs are retained in history.

The source object was recorded before the original failed audit and was
verified unchanged before and after the successful continuation. No source
rebuild occurred. The guard matched 98 project prerequisites and six cached
external boundaries; the original source check had 219 inputs and the
continuation 224. Proof commands used one thread, 4 GiB, default Lean limits
and a 120-second timeout. No dependencies, bootstrap proofs or site guards
were rebuilt or replayed.

The portable guard is byte-identical to the successful continuation guard.
Its ordinary maintained-default preparation queried the compiler version and
compiled no proof. Ordinary mode can perform a complete fresh source/audit
check. The optional continuation mode pins the preserved source PASS inside
the original overall FAIL and runs only the repaired audit. Author and root
reviewed the complete source and evidence; no additional independent child
review is claimed.

The constructor pairing, scaled transfer and final move/composition needed
for full MP remain outside this module. AX, internal interpreter-to-Enum and
final PA equivalence remain open. No first-exit, exact binary clock or new
state-count claim is made.

```sh
python Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_unpair_core254.py \
  --repo "$PWD" --dependency-root /path/to/pinned/Proofs \
  --param-push-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-param-push254-verification.json \
  --output /external/fresh/unpair-core-check
```
