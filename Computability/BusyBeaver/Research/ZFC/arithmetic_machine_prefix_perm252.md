# Removing the checked bootstrap from internal halting

[`ArithmeticMachinePrefixPerm252`](../../Lean/BusyBeaver/ZFC/ArithmeticMachinePrefixPerm252.lean)
proves that the actual represented machine halts from blank tape if and only
if it halts from the exact checked bootstrap target, in every IΣ1 model.

First, run composition and full-configuration halt absorption give the same
equivalence before and after any internal prefix time, from any initial
code. This includes a halt occurring inside the prefix. Specializing the
blank evaluator at the [82,552-step bootstrap](arithmetic_bootstrap_perm252.md)
then removes that fixed prefix without a runtime premise.

The [fresh check](results/arithmetic-machine-prefix-perm252-verification.json)
passes four axiom reports and six callers with standard Lean axioms and no
warnings. It reuses the exact 27-module union of the RunFrom and Bootstrap
prerequisites. The [independent review](results/arithmetic-machine-prefix-perm252-review.json)
binds the proof and provider identities. An earlier source attempt failed
only because `prefix` was used as a reserved binder name; the corrected
name is `prefixTime`.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_machine_prefix_perm252.py \
  --repo /path/to/Proofs --dependency-root /path/to/built/dependency-checkout \
  --run-from-evidence /outside/successful-run-from/verification.json \
  --bootstrap-evidence /outside/successful-arithmetic-bootstrap/verification.json \
  --output /outside/new-empty-machine-prefix-check
```

Portable preparation is recorded separately from the successful source and
audit check. The original run did not separately hash bundled Omega; the
final portable guard identifies and checks its actual selected object. This
does not supply retrospective evidence for the original run.
This checkpoint reduces the remaining runtime proof to execution
from the bootstrap target; it does not supply the unbounded register or
scheduler simulation.
