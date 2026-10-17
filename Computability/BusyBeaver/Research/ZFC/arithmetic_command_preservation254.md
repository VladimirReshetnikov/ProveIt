# Internal soundness of the actual commands

[`ArithmeticCommandPreservation254`](../../Lean/BusyBeaver/ZFC/ArithmeticCommandPreservation254.lean)
proves local soundness of every actual numeric command in every IΣ1 model.
Given a certified working state, a nonzero result preserves certification
of result minus one. A zero result supplies an accepted internal falsity
proof. Both statements use the actual shifted-success/zero-halt convention
and quantify over all internal raw commands.

Successful MP constructs the original MP proof witness, pushes truth and
clears the cache. Failed MP uses truth. DROP reuses the cache witness and
pushes the old top. Continuing NIP uses the certified stream's head and tail;
halting NIP extracts the accepted proof of cached falsity.

AX retains the literal label-collision test and all ten stack pushes: the
eight logical axioms, GEN of the old cache, and the old top. Its new top has
either a truth witness or the original bundle witness with both freshness
inequalities. A fixed list of ten internal proof codes enlarges the existing
bound explicitly. No collection principle or assumption of standard proof
codes is needed.

The [fresh source/audit check](results/arithmetic-command-preservation254-verification.json)
passes twelve axiom reports and fifteen callers, with only standard Lean
axioms and no warnings. It reuses 23 exact project prerequisites and four
identified external providers. The [independent review](results/arithmetic-command-preservation254-review.json)
and root review cover the final source, audit, dependencies and portable
checker. Earlier namespace/type and audit-syntax failures remain recorded;
the final falsity witness is explicitly typed in the arithmetic model.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_command_preservation254.py \
  --repo /path/to/Proofs --dependency-root /path/to/built/dependency-checkout \
  --certificate-evidence /outside/successful-stack-certificate/verification.json \
  --run-evidence /outside/successful-enumerator-run/verification.json \
  --output /outside/new-empty-command-preservation-check
```

Maintained-default and relocated-cache preflights are recorded separately;
they invoke no Lean process. The [scheduler equivalence](arithmetic_enumerator_equivalence254.md)
lifts this local result by Σ1 time induction. Internal binary execution and
C254/ZFC proof transformations remain open.
