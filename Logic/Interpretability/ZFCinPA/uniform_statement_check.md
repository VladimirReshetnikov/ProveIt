# Checked code builder and literal uniform provability sentence

The unchanged [UniformStatement source](Lean/ZFCinPA/UniformStatement.lean)
passes a fresh Lean check and **27 axiom probes with 27 typed clients**,
with no warnings. The [actual record](results/uniform-statement-verification.json)
checks the Σ₁-definable, total and single-valued builder for bounded-consistency
formula codes at every element of an IΣ₁ model. At each external natural
number, its value agrees with the quotation of `conZFCSet n`.

The literal uniform arithmetic sentence is equivalent to internal ZFC
provability of the builder's value at every model element. D1 supplies those
proofs at standard numeral inputs. The final soundness/completeness theorem
characterizes a PA proof of the uniform sentence by the selector property
in every PA model; it leaves that selector property as an obligation.
Numeralwise proofs do not establish the nonstandard cases.

Source and audit took 13.639 and 2.719 seconds with one thread, 4,096 MiB
and a shared 120-second deadline. The source's existing local recursion-depth
setting of 8,000 on `quote_conZFCSet` is preserved. The audit uses default
proof limits. All 382 recorded inputs and the fresh first-provider object
remained unchanged; every probe uses only standard Lean axioms.

The guard selects 37 project providers from the actual Translation,
FixedPoint and NativePeel records. Seven opaque Foundation/Mathlib boundaries
and Init remain explicit. The cached D1 provider is bound to the selected
pair in the older ConstructibleInterpretation record; its historical version
query, per-command timeout and absence of modern artifact captures remain
recorded. FixedPoint's thirteen source style warnings also remain in the
parent evidence. No full-cache check or fresh D1 compilation is claimed.

The [publication](results/uniform-statement-publication.json) and
[history](uniform-statement/history.json.gz) preserve the source-only plan,
subsequent actual-provider guard, source snapshots and raw logs. The
[root source/API review](uniform-statement/root-source-review.json) records
the standard/internal distinction before execution. This closes one original
validator inventory entry while preserving the uniform selector obligation.
