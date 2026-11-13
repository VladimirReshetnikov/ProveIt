# Held standard-natural finite interval check

This one-stage guarded author check passed and passed independent post-run review. Its unchanged [source-reviewed](../../reviews/trace74-boundary-natural-seed-draft-independent/README.md) draft proposes ordinary kernel `decide` for two strict finite inequalities and then derives positive additive slacks. It does not yet assemble a graph zero, fixed BFS tuple result or iPRA endpoint. The Lean execution is recorded below.

The parent is the independently [audited recurrence-cast union](../../reviews/trace74-boundary-recurrence-cast-result-independent/README.md). Read-only preflight found 2027 project objects, 81 outside objects and one new stage. Four inherited baseline nodes retain their source-ancestry boundary; outside/package/dynamic and external equation-file binding remain outside the claim. The check uses `-M3000`, a 600-second timeout, one Lean thread, the two-process/8-GiB guard and a pinned no-clobber outer supervisor. No `native_decide` or native compiler trust is used in the source.

- `run.py` SHA-256 `f9620254f4ec717c6f2f8e0db155439588b213b198d4618d5b0f139738f4caf9`.
- `run-outer.py` SHA-256 `772380f9fa68a24aab910012e1bc91f05d35186573f0ab978c747cda13624296`.
- Read-only preflight terminal SHA-256 `cbc190b38fe8659893612f42dd73fd7d9e934b5724b84d81dc17a5b37ca82622`.
- Twenty-three runner policy controls SHA-256 `f4102d09294a63c03d8e451f36a618047dddbb147671f92cc2e1d6ed4a32e06c`.
- Six outer supervisor controls SHA-256 `bb85b906ac1531988e59ca553a2a432fbe8a09e721e4ada89910c1b2f50e12d7`.

The policy requires both named theorem reports exactly once and in order, accepts only `propext`, `Classical.choice`, and `Quot.sound` as reported axioms, and rejects any diagnostic, `sorryAx`, extra output or stderr. Controls test missing, duplicate, reordered or renamed reports and unexpected axioms. Successful checking would establish only the finite interval and slack identities; connecting them to the parametric graph theorem remains separate.

The [independent prelaunch review](../../reviews/trace74-boundary-natural-seed-prelaunch-independent/README.md) gave scoped GO. Attempt01 passed with actual outer session 6612 exit 0 and stable inputs/wrapper. Child result SHA-256 `f76e0a3263df655f5f35315ff60bbe9d7aeb203f792b156f6c1f3c9aa7f9bb5c`; outer terminal SHA-256 `f5bcc7d4c507ef0cf8c46b9f88b7692b59edd43de8e5e7c561fdf5ad73ce0bc6`; object SHA-256 `6f9b6e3e20fa2b9ae63a299b8cbd3462ca463e403286e642cbd58f8e1119836b`. `interval` reported `[propext]`; `slacks` reported `[propext, Classical.choice, Quot.sound]`. Ordinary `decide` is used and no native compiler axiom is reported. The output union contains 2028 objects; the [independent post-run audit](../../reviews/trace74-boundary-natural-seed-result-independent/README.md) passed.
