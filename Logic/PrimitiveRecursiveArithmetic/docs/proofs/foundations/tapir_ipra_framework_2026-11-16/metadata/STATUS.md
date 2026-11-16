# Verification status

Baseline repository: `VladimirReshetnikov/ProveIt`

Pinned commit: `58627ed89814ba122e1f0f012f1aba103cda267b`

Inspection/build date: 2026-11-16

## Status classes

| Component | Status |
|---|---|
| Existing `ConciseIPRA` core and cited `IPRADerivations` modules | checked upstream at the pinned repository, as reported by that repository |
| Human proofs in `paper/` | fully developed mathematical arguments |
| `lean/TAPIR/Kernel.lean` | no-placeholder source candidate; unelaborated |
| `lean/TAPIR/Schedule.lean` | no-placeholder source candidate; unelaborated |
| Other `lean/TAPIR/*.lean` | formalization blueprints with visible `sorry` milestones |
| `reference/*.py` | exact host implementation; unit-tested |
| `examples/*.json` | generated finite evidence only |
| New Lean-kernel-checked theorem | none claimed |

## Runtime limitation

`lean` and `lake` were not installed in the artifact runtime.  The package does
not infer compilation from source plausibility.  Integration requires a pinned
ProveIt checkout and completion of `lean/FORMALIZATION_PLAN.md`.

## Logical boundary

Python, JSON, LaTeX, and host graph computations do not establish derivability
in iPRA.  The intended endpoint is always a term of type
`Prf PRAAx Γ φ`, produced by the Lean plan interpreter and checked by the
kernel.
