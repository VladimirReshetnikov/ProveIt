# 78-to-79 shifted-residual graph binding

For every commutative ring, the Lean theorems `first`, `main`, `strong`,
`auxiliary`, `transport`, and `output` compare the actual 78 and 79 graph
expressions under the same valuation. They show `A78 = A79+1`, equality of
the four remaining residuals, and `output78 = output79+2*A79`. In
particular, the outputs are **not** generally equal. This binding is not a
zero-existence equivalence, residual split, or iPRA endpoint.

On 2026-11-04 Lean exited 0 with six `[propext]` axiom reports and no warnings
or `sorryAx`. A subsequent [bounded guarded replay](lean-replay.json) also
exited 0, generated the same six exact reports and a byte-identical object,
and recorded the [complete output](lean-replay.log), command and before/after
hashes of the source, Lean executable and the two direct graph objects. The
[runner](check_lean.py) refuses to overwrite outputs; a repeat needs fresh
paths in a copy.

| Artifact | SHA-256 |
| --- | --- |
| `P64QCube78Binding.lean` | `59d26b65d5ce2312746f3bf70bd43fddd89b3ebac8b170d7b62c83dcf6331255` |
| `/tmp/P64QCube78Binding.olean` | `9a2ad33b9e505ea7e2042f694439d6a64684862fca6d38d107c0f4c4cc6d6ffd` |
| `/tmp/P64QCube78.olean` | `112e4979a76e241719cbb1b682e98c8cebabb3150c3349055dd6964ed12be0f5` |
| `/tmp/P64QCube79.olean` | `9f9c2112fa677ac6b330bc722741386da048fd9e01d091aa09dcdb60d24def65` |
| `check_lean.py` | `c9332993c819bcc03e449f699357d059e7be526f24fc54bbe541387478b75877` |
| `lean-replay.json` | `0b28a235fdfa00fdab699cd83f732a8ff1d63cdcec334066e05daf61f6f8e125` |
| `lean-replay.log` | `07e57d13ef56820baf33559197a46512171acdce384d88a2fd4c6cd648d0f123` |

The captured provider's full project-source/object, package-transitive,
dynamic-loading and search-path ancestry remains inherited, not authenticated
by the direct input guards.
