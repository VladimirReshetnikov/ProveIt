# 79-to-80 quotient graph binding

For any commutative ring, `ell` evaluates the 80 graph's first-radicand
parameter and `liftRing p` replaces coordinate 9 of an 80 valuation by
`ell p v + v 9`, leaving other coordinates unchanged. The six Lean theorems
`first`, `main`, `strong`, `auxiliary`, `transport`, and `output` prove equality
of the actual 79 and 80 expression evaluations under this substitution. The
reverse positive witness, zero-existence equivalence, and iPRA endpoint remain
separate.

On 2026-11-04 the Lean check exited 0 with six `[propext]` axiom reports and
no warnings or `sorryAx`. A subsequent [bounded guarded replay](lean-replay.json)
also exited 0, generated the same six exact reports and a byte-identical
object, and captured [the complete output](lean-replay.log), command and
before/after hashes of the source, Lean executable and the two direct graph
objects. The [runner](check_lean.py) refuses to overwrite its outputs; a
repeat needs fresh output paths in a copy.

| Artifact | SHA-256 |
| --- | --- |
| `P64QCube79Binding.lean` | `6699312618be0598dc0cc49473533928a46fd91a54871eef444d4f600a04e6a1` |
| `/tmp/P64QCube79Binding.olean` | `563456f423a9da9904ea9c50284ad67443ed7b4ef358608e01459f7ed400bcaf` |
| `/tmp/P64QCube79.olean` | `9f9c2112fa677ac6b330bc722741386da048fd9e01d091aa09dcdb60d24def65` |
| `/tmp/P64QCube80.olean` | `e8829517e10e4c3d2423594dd884b86466834d7714038660030d16861c8abd68` |
| `check_lean.py` | `4d82492c6595574eaf6ea04976061b33e5315aa58d06f0bd403fda4114522bbf` |
| `lean-replay.json` | `a9b7bee9e42473649c340d4ce049854ac1f0d5d00722cdb5aca48954165c3dd6` |
| `lean-replay.log` | `1f5780ef73fc2bfaa3968a599a43b681ff7a366b105507becf3eb10fa459eed8` |

The captured provider's full project-source/object, package-transitive,
dynamic-loading and search-path ancestry remains inherited, not authenticated
by the direct input guards.
