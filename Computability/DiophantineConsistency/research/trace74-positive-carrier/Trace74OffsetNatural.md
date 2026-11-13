# Natural modulus and signed offset

`Trace74OffsetNatural.modulus_eval` binds the actual chart modulus to the
image of the model element `(b · XY)(4A − 1)` under the same `X > 0` and
`Y > 0` hypotheses used by the strong-chart construction. These ensure
`A > 0`, so the model's truncated subtraction agrees with subtraction after
embedding in its difference ring. No positivity of every tuple coordinate is
needed for this identity.

`signed_offset` composes that identity with `Trace74OffsetQuotient`: if the
actual chart additionally satisfies `M ∣ Z`, then the signed offset and its
quotient have the natural-difference representation required by the
conditional base-witness theorem. This does not itself construct a graph zero
or discharge the other seed, rank, or coordinate assumptions.

## Observed check

Source SHA-256:
`6e03791fdce537bb1a1b1df2a0cf5bd34b1a893b16baf03e291c26441f830ae7`.
On 2026-11-04 the following Lean 4.32.0 check exited 0 with no warnings.
Both theorem reports list `[propext, Classical.choice, Quot.sound]`, with no
`sorryAx`:

```sh
python3 - <<'PY'
import json, os, subprocess
from pathlib import Path
base = Path('Computability/DiophantineConsistency/research')
data = json.loads((base / 'trace74-main-index-eleven-draft/observations/attempt01/terminal.json').read_text())
env = os.environ.copy()
env['LEAN_PATH'] = '/tmp:' + data['lean_path']
root = base / 'trace74-positive-carrier'
cmd = ['timeout', '120', '/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean', '-M3000', '-j1', '-DElab.async=false', '--root=' + str(root), str(root / 'Trace74OffsetNatural.lean'), '-o', '/tmp/Trace74OffsetNatural.olean']
raise SystemExit(subprocess.run(cmd, env=env).returncode)
PY
```

The resulting object SHA-256 was
`7055503204a173e74a4cd0e435fd07e32358aa227096d96003c5b844965c29d1`,
and the direct `/tmp/Trace74OffsetQuotient.olean` input SHA-256 was
`dc711c7bd4a2681670742a34e58cd5cb53ebfde814709098167866362e307543`.
The check used temporary prebuilt providers; complete project, package, and
dynamic ancestry was not independently rebuilt or audited.
