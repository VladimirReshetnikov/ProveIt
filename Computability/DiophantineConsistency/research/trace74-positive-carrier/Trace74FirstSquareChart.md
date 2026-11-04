# First Pell square on the actual chart

`Trace74FirstSquareChart.lean` establishes two conditional statements about a
single actual tuple in a model of `IΣ₁`. With `X > 0`, `Y > 0`, and a supplied
index whose first Pell ordinate is exactly half the tuple's `k`, `first_square`
shows that the tuple's actual first factor `E` is the square of a positive
Pell abscissa. `base_chart_inputs` derives, for that same tuple, the actual
chart's `c` and `E` identities and the main discriminant identity required by
`Trace74StrongSeedChart.exists_strong_chart`.

The proof uses the Pell norm at `b = 2(XY²−1)+1`, with positive `X` and `Y`
ensuring that the truncated subtraction behaves as expected. The ordinate
equality is an explicit hypothesis; it is not derived from a graph zero here.
The results do not construct a graph zero, establish compatibility with a
negative rank construction, or prove the claimed iPRA equivalence. The
strong-seed client still needs its other hypotheses and a same-tuple assembly.

## Observed check

The source SHA-256 was
`bff2771272d0463e3d14ff010577c762c8bef85a8ebfb96445f09d6f5b5b62aa`.
On 2026-11-04 Lean 4.32.0 exited 0 without warnings on this command from the
repository root, reporting only `propext`, `Classical.choice`, and `Quot.sound`
for both theorems, with no `sorryAx`:

```sh
python3 - <<'PY'
import json, os, subprocess
from pathlib import Path
base = Path('Computability/DiophantineConsistency/research')
data = json.loads((base / 'trace74-main-index-eleven-draft/observations/attempt01/terminal.json').read_text())
env = os.environ.copy()
env['LEAN_PATH'] = '/tmp:' + data['lean_path']
root = base / 'trace74-positive-carrier'
cmd = ['timeout', '120', '/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean', '-M3000', '-j1', '-DElab.async=false', '--root=' + str(root), str(root / 'Trace74FirstSquareChart.lean'), '-o', '/tmp/Trace74FirstSquareChart.olean']
raise SystemExit(subprocess.run(cmd, env=env).returncode)
PY
```

The output object SHA-256 was
`d44082392bbf416e7c896b1e2b71453e2b2a846168b1d288c7b01c2d5d7cf509`.
The directly imported `/tmp/Trace74StrongSeedChart.olean` and
`/tmp/Trace74PellGapBinding.olean` had SHA-256 hashes
`1302e8a76b336cb06616bfc2813a833b5296a85749bc524f6dc20d35addf5b9a`
and `8ffc0282fa2dc540cbba08255c19ca780234da569fd2ad2b1163418c0966445a`,
respectively. This is a check against temporary prebuilt providers; their
complete project, package, and dynamic ancestry was not independently rebuilt
or audited in this check.
