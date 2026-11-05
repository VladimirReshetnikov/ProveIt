# First Pell input assembled with a strong chart

`Trace74FirstSquareStrongChart.exists_chart` combines the actual first-square
chart identities with the strong-seed construction. Given one tuple with
`X > 0`, `Y > 0`, `c > 0`, and a first Pell index satisfying the stated
ordinate equation, it constructs positive `tau`, `t`, and `i` and binds the
strong `F`, `f`, and `Q` outputs to that same chart after updating coordinate
3. It also retains the stated Pell norm and divisibility conditions. All
assumptions are explicit, and no zero of the whole graph is assumed or
constructed. In particular, compatibility with independently constructed CRT
witnesses is not established. Positivity of `c` is a separate condition: its
definition `c = kY + v₈` permits zero when both `k` and `v₈` vanish.

## Observed check

Source SHA-256:
`d2d90cd5d115cd119f14ec937b79553036ea82887783c6596722283d15048aa8`.
On 2026-11-04 the following Lean 4.32.0 check exited 0 without warnings and
reported `[propext, Classical.choice, Quot.sound]` for the theorem, without
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
cmd = ['timeout', '120', '/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean', '-M3000', '-j1', '-DElab.async=false', '--root=' + str(root), str(root / 'Trace74FirstSquareStrongChart.lean'), '-o', '/tmp/Trace74FirstSquareStrongChart.olean']
raise SystemExit(subprocess.run(cmd, env=env).returncode)
PY
```

The output object SHA-256 was
`7dcf88bcd8f020fb680083b6658db0a6c6b4da7b620d3e78b0b7baadb3bdb73b`;
the directly imported `/tmp/Trace74FirstSquareChart.olean` SHA-256 was
`d44082392bbf416e7c896b1e2b71453e2b2a846168b1d288c7b01c2d5d7cf509`.
The check used temporary prebuilt providers whose complete project, package,
and dynamic ancestry was not independently rebuilt or audited.
