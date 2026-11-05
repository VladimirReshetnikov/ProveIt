# Strong seed and carrier divisibility on one tuple

`Trace74StrongCarrierChart.lean` joins the first-Pell strong-seed chart with
the actual carrier-divisibility lemma. Its `carrierInputs` predicate records
the three explicit requirements on the **same** base tuple: `bJ ∣ B`,
`XY ∣ k − rank − 1`, and `H ∣ K`. These inputs do not depend on coordinate 3.
Thus, after the strong seed updates that coordinate, `exists_chart` obtains
the actual strong `F`, `f`, and `Q` identities together with actual `M ∣ Z`
on the updated tuple, and retains the seed's stated inequalities and
divisibilities.

The theorem assumes the first Pell ordinate equation, `X > 0`, `Y > 0`,
`c > 0`, and all three carrier inputs. It does not yet derive these inputs
from the independently constructed CRT witnesses, or obtain the remaining
rank, auxiliary-orbit, positivity and exact offset data needed for a zero.
No graph zero, reduction, or iPRA equivalence is claimed.

## Observed check

Source SHA-256:
`18ba0e701f654b3344922cf53c8acc029224dcfba80a3ff76abfdfc36f5060d0`.
On 2026-11-04 Lean 4.32.0 exited 0 without warnings on the command below.
`carrierInputs_update_three` reported `propext`; `exists_chart` reported
`propext`, `Classical.choice`, and `Quot.sound`. Neither report includes
`sorryAx`.

```sh
python3 - <<'PY'
import json, os, subprocess
from pathlib import Path
base = Path('Computability/DiophantineConsistency/research')
data = json.loads((base / 'trace74-main-index-eleven-draft/observations/attempt01/terminal.json').read_text())
env = os.environ.copy()
env['LEAN_PATH'] = '/tmp:' + data['lean_path']
root = base / 'trace74-positive-carrier'
cmd = ['timeout', '120', '/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean', '-M3000', '-j1', '-DElab.async=false', '--root=' + str(root), str(root / 'Trace74StrongCarrierChart.lean'), '-o', '/tmp/Trace74StrongCarrierChart.olean']
raise SystemExit(subprocess.run(cmd, env=env).returncode)
PY
```

The resulting object SHA-256 was
`8409bdafb56a070c36bc4e9bf04efbbb4dc9e60742ee826d424badbdef411550`.
The direct `/tmp/Trace74CarrierChartBinding.olean` and
`/tmp/Trace74FirstSquareStrongChart.olean` inputs had SHA-256 hashes
`dde3d30a37241c7e9a15ac6f4128750106dc24a1160a086e8f504bebe2caaa78`
and `7dcf88bcd8f020fb680083b6658db0a6c6b4da7b620d3e78b0b7baadb3bdb73b`,
respectively. The check used temporary prebuilt providers; their full project,
package, and dynamic ancestry was not independently rebuilt or audited.
