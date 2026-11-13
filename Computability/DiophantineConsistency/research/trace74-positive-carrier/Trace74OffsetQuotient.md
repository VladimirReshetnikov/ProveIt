# Extracting the signed offset quotient

`Trace74OffsetQuotient.signed_offset` shows that actual chart divisibility
`M ∣ Z`, together with the explicit identity of chart `M` with the image of a
model element, supplies natural elements `C`, `G`, `P`, and `S` such that the
actual signed offset is `ι C − ι G = ι M * (ι P − ι S)`. The proof subtracts
the chart's explicit multiple of `M` from `Z` and represents both the offset
and its quotient in the model's difference ring. These are exactly the signed
offset identities consumed by the conditional base-witness assembly.

It does not prove that `M` has the required natural representation for an
arbitrary tuple, or discharge the separate rank, Pell, positivity, and tuple
requirements of the base witness. No graph zero is asserted.

## Observed check

Source SHA-256:
`c0406fd5d655b87429d72a413d3419bd943555e545fe20321b111341b94df2e7`.
On 2026-11-04 Lean 4.32.0 exited 0 without warnings on the following command,
reporting `[propext, Classical.choice, Quot.sound]` and no `sorryAx`:

```sh
python3 - <<'PY'
import json, os, subprocess
from pathlib import Path
base = Path('Computability/DiophantineConsistency/research')
data = json.loads((base / 'trace74-main-index-eleven-draft/observations/attempt01/terminal.json').read_text())
env = os.environ.copy()
env['LEAN_PATH'] = '/tmp:' + data['lean_path']
root = base / 'trace74-positive-carrier'
cmd = ['timeout', '120', '/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean', '-M3000', '-j1', '-DElab.async=false', '--root=' + str(root), str(root / 'Trace74OffsetQuotient.lean'), '-o', '/tmp/Trace74OffsetQuotient.olean']
raise SystemExit(subprocess.run(cmd, env=env).returncode)
PY
```

The object SHA-256 was
`dc711c7bd4a2681670742a34e58cd5cb53ebfde814709098167866362e307543`,
and the direct `/tmp/Trace74StrongCarrierChart.olean` input SHA-256 was
`8409bdafb56a070c36bc4e9bf04efbbb4dc9e60742ee826d424badbdef411550`.
This check used temporary prebuilt providers; full project, package, and
dynamic ancestry was not independently rebuilt or audited.
