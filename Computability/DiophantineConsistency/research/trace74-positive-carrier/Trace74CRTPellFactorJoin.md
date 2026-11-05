# Internal Pell factor joined to the CRT tuple

`Trace74CRTPellFactorJoin.exists_first_pell_carrier` applies the graph carrier
factor theorem to the same natural tuple used by the CRT/first-Pell bridge.
It replaces that bridge's explicit `H ∣ K` premise by three explicit
bindings to one internal Pell index and parameter:

* actual `X = power 2 nP`;
* actual `c = ycoord nP bP`;
* actual `A = bP + 1`.

All six CRT coprimality certificates, parameter-shape equalities, the first
Pell ordinate equation and positivity assumptions remain hypotheses. The
result constructs a coordinate-1/2-updated tuple with actual `M ∣ Z` and
the first-Pell and positivity inputs needed by the separate strong-seed and
offset join. It does not prove these hypotheses jointly realizable, identify
the separate CRT modulus with actual `c`, expose the CRT rank residue, or
construct a graph zero.

## Observed check

The source SHA-256 was
`29458dc99f62ef6b68aced0bc1a29a9ba84268a4eafd3f0f7dd880a9cc645019`.
On 2026-11-04 Lean 4.32.0 exited 0 without warnings on the command below,
reporting `[propext, Classical.choice, Quot.sound]` and no `sorryAx`.

```sh
python3 - <<'PY'
import json, os, subprocess
from pathlib import Path
base = Path('Computability/DiophantineConsistency/research')
data = json.loads((base / 'trace74-main-index-eleven-draft/observations/attempt01/terminal.json').read_text())
env = os.environ.copy()
env['LEAN_PATH'] = '/tmp:' + data['lean_path']
root = base / 'trace74-positive-carrier'
cmd = ['timeout', '120', '/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean', '-M3000', '-j1', '-DElab.async=false', '--root=' + str(root), str(root / 'Trace74CRTPellFactorJoin.lean'), '-o', '/tmp/Trace74CRTPellFactorJoin.olean']
raise SystemExit(subprocess.run(cmd, env=env).returncode)
PY
```

The output object SHA-256 was
`f75b557d597b06d104a9301376a5e3f9a847620d1906124ea8f3f0d89fe532dd`.
The directly imported `/tmp/Trace74CRTFirstPellJoin.olean` and
`/tmp/Trace74PellCarrierGraph.olean` hashes were
`00e5aad90aec95d820d4525692d127f640a728fb164bf296d5efe234a1de792b` and
`27d54ff39df4259d29b464b3ba0a8476d3a687d774a8a41b6961a9ae507705f2`.
The check used temporary prebuilt providers; full project, package, and
dynamic ancestry was not independently rebuilt or audited.
