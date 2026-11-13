# CRT tuple with preserved first-Pell inputs

`Trace74CRTFirstPellJoin.exists_first_pell_carrier` composes the natural-tuple
CRT witness with the first-Pell side of the strong-seed construction. It
constructs `N` above the supplied bound and sets coordinate 1 to `1` and
coordinate 2 to `q h + N`. On that exact updated natural tuple it proves
`X > 0`, `Y > 0`, `c > 0`, the first-Pell ordinate equation and actual chart
`M ∣ Z`. Those are exactly the hypotheses accepted by the separate checked
`Trace74SeedOffsetJoin.exists_seed_offset` theorem.

The result retains all six CRT coprimality certificates, its positivity and
shape equalities, the `H ∣ K` carrier condition, and the original first-Pell
equation and positive `X`, `Y`, and `c`. In particular `c0`, the CRT modulus,
is a separate parameter and is not asserted equal to the actual chart `c` by
this lemma. The result does not provide the main odd-ordinate/rank matching,
all-coordinate positivity, or a graph zero. The CRT theorem used here
constructs a tuple with `M ∣ Z` but does not expose its intermediate rank
residue in this conclusion.

## Observed check

Source SHA-256:
`22aae5387d025e418e94c9c88a8169102a3157827dc0914f130ae857b34d11ed`.
On 2026-11-04 Lean 4.32.0 exited 0 without warnings on the command below,
reporting `[propext, Classical.choice, Quot.sound]` and no `sorryAx`.
The earlier rejected coercion attempt is retained in
`observations/crt-first-pell-attempt01/`; it is not used by this check.

```sh
python3 - <<'PY'
import json, os, subprocess
from pathlib import Path
base = Path('Computability/DiophantineConsistency/research')
data = json.loads((base / 'trace74-main-index-eleven-draft/observations/attempt01/terminal.json').read_text())
env = os.environ.copy()
env['LEAN_PATH'] = '/tmp:' + data['lean_path']
root = base / 'trace74-positive-carrier'
cmd = ['timeout', '120', '/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean', '-M3000', '-j1', '-DElab.async=false', '--root=' + str(root), str(root / 'Trace74CRTFirstPellJoin.lean'), '-o', '/tmp/Trace74CRTFirstPellJoin.olean']
raise SystemExit(subprocess.run(cmd, env=env).returncode)
PY
```

Output object SHA-256:
`00e5aad90aec95d820d4525692d127f640a728fb164bf296d5efe234a1de792b`.
Direct inputs `/tmp/Trace74CRTNaturalTuple.olean` and
`/tmp/Trace74SeedOffsetJoin.olean` had SHA-256 hashes
`179954bfa22feb2c54af4d56f86e8276ca93b6a1f3d142aca56de0282dd1fda2`
and `202edc24735c0983f463c5f1dcd065f006c64a57e8fee7af2ece3a156c352cc0`.
This check used temporary prebuilt providers; full project, package, and
dynamic ancestry was not independently rebuilt or audited.
