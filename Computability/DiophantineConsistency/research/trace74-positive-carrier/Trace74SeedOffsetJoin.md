# Strong seed and offset quotient from one carrier chart

`Trace74CarrierUpdate.update_three` proves in any commutative ring that the
actual chart's `M ∣ Z` survives changing coordinate 3: the modulus and the
signed offset are independent of that coordinate, and the changed part of `Z`
is a multiple of `M`.

`Trace74SeedOffsetJoin.exists_seed_offset` uses this with the first-Pell
strong-seed construction and natural modulus binding. Starting from a single
model tuple with `X > 0`, `Y > 0`, `c > 0`, the displayed first-Pell ordinate
equation and actual `M ∣ Z`, it constructs positive `tau`, `t`, and `i` and
the signed natural offset/quotient pairs. The same coordinate-3-updated tuple
satisfies actual `E`, `F`, `Q`, `f`, and `c` identities, together with the
Pell norm and divisibilities listed in the theorem. These outputs are the
matching components used by the conditional base-witness assembly.

The theorem assumes actual `M ∣ Z`; the independent CRT construction offers
it on a coordinate-1/2-updated tuple subject to its six Bézout certificates,
shape equalities and `H ∣ K`. A formal join must still transfer the first-Pell
and positivity assumptions to that tuple. The result here does not establish
the main rank/odd-ordinate matching, every coordinate's positivity, a graph
zero, or the proposed reduction.

## Observed checks

On 2026-11-04 each source was checked separately with Lean 4.32.0 using the
following command (set `MODULE` in order to `Trace74CarrierUpdate`, then
`Trace74SeedOffsetJoin`). Both checks exited 0 without warnings or `sorryAx`.
The update theorem reports `[propext, Quot.sound]`; the seed/offset theorem
reports `[propext, Classical.choice, Quot.sound]`.

```sh
MODULE=Trace74CarrierUpdate python3 - <<'PY'
import json, os, subprocess
from pathlib import Path
base = Path('Computability/DiophantineConsistency/research')
data = json.loads((base / 'trace74-main-index-eleven-draft/observations/attempt01/terminal.json').read_text())
env = os.environ.copy()
env['LEAN_PATH'] = '/tmp:' + data['lean_path']
root = base / 'trace74-positive-carrier'
name = env['MODULE']
cmd = ['timeout', '120', '/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean', '-M3000', '-j1', '-DElab.async=false', '--root=' + str(root), str(root / (name + '.lean')), '-o', '/tmp/' + name + '.olean']
raise SystemExit(subprocess.run(cmd, env=env).returncode)
PY
```

| Artifact | SHA-256 |
| --- | --- |
| `Trace74CarrierUpdate.lean` | `b72c644f7f4cccc75d04fe48abfa65484a4dde7104cec3c1a4f0f87c7cd89ca7` |
| `/tmp/Trace74CarrierUpdate.olean` | `202666034e65c4bd2e23f4074b1f6273747ff098eaf76a1541dcfb690a37d910` |
| `Trace74SeedOffsetJoin.lean` | `c403a60400a119dfac6d0488dd95135dcbed115cf8f08994437605f08ec8d41c` |
| `/tmp/Trace74SeedOffsetJoin.olean` | `202edc24735c0983f463c5f1dcd065f006c64a57e8fee7af2ece3a156c352cc0` |
| `/tmp/Trace74OffsetNatural.olean` | `7055503204a173e74a4cd0e435fd07e32358aa227096d96003c5b844965c29d1` |

These checks used temporary prebuilt providers; full project, package, and
dynamic ancestry was not independently rebuilt or audited.
