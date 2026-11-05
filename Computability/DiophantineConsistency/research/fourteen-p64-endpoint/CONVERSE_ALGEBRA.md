# P64 converse residual assembly

`P64ConverseAlgebra.residuals` proves over any commutative ring that explicit
first-root, main-root, strong-norm, auxiliary-norm and transport identities
make the five actual package-64 residuals equal `0, 0, 0, 1, 0`. The main
carrier uses the candidate's `U = Y²` and explicitly requires
`k = R + 1 + 4XUt` and `gamma = gammaOld + 4Xt`; it derives the needed
carrier cancellation rather than assuming the main residual zero. The
first-root assumptions include `Y = s q³` and `ell + rho + s = tau`.

All listed identities remain hypotheses. The theorem does not construct
positive witnesses from a machine halt, prove the reverse graph implication,
or establish a native or standard iPRA endpoint. An intended next step is to
bind the canonical halt data and the first-Pell residue quotient to these
same variables and then prove their positivity.

## Graph binding and observed Lean checks

`P64GraphShim.lean` is the exact canonical `Compact44/P64Graph.lean` source
except that its first import is replaced with the captured `P65GraphShim`
provider; this is an import shim, not a fresh canonical project rebuild. The
literal gate block was compared with the pinned package-64 JSON using

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/fourteen-p64-endpoint/tools/generate_p64.py --check Computability/DiophantineConsistency/research/fourteen-p64-endpoint/P64GraphShim.lean
```

It exited 0 and reported 83 matching gates and JSON SHA-256
`b9731360a30bcbcfd6f9161241cafb01b8c5d68aa40b84ddc50ba689a0745d0e`.
On 2026-11-04 Lean 4.32.0 separately checked the graph shim and then
`P64ConverseAlgebra.lean` with exit 0 and no warnings. The residual theorem
reported `[propext, Quot.sound]`, with no `sorryAx`.

```sh
MODULE=P64GraphShim python3 - <<'PY'
import json, os, subprocess
from pathlib import Path
base = Path('Computability/DiophantineConsistency/research')
data = json.loads((base / 'trace74-main-index-eleven-draft/observations/attempt01/terminal.json').read_text())
env = os.environ.copy()
env['LEAN_PATH'] = '/tmp:/tmp/p65-post-merge-replay/lib:' + data['lean_path']
root = base / 'fourteen-p64-endpoint'
name = env['MODULE']
cmd = ['timeout', '180', '/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean', '-M3000', '-j1', '-DElab.async=false', '--root=' + str(root), str(root / (name + '.lean')), '-o', '/tmp/' + name + '.olean']
raise SystemExit(subprocess.run(cmd, env=env).returncode)
PY
```

Run first with `MODULE=P64GraphShim`, then `MODULE=P64ConverseAlgebra`.

| Artifact | SHA-256 |
| --- | --- |
| Canonical `P64Graph.lean` | `24ddb2677b60a25d16981c1043cb06754e2c01ca58b8147878086abe7f65d489` |
| `P64GraphShim.lean` | `ef6d00ee3388bce12a4e9f5534c6c0e05ba46d5663e7d4b5899487cc44b760f7` |
| `/tmp/P64GraphShim.olean` | `a1dafd038a86d88337b5d59611a1599b5fff96e9e46c9fc912a569606eeba01c` |
| `P64ConverseAlgebra.lean` | `0538b020d060ebe90da629033bb05a7458d7e4ddfe1b24c2455691fa01f6657d` |
| `/tmp/P64ConverseAlgebra.olean` | `823bebb12a1c46dfc4141ccabd386988d08293ca9456d63d9fe5354cd951f4f7` |
| `/tmp/P65GraphShim.olean` | `7bd2902eeffa586418aedef1aded667be68d32c0aeb6f3946a09d277db3dc19c` |

The imported provider and complete project, package, dynamic, and search-path
ancestry were not independently rebuilt or audited.
