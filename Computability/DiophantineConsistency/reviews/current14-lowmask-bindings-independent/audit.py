#!/usr/bin/env python3
"""Read-only check of retained low-mask author receipts and their inputs."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
DIR = ROOT / 'Computability/DiophantineConsistency'
PINS = {
    'research/current14-lowmask-display-binding/observations/author04/observation.json':
        'e8301fad5272cb88d3b84fb4ae2a84b4b685704460b42034398537ce477a3721',
    'research/current14-lowmask-integer-binding/observations/author04/observation.json':
        'f2cbfad9db61ea388f2ee20649e4187a5ec50f8c6368a60d4897c28db3f079c8',
    'research/current14-literal-port-assembly/Current14LiteralPorts.lean':
        'b19dfc3f5ea1639dcd6003613cd587992d3ab64f707cbe7c9fb61a466092f8b0',
    'Lean/DiophantineConsistency/CurrentMaskData2011.lean':
        '8e92c1f507bc250c31fb2671a921dfbef7a44ba643956f962cd64d9b50bd4582',
    'Lean/DiophantineConsistency/CurrentKernelData2011.lean':
        '529b2f89e4e93516a8a52343d98dc749c57f5a967d8ef522b92373bf3adf0a2c',
    'Lean/DiophantineConsistency/CurrentMaskRecipes2011.lean':
        '56df0219f29907cc50b4a821a8d7ae895162c7987e9600ad9e3f369d47c9de4f',
    'equation.tex': '94f5eba440c5c74d5ab28f51f1104aae13a774ab0238ed9e46b24a4c6b2f9635',
}
def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()
for path, expected in PINS.items():
    if sha(DIR / path) != expected:
        raise RuntimeError('pinned file differs: ' + path)
results = {}
for part in ('display', 'integer'):
    relative = 'research/current14-lowmask-' + part + '-binding/observations/author04/observation.json'
    obs = json.loads((DIR / relative).read_text())
    if obs['exit'] != 0 or obs['reason'] is not None or obs['stderr'] or obs['before'] != obs['after']:
        raise RuntimeError('bad author observation: ' + part)
    for path, meta in obs['before'].items():
        if sha(path) != meta['sha256'] or str(Path(path).resolve()) != meta['realpath']:
            raise RuntimeError('recorded input differs: ' + path)
    output = Path(obs['command'][4])
    if sha(output) != obs['object_sha256']:
        raise RuntimeError('recorded output differs: ' + str(output))
    if 'sorryAx' in obs['stdout'] or 'warning:' in obs['stdout'] or 'error:' in obs['stdout']:
        raise RuntimeError('unexpected Lean report: ' + part)
    if obs['stdout'].count('propext') != 2 or obs['stdout'].count('Classical.choice') != 2 or obs['stdout'].count('Quot.sound') != 2:
        raise RuntimeError('unexpected axiom count: ' + part)
    results[part] = {'exit': obs['exit'], 'object_sha256': obs['object_sha256'],
                     'guarded_input_count': len(obs['before'])}
print(json.dumps({'status': 'PASS', 'pinned_files': PINS, 'author_observations': results,
                  'scope': 'Receipt and current input hashes; source interpretation is documented in README. No fresh Lean or ancestry rebuild.'},
                 indent=2, sort_keys=True))
