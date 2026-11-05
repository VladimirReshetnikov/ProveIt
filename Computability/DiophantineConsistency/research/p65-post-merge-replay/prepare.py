#!/usr/bin/env python3
"""Prepare an isolated, deliberately uncached replay of the visible drift closure."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

RESEARCH = Path(__file__).resolve().parent.parent
OUT = Path('/tmp/p65-post-merge-replay')
PACKETS = ('p65-reverse-provider', 'p65-canonical-endpoint-provider')
UPDATED = {
    'DiophantineConsistency.Compact44.P72Exact': 'b4d7364433df15a205eea5b32a253761c77e0e21b5fe10a57c7e9822b6da6c99',
    'DiophantineConsistency.Compact44.P72Power': 'f46584fb3977ae5fc33b31bee18e8c27435d97bea10138f163af2de5ee66d462',
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


if OUT.exists():
    raise SystemExit(f'refusing to overwrite existing output: {OUT}')

entries = []
selected = set(UPDATED)
for packet in PACKETS:
    root = RESEARCH / packet
    manifest = json.loads((root / 'manifest.json').read_text())
    results = json.loads((root / 'results.json').read_text())
    if manifest['missing']:
        raise SystemExit(f'missing recorded imports in {packet}')
    for e in manifest['order']:
        expected = UPDATED.get(e['module'], e['source_sha256'])
        if sha(Path(e['original'])) != expected:
            raise SystemExit(f'source mismatch: {e["module"]}')
        result = results[e['module']]
        if sha(Path(result['object'])) != result['object_sha256']:
            raise SystemExit(f'object mismatch: {e["module"]}')
        if e['module'] in selected or selected.intersection(e['imports'].values()):
            entries.append((packet, e))
            selected.add(e['module'])
    for name, binding in manifest['bindings'].items():
        if sha(Path(binding['object'])) != binding['sha256']:
            raise SystemExit(f'provider mismatch: {packet}: {name}')

expected_modules = [
    'P72Exact', 'P72Power', 'P72Facts', 'P65Facts',
    'P72ConvArith', 'P72Converse', 'P65Converse', 'IPRAPositive65',
]
if [e['module'].split('.')[-1] for _, e in entries] != expected_modules:
    raise SystemExit('unexpected visible affected closure')

OUT.mkdir()
(OUT / 'lib').mkdir()
subprocess.run(['cp', '-as', '/tmp/p65-canonical-endpoint-provider/lib/.', str(OUT / 'lib')], check=True)
plan = []
for packet, e in entries:
    module = e['module']
    src = Path(e['original']).read_text()
    subs = e['imports']
    def replace(match):
        return match.group(1) + subs[match.group(2)]
    shim = re.sub(r'^(import\s+)(\S+)', replace, src, flags=re.M)
    dest = OUT / 'src' / (module.replace('.', '/') + '.lean')
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text(shim)
    if module not in UPDATED and sha(dest) != e['shim_sha256']:
        raise SystemExit(f'unexpected shim difference: {module}')
    obj = OUT / 'lib' / (module.replace('.', '/') + '.olean')
    if not obj.is_symlink():
        raise SystemExit(f'expected isolated overlay symlink: {obj}')
    obj.unlink()
    plan.append({'packet': packet, 'module': module, 'source': e['original'],
                 'source_sha256': sha(Path(e['original'])), 'shim': str(dest),
                 'shim_sha256': sha(dest), 'imports': subs, 'object': str(obj)})
(OUT / 'plan.json').write_text(json.dumps(plan, indent=2) + '\n')
print(f'Prepared {len(plan)} forced rebuilds in {OUT}; no compiler was run.')
