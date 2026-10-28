"""Freeze the two final successful leaves and every retained failed attempt."""
import json
from pathlib import Path
import re
import shutil

from replay import BUNDLE, MANIFEST, REV, SRC, LEAVES, sha, check, require, verify, dump

d = json.loads(MANIFEST.read_text())
verify(d)
runs = [json.loads(p.read_text()) for p in sorted(BUNDLE.glob('*-FoundationHACurrentTransfer*.json'))]
final = []
for name in LEAVES:
    candidates = [r for r in runs if r['module'].endswith('.' + name) and r['exit_code'] == 0]
    require(bool(candidates), 'No successful leaf: ' + name)
    r = candidates[-1]
    check(r['source'], r['source_sha256'])
    check(r['object'], r['object_sha256'])
    final.append(r)
for r in runs:
    check(r['snapshot'], r['source_sha256'])
    check(r['log'], r['log_sha256'])
require(Path(final[0]['log']).read_text() == '', 'Unexpected final main diagnostics')
log = Path(final[1]['log']).read_text()
reports = re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", log, re.S)
require(len(reports) == 10, 'Expected ten axiom reports')
for name, body in reports:
    require(set(re.split(r',\s*', body.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'},
            'Unexpected axiom: ' + name)
for name in LEAVES:
    source = (SRC / (name + '.lean')).read_text()
    require(re.search(r'\b(sorry|admit|native_decide)\b', source) is None, 'Forbidden proof shortcut')
modules = {r['module']: r for r in d['modules']}
todo = ['DiophantineConsistency.FoundationHAPeano',
        'DiophantineConsistency.FoundationHACurrentNoZero2011']
seen = set()
while todo:
    name = todo.pop()
    if name in seen or name not in modules:
        continue
    seen.add(name)
    todo.extend(modules[name]['imports'])
require(seen == set(modules), 'Unused or unlinked custom cached module')
out = dict(d)
out.update(status='PASS', fresh_modules=final, development_runs=runs,
           axioms=[{'theorem': n, 'axioms': re.split(r',\s*', a.strip())} for n, a in reports],
           inputs_sha256=sha(MANIFEST), imported_module_count=len(seen),
           free_bytes_after=shutil.disk_usage(REV).free,
           freeze_driver_sha256=sha(__file__),
           scope='Exactly two final fresh leaves; all133 existing custom prerequisites reused with '
                 'source/object hashes,85 Foundation. No whole Foundation/native replay. '
                 'Source PA equivalence remains an explicit theorem premise.')
out['bundle_files'] = {p.name: sha(p) for p in sorted(BUNDLE.iterdir()) if p.is_file()}
target = REV / 'foundation-ha-current-transfer-dependency-replay.json'
dump(target, out)
print(json.dumps({'manifest': str(target), 'sha256': sha(target),
                  'main_source': final[0]['source_sha256'], 'checks_source': final[1]['source_sha256'],
                  'main_object': final[0]['object_sha256'], 'checks_object': final[1]['object_sha256'],
                  'failed_attempts': sum(r['exit_code'] != 0 for r in runs),
                  'axiom_reports': len(reports)}, indent=2))
