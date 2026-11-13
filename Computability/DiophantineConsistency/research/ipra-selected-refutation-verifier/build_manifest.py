#!/usr/bin/env python3
"""Freeze both historical 13-variable chains and selected checker additions."""
import argparse, hashlib, json, re, subprocess
from pathlib import Path
if not __debug__: raise RuntimeError('assertions required')
D = Path(__file__).resolve().parent
ROOT = D.parents[3]
BASE = D.parent / 'ipra-standard-13-frontier/author-additions.json'
assert hashlib.sha256(BASE.read_bytes()).hexdigest() == '2a4749c34750dbff650e19b5e5fc7effd98a64774c4051852f3db39221b2f134'
p = argparse.ArgumentParser(); p.add_argument('--source-commit', required=True); args = p.parse_args()
assert re.fullmatch('[0-9a-f]{40}', args.source_commit)
m = json.loads(BASE.read_text()); assert len(m['order']) == 8 and m['status'] == 'FROZEN_ADDITIONS'
m['source_commit'] = args.source_commit
m['scope'] = ('Single-overlay historical author extension of audited AQ29 parent: rebuild both 13-variable endpoint chains and the selected bounded-checker clients; not a paired or current-source replay.')
for short in ['IPRASelectedMatrixCharacteristic', 'IPRASelectedCheckerConsistency']:
    name = 'DiophantineConsistency.' + short
    path = D / 'draft-src' / (short + '.lean'); rel = str(path.relative_to(ROOT))
    blob = subprocess.run(['git', 'show', args.source_commit + ':' + rel], cwd=ROOT, check=True, capture_output=True).stdout
    assert blob == path.read_bytes()
    imports = re.findall(r'^import\s+([A-Za-z_][A-Za-z0-9_.\']*)\s*$', blob.decode(), re.M)
    assert len(imports) == len(set(imports))
    m['order'].append(name)
    m['sources'][name] = {'workspace_path': rel, 'sha256': hashlib.sha256(blob).hexdigest(), 'imports': imports}
    declarations = re.findall(r'^#print axioms ([A-Za-z_][A-Za-z0-9_.\']*)\s*$', blob.decode(), re.M)
    if declarations: m['axiom_reports'][name] = [name + '.' + x for x in declarations]
assert len(m['order']) == len(m['sources']) == 10
assert sum(map(len, m['axiom_reports'].values())) == 16
out = D / 'author-additions.json'; out.write_text(json.dumps(m, indent=2, sort_keys=True) + '\n')
print('SELECTED_CHECKER_FROZEN_MANIFEST', hashlib.sha256(out.read_bytes()).hexdigest())
