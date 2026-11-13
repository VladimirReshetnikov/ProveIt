#!/usr/bin/env python3
"""Pin a coherent metatheoretic annotated-checker comparison extension."""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

if not __debug__:
    raise RuntimeError('optimized Python is unsupported')

D = Path(__file__).resolve().parent
ROOT = D.parents[3]
PARENT = Path('/tmp/ipra-aq29-fresh-source-closure-v2/manifest.json')
PARENT_SHA = '63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48'
assert hashlib.sha256(PARENT.read_bytes()).hexdigest() == PARENT_SHA
parent = json.loads(PARENT.read_text())
assert len(parent['order']) == 1210
old = set(parent['order'])
parser = argparse.ArgumentParser()
parser.add_argument('--source-commit', required=True)
args = parser.parse_args()
assert re.fullmatch('[0-9a-f]{40}', args.source_commit)
composition = 'DiophantineConsistency.SelectedExternalCheckerComparison'
composition_path = D / 'draft-src/SelectedExternalCheckerComparison.lean'
base = ROOT / 'Computability/DiophantineConsistency/Lean'
rows = {}
order = []
visiting = set()
external = set()

def visit(name):
    if name in old or name in rows:
        return
    if name in visiting:
        raise ValueError(('cyclic import', name))
    path = composition_path if name == composition else base.joinpath(*name.split('.')).with_suffix('.lean')
    if not path.is_file():
        external.add(name)
        return
    if not name.startswith('DiophantineConsistency.'):
        raise ValueError(('unexpected project module outside parent', name))
    visiting.add(name)
    rel = str(path.relative_to(ROOT))
    entry = subprocess.run(['git', 'ls-tree', '-z', args.source_commit, '--', rel],
                           cwd=ROOT, capture_output=True, check=True).stdout
    head, sep, tail = entry.partition(b'\t')
    assert sep and tail == rel.encode() + b'\0' and head.split(b' ')[:2] in ([b'100644', b'blob'], [b'100755', b'blob'])
    data = subprocess.run(['git', 'show', args.source_commit + ':' + rel],
                          cwd=ROOT, capture_output=True, check=True).stdout
    assert data == path.read_bytes(), ('workspace source drift', name)
    imports = re.findall(r'^import\s+([A-Za-z_][A-Za-z0-9_.\']*)\s*$', data.decode(), re.M)
    assert len(imports) == len(set(imports)), name
    for dependency in imports:
        visit(dependency)
    visiting.remove(name)
    rows[name] = {'workspace_path': rel, 'sha256': hashlib.sha256(data).hexdigest(), 'imports': imports}
    order.append(name)

visit(composition)
assert len(order) == len(rows) == 35 and order[-1] == composition
assert external == {'Init', 'Mathlib.Computability.Primrec.Basic', 'Mathlib.Data.Nat.Pairing',
                    'Mathlib.Tactic.FinCases', 'Mathlib.Tactic.Linarith', 'Mathlib.Tactic.SplitIfs'}
for name in external - {'Init'}:
    path = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib').joinpath(*name.split('.')).with_suffix('.olean')
    assert path.is_file(), ('external provider missing', name)
reports = {
    'DiophantineConsistency.DirectScalarArithmetic': ['DiophantineConsistency.DirectScalar.ifEq'],
    composition: [composition + '.source_nat_iff_no_annotated_certificate',
                  composition + '.explicit_checker_primrec_and_semantics'],
}
assert set(reports) <= set(order)
result = {'status': 'FROZEN_ADDITIONS', 'source_commit': args.source_commit,
          'parent_manifest_sha256': PARENT_SHA,
          'scope': 'Historical author-only source extension: standard-natural metatheoretic checker comparison; not an internal iPRA proof or paired replay.',
          'order': order, 'sources': rows, 'axiom_reports': reports}
out = D / 'external-author-additions.json'
if out.exists() or out.is_symlink():
    raise ValueError('refusing to overwrite frozen manifest')
out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
print('EXTERNAL_CHECKER_FROZEN_MANIFEST', hashlib.sha256(out.read_bytes()).hexdigest(),
      len(order), 'modules', sum(map(len, reports.values())), 'reports',
      sum((ROOT / x['workspace_path']).stat().st_size for x in rows.values()), 'source bytes')
