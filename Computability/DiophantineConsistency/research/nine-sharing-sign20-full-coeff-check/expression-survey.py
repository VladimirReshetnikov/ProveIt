#!/usr/bin/env python3
"""Bind current-expression definition to the checked four-stage producer."""
import hashlib
import json
import os
from pathlib import Path

P = Path(__file__).resolve().parent
D = P.parents[1]
BASE = Path('/tmp/nine-sharing-sign20-concrete-polynomial-bridge-check-20261109')
PRODUCER = Path('/tmp/nine-sharing-sign20-expression-eval-check-20261109')
STATE = D / 'research/nine-sharing-sign20-expression-eval-check/attempt01/state.json'
def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
assert sha(STATE) == 'b5a78477b7d4713fd24111c2e2f5d8a43840dd01ca40fbdddde2824c6313d47b'
outer = D / 'research/nine-sharing-sign20-expression-eval-check/attempt01/outer-result.json'
audit = D / 'reviews/nine-sharing-sign20-expression-eval-terminal-independent/check.py'
assert sha(outer) == '65fcd8c43f349184c48daf2208f5fe19b8cde4a976d3ddea12671a1b5016a0ee'
assert json.loads(outer.read_text())['author_observed_numeric_outer_exit'] == 0
assert sha(audit) == '8ee393adf3d5c0afa0c929fe1b5787325f080a4a356d2ef7ff9d1659401e8261'
s = json.loads(STATE.read_text())
assert s['status'] == 'PASS' and len(s['rows']) == 4
row, = [r for r in s['rows'] if r['module'] == 'Sign20CurrentExpressionDef']
name = row['module']
assert row['deps']['exit'] == row['compile']['exit'] == 0
assert sha(PRODUCER/'src/DiophantineConsistency'/(name+'.lean')) == row['source_sha256']
obj = PRODUCER/'lib/DiophantineConsistency'/(name+'.olean')
assert sha(obj) == row['object_sha256']
for key in ('deps', 'compile'):
    assert sha(PRODUCER/(name+'-'+key+'.txt')) == row[key]['log_sha256']
for path, rec in row['direct_guard'].items():
    p = Path(path)
    if rec is None: assert not os.path.lexists(p)
    else: assert p.is_file() and str(p.resolve()) == rec['realpath'] and sha(p) == rec['sha256']
for path, dest in s['overlay_links'].items():
    assert Path(path).is_symlink() and str(Path(path).resolve()) == dest
current = BASE/'lib/DiophantineConsistency'/(name+'.olean')
assert current.is_file() and current.resolve() == obj.resolve() and sha(current) == row['object_sha256']
print(json.dumps({'status':'PASS', 'object_sha256':row['object_sha256'],
                  'realpath':str(obj.resolve()), 'scope':'direct producer point observations; ancestry inherited'}, sort_keys=True))
