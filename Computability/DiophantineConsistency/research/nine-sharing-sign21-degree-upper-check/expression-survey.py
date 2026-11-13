#!/usr/bin/env python3
"""Bind current-expression definition to the checked four-stage producer."""
import hashlib
import json
import os
from pathlib import Path

P = Path(__file__).resolve().parent
D = P.parents[1]
BASE = Path('/tmp/nine-sharing-sign21-concrete-polynomial-bridge-check-20261109')
PRODUCER = Path('/tmp/nine-sharing-sign21-expression-eval-check-20261109')
STATE = D / 'research/nine-sharing-sign21-expression-eval-check/attempt01/state.json'
def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
assert sha(STATE) == 'a5e897bfc36ba9c7773389c52c658704b085c0932b342d1fa5f8816acf56ed72'
outer = D / 'research/nine-sharing-sign21-expression-eval-check/attempt01/outer-result.json'
audit = D / 'reviews/nine-sharing-sign21-expression-eval-terminal-independent/check.py'
assert sha(outer) == '9d5b347db282ce1fccb102d49f1ce00c4bd10c08cd1759a6a10c6c8427038c83'
assert json.loads(outer.read_text())['author_observed_numeric_outer_exit'] == 0
assert sha(audit) == '71a072d25fb84568cc7b26cca3f0bb62d060cb21eed5b3904b676b9d06ff3a65'
s = json.loads(STATE.read_text())
assert s['status'] == 'PASS' and len(s['rows']) == 4
row, = [r for r in s['rows'] if r['module'] == 'Sign21CurrentExpressionDef']
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
