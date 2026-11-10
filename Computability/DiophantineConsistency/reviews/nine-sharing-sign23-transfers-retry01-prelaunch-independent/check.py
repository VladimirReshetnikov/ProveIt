#!/usr/bin/env python3
"""Review map_ofNat transfer retry and unchanged provider/resource guard."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root/'research'
packet = research/'nine-sharing-sign23-transfers-retry01'
prior = research/'nine-sharing-sign23-transfers-check'
draft = research/'nine-sharing-sign23-transfers-retry-draft'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
rows = json.loads((packet/'source-manifest.json').read_text())['rows']
names = ['Sign23Transfers00','Sign23Transfers01']
assert [r['module'] for r in rows] == ['DiophantineConsistency.'+n for n in names]
count = 0
for row,name in zip(rows,names):
    src = packet/'src/DiophantineConsistency'/(name+'.lean')
    original = (prior/'src/DiophantineConsistency'/(name+'.lean')).read_text()
    needle = 'Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul]'
    assert original.count(needle) == 7
    count += original.count(needle)
    assert src.read_text() == original.replace(needle,needle[:-1]+', map_ofNat]')
    assert digest(src) == digest(draft/(name+'.lean')) == row['source_sha256']
    assert row['imports'] == ['DiophantineConsistency.Sign23Coordinate']
assert count == 14
expected = (prior/'run.py').read_text()
for old,new in [('/tmp/nine-sharing-sign23-transfers-check-20261109','/tmp/nine-sharing-sign23-transfers-retry01-20261109'),
                (digest(prior/'source-manifest.json'),digest(packet/'source-manifest.json')),
                ('Bounded sign23 residual transfer diagnostic','Bounded sign23 residual transfer numeral-rewrite retry'),
                ('PASS sign23 residual transfer diagnostic','PASS sign23 residual transfer numeral-rewrite retry')]:
    assert expected.count(old) == 1
    expected = expected.replace(old,new)
assert expected == (packet/'run.py').read_text()
assert "'-M2800'" in expected and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in expected
upstream = root/'reviews/nine-sharing-sign23-transfers-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(packet/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','map_ofNat_additions':count,'runner_sha256':digest(packet/'run.py'),
                  'scope':'source-only numeral-rewrite retry; prior failure included sorryAx'},sort_keys=True,indent=2))
