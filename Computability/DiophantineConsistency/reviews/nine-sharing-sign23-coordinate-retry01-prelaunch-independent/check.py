#!/usr/bin/env python3
"""Review sole numeral-rewrite retry and preserved guard controls."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root/'research'
packet = research/'nine-sharing-sign23-coordinate-retry01'
prior = research/'nine-sharing-sign23-coordinate-check'
draft = research/'nine-sharing-sign23-coordinate-retry-draft'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
src = packet/'src/DiophantineConsistency/Sign23Coordinate.lean'
old = (prior/'src/DiophantineConsistency/Sign23Coordinate.lean').read_text()
needle = 'Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul]'
assert old.count(needle) == 1
assert src.read_text() == old.replace(needle,needle[:-1]+', map_ofNat]')
entry, = json.loads((packet/'source-manifest.json').read_text())['rows']
assert digest(src) == digest(draft/'Sign23Coordinate.lean') == entry['source_sha256']
assert entry['imports'] == ['DiophantineConsistency.SharingSign23Squares','DiophantineConsistency.SharingSign24Squares']
assert digest(packet/'sign24-survey.py') == digest(prior/'sign24-survey.py')
expected = (prior/'run.py').read_text()
for old,new in [('/tmp/nine-sharing-sign23-coordinate-check-20261109','/tmp/nine-sharing-sign23-coordinate-retry01-20261109'),
                (digest(prior/'source-manifest.json'),digest(packet/'source-manifest.json')),
                ('Bounded sign23 coordinate diagnostic','Bounded sign23 coordinate numeral-rewrite retry'),
                ('PASS sign23 coordinate diagnostic','PASS sign23 coordinate numeral-rewrite retry')]:
    assert expected.count(old) == 1
    expected = expected.replace(old,new)
assert expected == (packet/'run.py').read_text()
assert "'-M2800'" in expected and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in expected
upstream = root/'reviews/nine-sharing-sign23-coordinate-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(packet/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','source_sha256':digest(src),'runner_sha256':digest(packet/'run.py'),
                  'scope':'sole map_ofNat simp addition; no compiled theorem'},sort_keys=True,indent=2))
