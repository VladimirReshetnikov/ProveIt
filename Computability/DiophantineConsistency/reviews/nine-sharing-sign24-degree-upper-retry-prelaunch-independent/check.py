#!/usr/bin/env python3
"""Review theorem-local heartbeat retry following concrete rfl timeout."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root/'research'
packet = research/'nine-sharing-sign24-degree-upper-retry-check'
prior = research/'nine-sharing-sign24-degree-upper-check'
draft = research/'nine-sharing-sign24-degree-upper-retry-draft'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
names = ['Sign24SyntaxDegree','Sign24DegreeUpper']
rows = json.loads((packet/'source-manifest.json').read_text())['rows']
assert [r['module'] for r in rows] == ['DiophantineConsistency.'+n for n in names]
for row,name in zip(rows,names):
    src = packet/'src/DiophantineConsistency'/(name+'.lean')
    assert digest(src) == digest(draft/(name+'.lean')) == row['source_sha256']
    old = (prior/'src/DiophantineConsistency'/(name+'.lean')).read_text()
    if name == names[1]:
        needle = 'theorem expression_syntax_degree (p : Fin 4 → ℤ) :'
        assert old.count(needle) == 1
        old = old.replace(needle,'set_option maxHeartbeats 4000000 in\n'+needle)
    assert src.read_text() == old
assert (packet/'src/DiophantineConsistency/Sign24DegreeUpper.lean').read_text().count('set_option maxHeartbeats 4000000 in') == 1
expected = (prior/'run.py').read_text()
for old,new in [('/tmp/nine-sharing-sign24-degree-upper-20261109','/tmp/nine-sharing-sign24-degree-upper-retry-20261109'),
                (digest(prior/'source-manifest.json'),digest(packet/'source-manifest.json')),
                ('Bounded sign24 degree upper-bound attempt','Bounded sign24 degree upper-bound local-heartbeat retry'),
                ('PASS sign24 degree upper-bound attempt','PASS sign24 degree upper-bound local-heartbeat retry')]:
    assert expected.count(old) == 1
    expected = expected.replace(old,new)
runner = packet/'run.py'
assert expected == runner.read_text()
assert digest(runner) == '3911f7d573d16dac620bf19193379a8d232e224862d7a58a370655a026063a85'
assert "'-M3600'" in expected and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in expected
assert digest(packet/'expression-survey.py') == digest(prior/'expression-survey.py')
upstream = root/'reviews/nine-sharing-sign24-degree-upper-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':digest(runner),'heartbeat_change':'4000000 local to syntax-degree theorem',
                  'scope':'candidate degree upper bound; prior concrete timeout and sorryAx not credited'},sort_keys=True,indent=2))
