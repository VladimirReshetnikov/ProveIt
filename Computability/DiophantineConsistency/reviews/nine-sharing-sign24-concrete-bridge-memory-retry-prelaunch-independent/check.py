#!/usr/bin/env python3
"""Review scoped sign24 Lean interpreter-limit retry and unchanged controls."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root/'research'
packet = research/'nine-sharing-sign24-concrete-bridge-memory-retry-check'
prior = research/'nine-sharing-sign24-concrete-polynomial-bridge-check'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert digest(packet/'source-manifest.json') == digest(prior/'source-manifest.json') == '0a6775382f22779bf38bd541909192f941e57ec95c07b39f2522c461f7d5b9f9'
entry, = json.loads((packet/'source-manifest.json').read_text())['rows']
name = 'Sign24DirectPolynomialBridge'
assert entry['module'] == 'DiophantineConsistency.'+name
src = packet/'src/DiophantineConsistency'/(name+'.lean')
assert digest(src) == digest(prior/'src/DiophantineConsistency'/(name+'.lean')) == entry['source_sha256']
assert digest(packet/'provider-union-survey.py') == digest(prior/'provider-union-survey.py')
assert digest(packet/'union.json') == digest(prior/'union.json')
expected = (prior/'run.py').read_text()
for old,new in [('/tmp/nine-sharing-sign24-concrete-polynomial-bridge-check-20261109','/tmp/nine-sharing-sign24-concrete-bridge-memory-retry-20261109'),
                ('Bounded sign25 concrete polynomial bridge diagnostic','Bounded sign24 concrete bridge memory retry'),
                ("'-M2800'","'-M3600'")]:
    assert expected.count(old) == 1
    expected = expected.replace(old,new)
runner = packet/'run.py'
assert expected == runner.read_text()
assert digest(runner) == 'b35611bbc283834f6c0ab17338385a1bc31ff30d30ae5609ab382b489df443a4'
assert "rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1" in expected
assert "shutil.disk_usage('/tmp').free>=5_000_000_000" in expected and "'-j1'" in expected
failures = {}
for packet_name in ('nine-sharing-sign24-concrete-polynomial-bridge-check','nine-sharing-sign24-polynomial-bridge-staged-check','nine-sharing-sign24-polynomial-bridge-bypass-check'):
    p = research/packet_name/'attempt01/state.json'
    state = json.loads(p.read_text())
    failed = [r for r in state['rows'] if r.get('compile',{}).get('exit') == -6]
    assert state['status'] == 'FAILED' and len(failed) == 1
    row, = failed
    log = research/packet_name/'attempt01'/(row['module']+'-compile.txt')
    assert 'memory_exception' in log.read_text() and "'interpreter'" in log.read_text()
    failures[packet_name] = {'state_sha256':digest(p),'peak_sampled_rss':row['compile']['peak_session_rss_bytes']}
upstream = root/'reviews/nine-sharing-sign25-endpoint-memory-retry-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':digest(runner),'failures':failures,
                  'memory_change':'-M2800 to -M3600; sampled RSS and all other controls unchanged',
                  'scope':'scoped bridge retry only; no Lean theorem'},sort_keys=True,indent=2))
