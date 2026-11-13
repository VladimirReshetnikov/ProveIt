#!/usr/bin/env python3
"""Review scoped Lean interpreter-limit retry and unchanged hard controls."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root/'research'
packet = research/'nine-sharing-sign25-endpoint-memory-retry-check'
prior = research/'nine-sharing-sign25-endpoint-no-alias-retry-check'
draft = research/'nine-sharing-sign25-endpoint-memory-retry-draft'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = packet/'source-manifest.json'
old_manifest = prior/'source-manifest.json'
assert digest(manifest) == '1903addd6116b80b8b92e2ac04730e8abae76db7d5dea82b397695e456539f65'
rows = json.loads(manifest.read_text())['rows']
old_rows = json.loads(old_manifest.read_text())['rows']
assert len(rows) == len(old_rows) == 3
for row,old in zip(rows,old_rows):
    assert {k:v for k,v in row.items() if k != 'source'} == {k:v for k,v in old.items() if k != 'source'}
    name = row['module'].split('.')[-1]
    src = packet/'src/DiophantineConsistency'/(name+'.lean')
    assert digest(src) == digest(draft/(name+'.lean')) == digest(prior/'src/DiophantineConsistency'/(name+'.lean')) == row['source_sha256']
expected = (prior/'run.py').read_text()
replacements = [('/tmp/nine-sharing-sign25-endpoint-no-alias-retry-20261109','/tmp/nine-sharing-sign25-endpoint-memory-retry-20261109'),
                (digest(old_manifest),digest(manifest)),
                ('Bounded sign25 no-alias opacity retry','Bounded sign25 memory-limit endpoint retry'),
                ("'-M2800'","'-M3600'"),('PASS sign25 no-alias opacity retry','PASS sign25 memory-limit endpoint retry')]
for old,new in replacements:
    assert expected.count(old) == 1
    expected = expected.replace(old,new)
runner = packet/'run.py'
assert expected == runner.read_text()
assert digest(runner) == '5848492b06b89bac0dffde190ab20481738fb1a1c6c0da617b2cfeb6ca1d3e22'
assert "rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1" in expected
assert "shutil.disk_usage('/tmp').free>=5_000_000_000" in expected
assert "LEAN_NUM_THREADS='1'" in expected and "'-j1'" in expected
evidence = {}
for name in ('nine-sharing-sign25-endpoint-no-alias-retry-check','nine-sharing-sign25-endpoint-wrappers-check',
             'nine-sharing-sign25-endpoint-transfer-check','nine-sharing-sign25-typed-sentence-check'):
    path = research/name/'attempt01/state.json'
    state = json.loads(path.read_text())
    assert state['status'] == 'FAILED'
    failed = [r for r in state['rows'] if r.get('compile',{}).get('exit') == -6]
    assert len(failed) == 1
    row, = failed
    log = research/name/'attempt01'/(row['module']+'-compile.txt')
    assert 'memory_exception' in log.read_text() and "'interpreter'" in log.read_text()
    evidence[name] = {'state_sha256':digest(path),'peak_sampled_rss':row['compile']['peak_session_rss_bytes']}
upstream = root/'reviews/nine-sharing-sign25-concrete-polynomial-bridge-terminal-frontier-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(packet/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':digest(runner),'memory_change':'-M2800 to -M3600',
                  'other_runner_changes':'fresh output, manifest and scope labels only', 'failure_evidence':evidence,
                  'scope':'scoped interpreter retry; sampled 4 GiB RSS cap unchanged'},sort_keys=True,indent=2))
