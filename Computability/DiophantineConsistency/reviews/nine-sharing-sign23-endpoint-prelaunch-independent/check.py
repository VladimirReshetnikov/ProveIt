#!/usr/bin/env python3
"""Review Fin23 endpoint adaptation, current bridge and guarded provider routes."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root/'research'
packet = research/'nine-sharing-sign23-endpoint-check'
draft = research/'nine-sharing-sign23-endpoint-draft'
prior = research/'nine-sharing-sign24-endpoint-memory-check'
bridge = research/'nine-sharing-sign23-concrete-polynomial-bridge-check'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = packet/'source-manifest.json'
assert digest(manifest) == '1a79ce4431773050aa667daab1458d92b55917a81f7dfe8366f07ee2fe6247f7'
rows = json.loads(manifest.read_text())['rows']
names = ['Sign23DirectNoAliasNative','Sign23DirectNoAliasStandard','Sign23DirectNoAliasTranslated']
assert [r['module'] for r in rows] == ['DiophantineConsistency.'+n for n in names]
for row,name in zip(rows,names):
    src = packet/'src/DiophantineConsistency'/(name+'.lean')
    old = prior/'src/DiophantineConsistency'/(name.replace('Sign23','Sign24')+'.lean')
    assert digest(src) == digest(draft/(name+'.lean')) == row['source_sha256']
    assert src.read_text() == old.read_text().replace('Sign24','Sign23').replace('SharingSeed24Octic','SharingSeed23Octic')
    assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M) == row['imports']
assert rows[0]['imports'] == ['DiophantineConsistency.Sign23DirectPolynomialBridge','DiophantineConsistency.IPRAExpressionNative']
assert rows[1]['imports'] == ['DiophantineConsistency.Sign23DirectNoAliasNative','DiophantineConsistency.IPRAStandardTheory']
assert rows[2]['imports'] == ['DiophantineConsistency.Sign23DirectNoAliasStandard']
state = json.loads((bridge/'attempt01/state.json').read_text())
outer = json.loads((bridge/'attempt01/outer-result.json').read_text())
assert state['status'] == 'PASS' and outer['author_observed_numeric_outer_exit'] == 0 and state['rows'][0]['object_sha256'] == '2cb1f6c016b2d608ecc59ff59c9d88be2ab5a19d76a65d4c98c9f1ed76360c71'
audit = root/'reviews/nine-sharing-sign23-concrete-polynomial-bridge-terminal-independent/check.py'
assert digest(audit) == '4b8965bc5acdbb9ead4bf8bd13fadc0d49a1f3c220b24a75e9af3aa29e747769'
subprocess.run([sys.executable,'-I','-S','-B',str(audit)],check=True,capture_output=True,timeout=120)
survey = packet/'framework-survey.py'
assert digest(survey) == '77d04a3bb3cfec40baf02321b82c5ffc579c63607a6910d023c550e427436dcd'
old_survey = (prior/'framework-survey.py').read_text()
assert survey.read_text() == old_survey.replace('/tmp/nine-sharing-sign24-concrete-bridge-memory-retry-20261109','/tmp/nine-sharing-sign23-concrete-polynomial-bridge-check-20261109')
runner = packet/'run.py'
assert digest(runner) == '84c52e445558adf15c87cec8582aafd2433032885c1af9d0d2553535c693f226'
r = runner.read_text()
assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
assert 'shutil.disk_usage(\'/tmp\').free>=5_000_000_000' in r
assert "if local=='Sign23DirectPolynomialBridge':expected_hash=base['rows'][0]['object_sha256']" in r
assert "outer-result.json')=='c4cdca9899a028dd242d87302c6975a69453c7f74ed0aa0494dbcf051e237492'" in r
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':digest(runner),'stages':3,
                  'scope':'adapted native, standard and translated symbolic Fin23 endpoint candidates; no Lean result'},sort_keys=True,indent=2))
