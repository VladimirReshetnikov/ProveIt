#!/usr/bin/env python3
"""Review Fin24 endpoint adaptation, current bridge and guarded provider routes."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root/'research'
packet = research/'nine-sharing-sign24-endpoint-memory-check'
draft = research/'nine-sharing-sign24-endpoint-memory-draft'
prior = research/'nine-sharing-sign25-endpoint-memory-retry-check'
bridge = research/'nine-sharing-sign24-concrete-bridge-memory-retry-check'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = packet/'source-manifest.json'
assert digest(manifest) == '5b817535ec860c794c84fe479283ddf7fa3bc01edae34ddf56be70ac9bf5c793'
rows = json.loads(manifest.read_text())['rows']
names = ['Sign24DirectNoAliasNative','Sign24DirectNoAliasStandard','Sign24DirectNoAliasTranslated']
assert [r['module'] for r in rows] == ['DiophantineConsistency.'+n for n in names]
for row,name in zip(rows,names):
    src = packet/'src/DiophantineConsistency'/(name+'.lean')
    old = prior/'src/DiophantineConsistency'/(name.replace('Sign24','Sign25')+'.lean')
    assert digest(src) == digest(draft/(name+'.lean')) == row['source_sha256']
    assert src.read_text() == old.read_text().replace('Sign25','Sign24').replace('SharingSeed25Octic','SharingSeed24Octic')
    assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M) == row['imports']
assert rows[0]['imports'] == ['DiophantineConsistency.Sign24DirectPolynomialBridge','DiophantineConsistency.IPRAExpressionNative']
assert rows[1]['imports'] == ['DiophantineConsistency.Sign24DirectNoAliasNative','DiophantineConsistency.IPRAStandardTheory']
assert rows[2]['imports'] == ['DiophantineConsistency.Sign24DirectNoAliasStandard']
state = json.loads((bridge/'attempt01/state.json').read_text())
outer = json.loads((bridge/'attempt01/outer-result.json').read_text())
assert state['status'] == 'PASS' and outer['outer_exit_code'] == 0 and state['rows'][0]['object_sha256'] == '7f868da1803547aaca112e044ec2f0ca8351599f0dbfe472b9a6ffc88621fe63'
audit = root/'reviews/nine-sharing-sign24-concrete-bridge-memory-retry-terminal-independent/check.py'
assert digest(audit) == 'c8854f8e0ebf1e998192738f75119fbc1796b114a4f7fab96279d88686a04d87'
subprocess.run([sys.executable,'-I','-S','-B',str(audit)],check=True,capture_output=True,timeout=120)
survey = packet/'framework-survey.py'
assert digest(survey) == 'e76b7ad869ccd5f86efdcfe14ca26ffa720bd248ecd97fcea127b778cecb4096'
old_survey = (prior/'framework-survey.py').read_text()
assert survey.read_text() == old_survey.replace('/tmp/nine-sharing-sign25-concrete-polynomial-bridge-check-20261106','/tmp/nine-sharing-sign24-concrete-bridge-memory-retry-20261109')
runner = packet/'run.py'
assert digest(runner) == 'ce11dd6e670f86bd96b5b817cb242e166a9abbf3974169f344ca12fb1e1e02a8'
r = runner.read_text()
assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
assert 'shutil.disk_usage(\'/tmp\').free>=5_000_000_000' in r
assert "if local=='Sign24DirectPolynomialBridge':expected_hash=base['rows'][0]['object_sha256']" in r
assert "outer-result.json')=='8cd9eac76f5a3b196511327079ba1e3a2b2d8ec23769b242cd693fc867c106d8'" in r
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':digest(runner),'stages':3,
                  'scope':'adapted native, standard and translated symbolic Fin24 endpoint candidates; no Lean result'},sort_keys=True,indent=2))
