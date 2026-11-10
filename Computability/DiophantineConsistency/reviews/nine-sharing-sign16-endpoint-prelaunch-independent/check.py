#!/usr/bin/env python3
"""Review Fin16 endpoint adaptation, current bridge and guarded provider routes."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root/'research'
packet = research/'nine-sharing-sign16-endpoint-check'
draft = research/'nine-sharing-sign16-endpoint-draft'
prior = research/'nine-sharing-sign17-endpoint-check'
bridge = research/'nine-sharing-sign16-concrete-polynomial-bridge-check'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = packet/'source-manifest.json'
assert digest(manifest) == '7dfe7062af77e621f3b54ff09f220259f34b3a660964216e1068f56293f337ba'
rows = json.loads(manifest.read_text())['rows']
names = ['Sign16DirectNoAliasNative','Sign16DirectNoAliasStandard','Sign16DirectNoAliasTranslated']
assert [r['module'] for r in rows] == ['DiophantineConsistency.'+n for n in names]
for row,name in zip(rows,names):
    src = packet/'src/DiophantineConsistency'/(name+'.lean')
    old = prior/'src/DiophantineConsistency'/(name.replace('Sign16','Sign17')+'.lean')
    assert digest(src) == digest(draft/(name+'.lean')) == row['source_sha256']
    assert src.read_text() == old.read_text().replace('Sign17','Sign16').replace('SharingSeed17Degree96','SharingSeed16Degree112')
    assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M) == row['imports']
assert rows[0]['imports'] == ['DiophantineConsistency.Sign16DirectPolynomialBridge','DiophantineConsistency.IPRAExpressionNative']
assert rows[1]['imports'] == ['DiophantineConsistency.Sign16DirectNoAliasNative','DiophantineConsistency.IPRAStandardTheory']
assert rows[2]['imports'] == ['DiophantineConsistency.Sign16DirectNoAliasStandard']
state = json.loads((bridge/'attempt01/state.json').read_text())
outer = json.loads((bridge/'attempt01/outer-result.json').read_text())
assert state['status'] == 'PASS' and outer['author_observed_numeric_outer_exit'] == 0 and state['rows'][0]['object_sha256'] == '267cb36d950cd00e3a6ceafc7df400b17b5e315375f17fe4477eeef008d8ec69'
audit = root/'reviews/nine-sharing-sign16-concrete-polynomial-bridge-terminal-independent/check.py'
assert digest(audit) == 'c7a00af0912e05e356cd24a4ac8b34ebe8078943f7900176b5885e1955092f3d'
subprocess.run([sys.executable,'-I','-S','-B',str(audit)],check=True,capture_output=True,timeout=120)
survey = packet/'framework-survey.py'
assert digest(survey) == 'c2148b1b5de6ff36bcaadecf2a4bcc5ce01494c3820ff26926f2e0b3a5fee3ff'
old_survey = (prior/'framework-survey.py').read_text()
assert survey.read_text() == old_survey.replace('/tmp/nine-sharing-sign17-concrete-polynomial-bridge-check-20261109','/tmp/nine-sharing-sign16-concrete-polynomial-bridge-check-20261110')
runner = packet/'run.py'
assert digest(runner) == 'bc56edfca0e7d7743ecc5f12b1b9606989b5cf90d90f11bab2430d354d618a3a'
r = runner.read_text()
assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
assert 'shutil.disk_usage(\'/tmp\').free>=5_000_000_000' in r
assert "if local=='Sign16DirectPolynomialBridge':expected_hash=base['rows'][0]['object_sha256']" in r
assert "outer-result.json')=='d19bea7ccb72d587fc70b5d88b94631b8fee1a43d267645e2da62aa04ca1f9ad'" in r
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':digest(runner),'stages':3,
                  'scope':'adapted native, standard and translated symbolic Fin17 endpoint candidates; no Lean result'},sort_keys=True,indent=2))
