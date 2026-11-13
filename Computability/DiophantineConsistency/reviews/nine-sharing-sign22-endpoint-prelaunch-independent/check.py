#!/usr/bin/env python3
"""Review Fin22 endpoint adaptation, current bridge and guarded provider routes."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root/'research'
packet = research/'nine-sharing-sign22-endpoint-check'
draft = research/'nine-sharing-sign22-endpoint-draft'
prior = research/'nine-sharing-sign23-endpoint-check'
bridge = research/'nine-sharing-sign22-concrete-polynomial-bridge-check'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = packet/'source-manifest.json'
assert digest(manifest) == '309dcb72ff0d767e0be2521ed5a7d88e58ce137449e603f15dca1a06f56e5200'
rows = json.loads(manifest.read_text())['rows']
names = ['Sign22DirectNoAliasNative','Sign22DirectNoAliasStandard','Sign22DirectNoAliasTranslated']
assert [r['module'] for r in rows] == ['DiophantineConsistency.'+n for n in names]
for row,name in zip(rows,names):
    src = packet/'src/DiophantineConsistency'/(name+'.lean')
    old = prior/'src/DiophantineConsistency'/(name.replace('Sign22','Sign23')+'.lean')
    assert digest(src) == digest(draft/(name+'.lean')) == row['source_sha256']
    assert src.read_text() == old.read_text().replace('Sign23','Sign22').replace('SharingSeed23Octic','SharingSeed22Dodecic')
    assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M) == row['imports']
assert rows[0]['imports'] == ['DiophantineConsistency.Sign22DirectPolynomialBridge','DiophantineConsistency.IPRAExpressionNative']
assert rows[1]['imports'] == ['DiophantineConsistency.Sign22DirectNoAliasNative','DiophantineConsistency.IPRAStandardTheory']
assert rows[2]['imports'] == ['DiophantineConsistency.Sign22DirectNoAliasStandard']
state = json.loads((bridge/'attempt01/state.json').read_text())
outer = json.loads((bridge/'attempt01/outer-result.json').read_text())
assert state['status'] == 'PASS' and outer['author_observed_numeric_outer_exit'] == 0 and state['rows'][0]['object_sha256'] == '53e98c8448caeebd9564037973e0ecd88be1793abd03f321d4d161f0651c7934'
audit = root/'reviews/nine-sharing-sign22-concrete-polynomial-bridge-terminal-independent/check.py'
assert digest(audit) == 'fb534290e96ce030b25f62fbb67fbf0b03381431372543bb6748fecaa638c682'
subprocess.run([sys.executable,'-I','-S','-B',str(audit)],check=True,capture_output=True,timeout=120)
survey = packet/'framework-survey.py'
assert digest(survey) == 'bd0a23fb642365f6ef15a5b0dac263ec81ae85eca86515fde44cfecfc39276d4'
old_survey = (prior/'framework-survey.py').read_text()
assert survey.read_text() == old_survey.replace('/tmp/nine-sharing-sign23-concrete-polynomial-bridge-check-20261109','/tmp/nine-sharing-sign22-concrete-polynomial-bridge-check-20261109')
runner = packet/'run.py'
assert digest(runner) == '1e346805c189363cde3eccf70f0c5ec00cb97551ca1f68eecabc9a78d50ba1ba'
r = runner.read_text()
assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
assert 'shutil.disk_usage(\'/tmp\').free>=5_000_000_000' in r
assert "if local=='Sign22DirectPolynomialBridge':expected_hash=base['rows'][0]['object_sha256']" in r
assert "outer-result.json')=='0998d6d47a9f6c08a87b4cbc2bed224568a9f3debe0ba71578c2de3c651b4482'" in r
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':digest(runner),'stages':3,
                  'scope':'adapted native, standard and translated symbolic Fin22 endpoint candidates; no Lean result'},sort_keys=True,indent=2))
