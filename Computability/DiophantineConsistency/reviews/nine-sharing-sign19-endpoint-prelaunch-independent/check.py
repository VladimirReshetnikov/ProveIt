#!/usr/bin/env python3
"""Review Fin20 endpoint adaptation, current bridge and guarded provider routes."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root/'research'
packet = research/'nine-sharing-sign19-endpoint-check'
draft = research/'nine-sharing-sign19-endpoint-draft'
prior = research/'nine-sharing-sign20-endpoint-check'
bridge = research/'nine-sharing-sign19-concrete-polynomial-bridge-check'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = packet/'source-manifest.json'
assert digest(manifest) == '1fe53147129b5bdc6e0debb9ed0d2719679741ee27b14c7a79fa68701c606c12'
rows = json.loads(manifest.read_text())['rows']
names = ['Sign19DirectNoAliasNative','Sign19DirectNoAliasStandard','Sign19DirectNoAliasTranslated']
assert [r['module'] for r in rows] == ['DiophantineConsistency.'+n for n in names]
for row,name in zip(rows,names):
    src = packet/'src/DiophantineConsistency'/(name+'.lean')
    old = prior/'src/DiophantineConsistency'/(name.replace('Sign19','Sign20')+'.lean')
    assert digest(src) == digest(draft/(name+'.lean')) == row['source_sha256']
    assert src.read_text() == old.read_text().replace('Sign20','Sign19').replace('SharingSeed20Degree20','SharingSeed19Degree44')
    assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M) == row['imports']
assert rows[0]['imports'] == ['DiophantineConsistency.Sign19DirectPolynomialBridge','DiophantineConsistency.IPRAExpressionNative']
assert rows[1]['imports'] == ['DiophantineConsistency.Sign19DirectNoAliasNative','DiophantineConsistency.IPRAStandardTheory']
assert rows[2]['imports'] == ['DiophantineConsistency.Sign19DirectNoAliasStandard']
state = json.loads((bridge/'attempt01/state.json').read_text())
outer = json.loads((bridge/'attempt01/outer-result.json').read_text())
assert state['status'] == 'PASS' and outer['author_observed_numeric_outer_exit'] == 0 and state['rows'][0]['object_sha256'] == '7b13196fe2a4c6b7e2cb1f6dc1820f05c889354f1a34d8ab79baff462c87a99a'
audit = root/'reviews/nine-sharing-sign19-concrete-polynomial-bridge-terminal-independent/check.py'
assert digest(audit) == '77d01c4e7e05e8e19eac8b43501353f6b3e3c27a41abc5115088562b34ef8dbf'
subprocess.run([sys.executable,'-I','-S','-B',str(audit)],check=True,capture_output=True,timeout=120)
survey = packet/'framework-survey.py'
assert digest(survey) == 'e98d21b6a02ce38775143419d28624ad50fe955b29e0cb30389cae92d0ba04b9'
old_survey = (prior/'framework-survey.py').read_text()
assert survey.read_text() == old_survey.replace('/tmp/nine-sharing-sign20-concrete-polynomial-bridge-check-20261109','/tmp/nine-sharing-sign19-concrete-polynomial-bridge-check-20261109')
runner = packet/'run.py'
assert digest(runner) == 'b3ec490b2d98f466fcc2c28df8ef57acf3a38e415ed553c574e51454e175b0ee'
r = runner.read_text()
assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
assert 'shutil.disk_usage(\'/tmp\').free>=5_000_000_000' in r
assert "if local=='Sign19DirectPolynomialBridge':expected_hash=base['rows'][0]['object_sha256']" in r
assert "outer-result.json')=='5b0d81da50a6f3583161cf73ab9b459b341963aced49a285d83394c1584288fc'" in r
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':digest(runner),'stages':3,
                  'scope':'adapted native, standard and translated symbolic Fin19 endpoint candidates; no Lean result'},sort_keys=True,indent=2))
