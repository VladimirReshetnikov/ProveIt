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
packet = research/'nine-sharing-sign17-endpoint-check'
draft = research/'nine-sharing-sign17-endpoint-draft'
prior = research/'nine-sharing-sign18-endpoint-check'
bridge = research/'nine-sharing-sign17-concrete-polynomial-bridge-check'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = packet/'source-manifest.json'
assert digest(manifest) == 'd351aefa1f9557a711e3406860945dc1443757c08b5dbd2ce2dec552c1248715'
rows = json.loads(manifest.read_text())['rows']
names = ['Sign17DirectNoAliasNative','Sign17DirectNoAliasStandard','Sign17DirectNoAliasTranslated']
assert [r['module'] for r in rows] == ['DiophantineConsistency.'+n for n in names]
for row,name in zip(rows,names):
    src = packet/'src/DiophantineConsistency'/(name+'.lean')
    old = prior/'src/DiophantineConsistency'/(name.replace('Sign17','Sign18')+'.lean')
    assert digest(src) == digest(draft/(name+'.lean')) == row['source_sha256']
    assert src.read_text() == old.read_text().replace('Sign18','Sign17').replace('SharingSeed18Degree94','SharingSeed17Degree96')
    assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M) == row['imports']
assert rows[0]['imports'] == ['DiophantineConsistency.Sign17DirectPolynomialBridge','DiophantineConsistency.IPRAExpressionNative']
assert rows[1]['imports'] == ['DiophantineConsistency.Sign17DirectNoAliasNative','DiophantineConsistency.IPRAStandardTheory']
assert rows[2]['imports'] == ['DiophantineConsistency.Sign17DirectNoAliasStandard']
state = json.loads((bridge/'attempt01/state.json').read_text())
outer = json.loads((bridge/'attempt01/outer-result.json').read_text())
assert state['status'] == 'PASS' and outer['author_observed_numeric_outer_exit'] == 0 and state['rows'][0]['object_sha256'] == 'd161a98d5e26dcc66cbe035f2f744b7aa85c26f395ea6e8909455605ea591621'
audit = root/'reviews/nine-sharing-sign17-concrete-polynomial-bridge-terminal-independent/check.py'
assert digest(audit) == '44d70aab47ce1f22e486d6c0a16fb4ab43e7329333c4bee2e9a88f1f0487b5fd'
subprocess.run([sys.executable,'-I','-S','-B',str(audit)],check=True,capture_output=True,timeout=120)
survey = packet/'framework-survey.py'
assert digest(survey) == '6cdbecf197adcc45f37e00eaca6df0c92bca3596938a2d49798cfd18e38fc0e6'
old_survey = (prior/'framework-survey.py').read_text()
assert survey.read_text() == old_survey.replace('/tmp/nine-sharing-sign18-concrete-polynomial-bridge-check-20261109','/tmp/nine-sharing-sign17-concrete-polynomial-bridge-check-20261109')
runner = packet/'run.py'
assert digest(runner) == '8f54edd416f93adf12310566bda3c9d02a6b0f9ec0d35bb07434a563f8806ea5'
r = runner.read_text()
assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
assert 'shutil.disk_usage(\'/tmp\').free>=5_000_000_000' in r
assert "if local=='Sign17DirectPolynomialBridge':expected_hash=base['rows'][0]['object_sha256']" in r
assert "outer-result.json')=='35654ec0f7467b708b1fe6c9b5a391be382be83e919b393688ea441f0399cfe2'" in r
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':digest(runner),'stages':3,
                  'scope':'adapted native, standard and translated symbolic Fin17 endpoint candidates; no Lean result'},sort_keys=True,indent=2))
