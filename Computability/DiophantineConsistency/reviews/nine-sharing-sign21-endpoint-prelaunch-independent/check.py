#!/usr/bin/env python3
"""Review Fin21 endpoint adaptation, current bridge and guarded provider routes."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root/'research'
packet = research/'nine-sharing-sign21-endpoint-check'
draft = research/'nine-sharing-sign21-endpoint-draft'
prior = research/'nine-sharing-sign22-endpoint-check'
bridge = research/'nine-sharing-sign21-concrete-polynomial-bridge-check'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = packet/'source-manifest.json'
assert digest(manifest) == 'd93091286d66e5029cb8c175792c2001348cdbe5bbb87906a75613f1761c4ff0'
rows = json.loads(manifest.read_text())['rows']
names = ['Sign21DirectNoAliasNative','Sign21DirectNoAliasStandard','Sign21DirectNoAliasTranslated']
assert [r['module'] for r in rows] == ['DiophantineConsistency.'+n for n in names]
for row,name in zip(rows,names):
    src = packet/'src/DiophantineConsistency'/(name+'.lean')
    old = prior/'src/DiophantineConsistency'/(name.replace('Sign21','Sign22')+'.lean')
    assert digest(src) == digest(draft/(name+'.lean')) == row['source_sha256']
    assert src.read_text() == old.read_text().replace('Sign22','Sign21').replace('SharingSeed22Dodecic','SharingSeed21Degree14')
    assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M) == row['imports']
assert rows[0]['imports'] == ['DiophantineConsistency.Sign21DirectPolynomialBridge','DiophantineConsistency.IPRAExpressionNative']
assert rows[1]['imports'] == ['DiophantineConsistency.Sign21DirectNoAliasNative','DiophantineConsistency.IPRAStandardTheory']
assert rows[2]['imports'] == ['DiophantineConsistency.Sign21DirectNoAliasStandard']
state = json.loads((bridge/'attempt01/state.json').read_text())
outer = json.loads((bridge/'attempt01/outer-result.json').read_text())
assert state['status'] == 'PASS' and outer['author_observed_numeric_outer_exit'] == 0 and state['rows'][0]['object_sha256'] == 'c3190a00c9d685e68bd12101d48c291e0057e342dbd474d84ce7d5e303579379'
audit = root/'reviews/nine-sharing-sign21-concrete-polynomial-bridge-terminal-independent/check.py'
assert digest(audit) == 'f25640c5d74e8165b4c574054b09332b87c58b03a21f058eff13891ef210279f'
subprocess.run([sys.executable,'-I','-S','-B',str(audit)],check=True,capture_output=True,timeout=120)
survey = packet/'framework-survey.py'
assert digest(survey) == '66ed61302f8cd5deca6812994e17dade30c22f8b339cf354294e7bdc86dcc500'
old_survey = (prior/'framework-survey.py').read_text()
assert survey.read_text() == old_survey.replace('/tmp/nine-sharing-sign22-concrete-polynomial-bridge-check-20261109','/tmp/nine-sharing-sign21-concrete-polynomial-bridge-check-20261109')
runner = packet/'run.py'
assert digest(runner) == '825c24d68c9a6f28f2127bb96099137f44607518b7b84ebb15f5a09fdbb1b527'
r = runner.read_text()
assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
assert 'shutil.disk_usage(\'/tmp\').free>=5_000_000_000' in r
assert "if local=='Sign21DirectPolynomialBridge':expected_hash=base['rows'][0]['object_sha256']" in r
assert "outer-result.json')=='b2f8aca8c356193f1dcf521a6c07397f7c13c6d036319e94d3bf1eac715856d0'" in r
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':digest(runner),'stages':3,
                  'scope':'adapted native, standard and translated symbolic Fin21 endpoint candidates; no Lean result'},sort_keys=True,indent=2))
