#!/usr/bin/env python3
"""Review Fin15 endpoint adaptation, current bridge and guarded provider routes."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root/'research'
packet = research/'nine-sharing-sign15-endpoint-check'
draft = research/'nine-sharing-sign15-endpoint-draft'
prior = research/'nine-sharing-sign16-endpoint-check'
bridge = research/'nine-sharing-sign15-concrete-polynomial-bridge-check'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = packet/'source-manifest.json'
assert digest(manifest) == '1cb68e0032a8ee5259d4f1239d121e7f870c3dc8935f1eb5b8c0f5ff278f29f5'
rows = json.loads(manifest.read_text())['rows']
names = ['Sign15DirectNoAliasNative','Sign15DirectNoAliasStandard','Sign15DirectNoAliasTranslated']
assert [r['module'] for r in rows] == ['DiophantineConsistency.'+n for n in names]
for row,name in zip(rows,names):
    src = packet/'src/DiophantineConsistency'/(name+'.lean')
    old = prior/'src/DiophantineConsistency'/(name.replace('Sign15','Sign16')+'.lean')
    assert digest(src) == digest(draft/(name+'.lean')) == row['source_sha256']
    assert src.read_text() == old.read_text().replace('Sign16','Sign15').replace('SharingSeed16Degree112','SharingSeed15Degree124')
    assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M) == row['imports']
assert rows[0]['imports'] == ['DiophantineConsistency.Sign15DirectPolynomialBridge','DiophantineConsistency.IPRAExpressionNative']
assert rows[1]['imports'] == ['DiophantineConsistency.Sign15DirectNoAliasNative','DiophantineConsistency.IPRAStandardTheory']
assert rows[2]['imports'] == ['DiophantineConsistency.Sign15DirectNoAliasStandard']
state = json.loads((bridge/'attempt01/state.json').read_text())
outer = json.loads((bridge/'attempt01/outer-result.json').read_text())
assert state['status'] == 'PASS' and outer['author_observed_numeric_outer_exit'] == 0 and state['rows'][0]['object_sha256'] == 'e379da69a9b0ad6947b003dc219cb20d83d41f1afecd3696848bb2b453ca458c'
audit = root/'reviews/nine-sharing-sign15-concrete-polynomial-bridge-terminal-independent/check.py'
assert digest(audit) == '5e94100bb5ae77bc44da341ee9ce5378936fad55bacbf3bf6ee5e9e5745b7ac1'
subprocess.run([sys.executable,'-I','-S','-B',str(audit)],check=True,capture_output=True,timeout=120)
survey = packet/'framework-survey.py'
assert digest(survey) == 'f3235bd52261c43da0f174b53d265655dbc7028ea813b31f08c210cc8530a205'
old_survey = (prior/'framework-survey.py').read_text()
assert survey.read_text() == old_survey.replace('/tmp/nine-sharing-sign16-concrete-polynomial-bridge-check-20261110','/tmp/nine-sharing-sign15-concrete-polynomial-bridge-check-20261110')
runner = packet/'run.py'
assert digest(runner) == '4c198fad6011fd33e73cd481e0db5b3d433ac8a8696879675ed02b30e82be4ae'
r = runner.read_text()
assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
assert 'shutil.disk_usage(\'/tmp\').free>=5_000_000_000' in r
assert "if local=='Sign15DirectPolynomialBridge':expected_hash=base['rows'][0]['object_sha256']" in r
assert "outer-result.json')=='e8c6e520a95142574cddeb787b98dd318cfe42f4cda212c5ee55e9121d3a7d70'" in r
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':digest(runner),'stages':3,
                  'scope':'adapted native, standard and translated symbolic Fin17 endpoint candidates; no Lean result'},sort_keys=True,indent=2))
