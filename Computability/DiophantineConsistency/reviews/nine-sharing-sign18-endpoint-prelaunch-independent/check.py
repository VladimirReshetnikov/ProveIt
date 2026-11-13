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
packet = research/'nine-sharing-sign18-endpoint-check'
draft = research/'nine-sharing-sign18-endpoint-draft'
prior = research/'nine-sharing-sign19-endpoint-check'
bridge = research/'nine-sharing-sign18-concrete-polynomial-bridge-check'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = packet/'source-manifest.json'
assert digest(manifest) == 'eab9417282cdfc298e3153378f727fdc703f6bbdc84963a54e2258999c4a4e90'
rows = json.loads(manifest.read_text())['rows']
names = ['Sign18DirectNoAliasNative','Sign18DirectNoAliasStandard','Sign18DirectNoAliasTranslated']
assert [r['module'] for r in rows] == ['DiophantineConsistency.'+n for n in names]
for row,name in zip(rows,names):
    src = packet/'src/DiophantineConsistency'/(name+'.lean')
    old = prior/'src/DiophantineConsistency'/(name.replace('Sign18','Sign19')+'.lean')
    assert digest(src) == digest(draft/(name+'.lean')) == row['source_sha256']
    assert src.read_text() == old.read_text().replace('Sign19','Sign18').replace('SharingSeed19Degree44','SharingSeed18Degree94')
    assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M) == row['imports']
assert rows[0]['imports'] == ['DiophantineConsistency.Sign18DirectPolynomialBridge','DiophantineConsistency.IPRAExpressionNative']
assert rows[1]['imports'] == ['DiophantineConsistency.Sign18DirectNoAliasNative','DiophantineConsistency.IPRAStandardTheory']
assert rows[2]['imports'] == ['DiophantineConsistency.Sign18DirectNoAliasStandard']
state = json.loads((bridge/'attempt01/state.json').read_text())
outer = json.loads((bridge/'attempt01/outer-result.json').read_text())
assert state['status'] == 'PASS' and outer['author_observed_numeric_outer_exit'] == 0 and state['rows'][0]['object_sha256'] == '3b50d8bb8862b981e1e66ea7eea5aa0d6c317b878095776611071b5e834969e9'
audit = root/'reviews/nine-sharing-sign18-concrete-polynomial-bridge-terminal-independent/check.py'
assert digest(audit) == '61eb2d46b217b1e0f6f39b7cb057193edf65aacc26e4c387e93c152d89275bbe'
subprocess.run([sys.executable,'-I','-S','-B',str(audit)],check=True,capture_output=True,timeout=120)
survey = packet/'framework-survey.py'
assert digest(survey) == '705b227ca2831ec015de1b45140153f1f46f24a383052cf667aca0a29fcc7b04'
old_survey = (prior/'framework-survey.py').read_text()
assert survey.read_text() == old_survey.replace('/tmp/nine-sharing-sign19-concrete-polynomial-bridge-check-20261109','/tmp/nine-sharing-sign18-concrete-polynomial-bridge-check-20261109')
runner = packet/'run.py'
assert digest(runner) == '5843fdb08deab400b572a778e5f96ec6e54b014899f3d2675607fcdf2db3e1ac'
r = runner.read_text()
assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
assert 'shutil.disk_usage(\'/tmp\').free>=5_000_000_000' in r
assert "if local=='Sign18DirectPolynomialBridge':expected_hash=base['rows'][0]['object_sha256']" in r
assert "outer-result.json')=='83a3040504fc9d9c18e38e86af364f903cb573c073dd9188b2926f26e664b7cf'" in r
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':digest(runner),'stages':3,
                  'scope':'adapted native, standard and translated symbolic Fin18 endpoint candidates; no Lean result'},sort_keys=True,indent=2))
