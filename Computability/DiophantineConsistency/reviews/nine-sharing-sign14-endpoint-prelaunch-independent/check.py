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
packet = research/'nine-sharing-sign14-endpoint-check'
draft = research/'nine-sharing-sign14-endpoint-draft'
prior = research/'nine-sharing-sign15-endpoint-check'
bridge = research/'nine-sharing-sign14-concrete-polynomial-bridge-check'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = packet/'source-manifest.json'
assert digest(manifest) == '8a3d6a336493456939c83db62b11059fdf90f3a3bef4775503d59817ec697b29'
rows = json.loads(manifest.read_text())['rows']
names = ['Sign14DirectNoAliasNative','Sign14DirectNoAliasStandard','Sign14DirectNoAliasTranslated']
assert [r['module'] for r in rows] == ['DiophantineConsistency.'+n for n in names]
for row,name in zip(rows,names):
    src = packet/'src/DiophantineConsistency'/(name+'.lean')
    old = prior/'src/DiophantineConsistency'/(name.replace('Sign14','Sign15')+'.lean')
    assert digest(src) == digest(draft/(name+'.lean')) == row['source_sha256']
    assert src.read_text() == old.read_text().replace('Sign15','Sign14').replace('SharingSeed15Degree124','SharingSeed14Degree124')
    assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M) == row['imports']
assert rows[0]['imports'] == ['DiophantineConsistency.Sign14DirectPolynomialBridge','DiophantineConsistency.IPRAExpressionNative']
assert rows[1]['imports'] == ['DiophantineConsistency.Sign14DirectNoAliasNative','DiophantineConsistency.IPRAStandardTheory']
assert rows[2]['imports'] == ['DiophantineConsistency.Sign14DirectNoAliasStandard']
state = json.loads((bridge/'attempt01/state.json').read_text())
outer = json.loads((bridge/'attempt01/outer-result.json').read_text())
assert state['status'] == 'PASS' and outer['author_observed_numeric_outer_exit'] == 0 and state['rows'][0]['object_sha256'] == '4b59e7a1e45825818b5b5715cb26d1b195d9b25b6aacda8a81078d37cecfc2ed'
audit = root/'reviews/nine-sharing-sign14-concrete-polynomial-bridge-terminal-independent/check.py'
assert digest(audit) == '60518629de439ba701c339bc42c997bd59499644f967c1d7bbe2996fa99f1b4f'
subprocess.run([sys.executable,'-I','-S','-B',str(audit)],check=True,capture_output=True,timeout=120)
survey = packet/'framework-survey.py'
assert digest(survey) == '9167ee10551dbe197c4ff3e6fd7382449bbf565d25dbf41e61ef1314c7cd3aec'
old_survey = (prior/'framework-survey.py').read_text()
assert survey.read_text() == old_survey.replace('/tmp/nine-sharing-sign15-concrete-polynomial-bridge-check-20261110','/tmp/nine-sharing-sign14-concrete-polynomial-bridge-check-20261110')
runner = packet/'run.py'
assert digest(runner) == 'bc1c9e91310ba95b5c3230c0043042910bf2080e768fde778ff4dba611a9ca73'
r = runner.read_text()
assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
assert 'shutil.disk_usage(\'/tmp\').free>=5_000_000_000' in r
assert "if local=='Sign14DirectPolynomialBridge':expected_hash=base['rows'][0]['object_sha256']" in r
assert "outer-result.json')=='aa3036c9f8b209e58d306091d7b6917faa8083f07a111cc8e441e3d0680f3e7c'" in r
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':digest(runner),'stages':3,
                  'scope':'adapted native, standard and translated symbolic Fin14 endpoint candidates; no Lean result'},sort_keys=True,indent=2))
