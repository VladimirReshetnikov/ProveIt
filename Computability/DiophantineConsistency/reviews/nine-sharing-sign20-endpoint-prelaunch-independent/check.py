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
packet = research/'nine-sharing-sign20-endpoint-check'
draft = research/'nine-sharing-sign20-endpoint-draft'
prior = research/'nine-sharing-sign21-endpoint-check'
bridge = research/'nine-sharing-sign20-concrete-polynomial-bridge-check'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = packet/'source-manifest.json'
assert digest(manifest) == 'ed79c1bb35d1b6f5bf9014e275b372610c220a93c7bf9b815e66da12a5537c87'
rows = json.loads(manifest.read_text())['rows']
names = ['Sign20DirectNoAliasNative','Sign20DirectNoAliasStandard','Sign20DirectNoAliasTranslated']
assert [r['module'] for r in rows] == ['DiophantineConsistency.'+n for n in names]
for row,name in zip(rows,names):
    src = packet/'src/DiophantineConsistency'/(name+'.lean')
    old = prior/'src/DiophantineConsistency'/(name.replace('Sign20','Sign21')+'.lean')
    assert digest(src) == digest(draft/(name+'.lean')) == row['source_sha256']
    assert src.read_text() == old.read_text().replace('Sign21','Sign20').replace('SharingSeed21Degree14','SharingSeed20Degree20')
    assert re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M) == row['imports']
assert rows[0]['imports'] == ['DiophantineConsistency.Sign20DirectPolynomialBridge','DiophantineConsistency.IPRAExpressionNative']
assert rows[1]['imports'] == ['DiophantineConsistency.Sign20DirectNoAliasNative','DiophantineConsistency.IPRAStandardTheory']
assert rows[2]['imports'] == ['DiophantineConsistency.Sign20DirectNoAliasStandard']
state = json.loads((bridge/'attempt01/state.json').read_text())
outer = json.loads((bridge/'attempt01/outer-result.json').read_text())
assert state['status'] == 'PASS' and outer['author_observed_numeric_outer_exit'] == 0 and state['rows'][0]['object_sha256'] == 'b7fea8c38fcc8385c1d5e2d1e1397322a90b658b027af888f967c83c2ce20323'
audit = root/'reviews/nine-sharing-sign20-concrete-polynomial-bridge-terminal-independent/check.py'
assert digest(audit) == 'e1744c21057a550a8a35912d1a0be4ba260855a7d219bb01ecc7e88eaf59309b'
subprocess.run([sys.executable,'-I','-S','-B',str(audit)],check=True,capture_output=True,timeout=120)
survey = packet/'framework-survey.py'
assert digest(survey) == 'e520ea55d5db51d161783a9841a40e7465a6bf544204c882945fdd6ef9cf9a7c'
old_survey = (prior/'framework-survey.py').read_text()
assert survey.read_text() == old_survey.replace('/tmp/nine-sharing-sign21-concrete-polynomial-bridge-check-20261109','/tmp/nine-sharing-sign20-concrete-polynomial-bridge-check-20261109')
runner = packet/'run.py'
assert digest(runner) == '0693de812d47ff5f06c06dd217a09c5811e2e7e1d9d199ee5aefd38b49f2a739'
r = runner.read_text()
assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
assert 'shutil.disk_usage(\'/tmp\').free>=5_000_000_000' in r
assert "if local=='Sign20DirectPolynomialBridge':expected_hash=base['rows'][0]['object_sha256']" in r
assert "outer-result.json')=='ba57aa78858d7003a243a23364b6972d8e74865cc639ad061db37077dc5b6f9a'" in r
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':digest(runner),'stages':3,
                  'scope':'adapted native, standard and translated symbolic Fin20 endpoint candidates; no Lean result'},sort_keys=True,indent=2))
