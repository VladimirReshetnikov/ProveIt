#!/usr/bin/env python3
"""Review reuse of the successful native child from a failed outer run."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root / 'research'
packet = research / 'nine-sharing-sign25-endpoint-wrappers-check'
draft = research / 'nine-sharing-sign25-endpoint-wrappers-draft'
retry = research / 'nine-sharing-sign25-endpoint-no-alias-retry-check/src/DiophantineConsistency'
partial = research / 'nine-sharing-sign25-endpoint-no-alias-check'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = packet / 'source-manifest.json'
assert digest(manifest) == 'a3c2e0a8d69877c4c4179e271d26e98bfc96e26c870f3768eca6469f1546ad46'
rows = json.loads(manifest.read_text())['rows']
names = ['Sign25DirectNoAliasStandard','Sign25DirectNoAliasTranslated']
assert [r['module'] for r in rows] == ['DiophantineConsistency.' + n for n in names]
for name, row in zip(names, rows):
    src = packet / 'src/DiophantineConsistency' / (name + '.lean')
    assert digest(src) == digest(draft / (name + '.lean')) == digest(retry / (name + '.lean')) == row['source_sha256']
    assert re.findall(r'^import ([A-Za-z0-9_.]+)$', src.read_text(), re.M) == row['imports']
assert rows[0]['imports'] == ['DiophantineConsistency.Sign25DirectNoAliasNative','DiophantineConsistency.IPRAStandardTheory']
assert rows[1]['imports'] == ['DiophantineConsistency.Sign25DirectNoAliasStandard']
assert 'standardTheory ⊢' in (draft / (names[0] + '.lean')).read_text()
assert '(Semiformula.lMap embedding sourceSentence)ᴺ' in (draft / (names[1] + '.lean')).read_text()
state_path = partial / 'attempt01/state.json'
assert digest(state_path) == '0e775b75519c40e1d4410cc8fea42d003c9733c4233a81e35b90b3bcb2384361'
state = json.loads(state_path.read_text())
assert state['status'] == 'FAILED' and len(state['rows']) == 2
assert state['rows'][0]['module'] == 'Sign25DirectNoAliasNative' and state['rows'][0]['compile']['exit'] == 0
assert state['rows'][0]['object_sha256'] == '90c2795bbcca2630f16e1b0f0cb7ee7723a849c0a401bcf240115888faadcd8b'
assert state['rows'][1]['module'] == 'Sign25DirectNoAliasStandard' and state['rows'][1]['compile']['exit'] == -6
assert json.loads((partial / 'attempt01/outer-result.json').read_text())['outer_exit_code'] == 1
audit = root / 'reviews/nine-sharing-sign25-endpoint-no-alias-terminal-independent/check.py'
assert digest(audit) == '3efa7f2442a8855d6f5b9df2ada203bd05b35de0eb162609bcbf4e80d268f6ac'
subprocess.run([sys.executable,'-I','-S','-B',str(audit)], check=True, capture_output=True, timeout=120)
runner = (packet / 'run.py').read_text()
assert digest(packet / 'run.py') == '80c080da95b678b1ed3d56ad047d040a73752ab4b0f995345d9455abfff45cd6'
assert "for row in base['rows'][:1]:" in runner and "base['status']=='FAILED'" in runner
assert "if local=='Sign25DirectNoAliasNative':expected_hash=base['rows'][0]['object_sha256']" in runner
assert "need(sha(BASE/'src/DiophantineConsistency'/(n+'.lean'))==row['source_sha256']" in runner
assert "'Sign25DirectNoAliasStandard','Sign25DirectNoAliasTranslated'" in runner
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(packet / 'run.py'),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','native_parent_outer_exit':1,'native_child_exit':0,
                  'runner_sha256':digest(packet / 'run.py'),'scope':'reuse of audited successful native child; no parent postflight or new endpoint'},sort_keys=True,indent=2))
