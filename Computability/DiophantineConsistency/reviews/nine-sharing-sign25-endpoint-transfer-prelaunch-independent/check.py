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
packet = research / 'nine-sharing-sign25-endpoint-transfer-check'
draft = research / 'nine-sharing-sign25-endpoint-transfer-draft'
retry = research / 'nine-sharing-sign25-endpoint-no-alias-retry-check/src/DiophantineConsistency'
partial = research / 'nine-sharing-sign25-endpoint-no-alias-check'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = packet / 'source-manifest.json'
assert digest(manifest) == '2c21e924b2ed3e68812cb9cfc4129d63f00adfce439491aaf33659719c176c61'
rows = json.loads(manifest.read_text())['rows']
names = ['Sign25DirectNoAliasStandard','Sign25DirectNoAliasTranslated']
assert [r['module'] for r in rows] == ['DiophantineConsistency.' + n for n in names]
for name, row in zip(names, rows):
    src = packet / 'src/DiophantineConsistency' / (name + '.lean')
    assert digest(src) == digest(draft / (name + '.lean')) == row['source_sha256']
    prior = (retry / (name + '.lean')).read_text()
    if name == names[0]: prior = prior.replace('(IPRAStandardTheory.provable_iff _).2 native_equivalence', 'IPRAStandardTheory.transfer IPRAStandardTheory.native_axiom native_equivalence')
    assert src.read_text() == prior
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
assert digest(packet / 'run.py') == '8b2eaa1f44950c26e7d49357e80011b8900a7d7a979d094be5c429c51b1db2a8'
assert "for row in base['rows'][:1]:" in runner and "base['status']=='FAILED'" in runner
assert "if local=='Sign25DirectNoAliasNative':expected_hash=base['rows'][0]['object_sha256']" in runner
assert "need(sha(BASE/'src/DiophantineConsistency'/(n+'.lean'))==row['source_sha256']" in runner
assert "'Sign25DirectNoAliasStandard','Sign25DirectNoAliasTranslated'" in runner
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(packet / 'run.py'),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','native_parent_outer_exit':1,'native_child_exit':0,
                  'runner_sha256':digest(packet / 'run.py'),'scope':'reuse of audited successful native child; no parent postflight or new endpoint'},sort_keys=True,indent=2))
