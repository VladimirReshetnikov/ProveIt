#!/usr/bin/env python3
"""Review independent import-only diagnostic modules and provider routing."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root / 'research'
packet = research / 'nine-sharing-sign25-wrapper-import-diagnostic-check'
draft = research / 'nine-sharing-sign25-wrapper-import-diagnostic-draft'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = packet / 'source-manifest.json'
assert digest(manifest) == '1f178eaebf7e0e0361c3c03310979f973a5c73b3ce652fde7202336bbfda6e80'
rows = json.loads(manifest.read_text())['rows']
names = ['Sign25ImportNativeOnly','Sign25ImportStandardOnly','Sign25ImportBoth']
assert [r['module'] for r in rows] == ['DiophantineConsistency.' + n for n in names]
expected = [['DiophantineConsistency.Sign25DirectNoAliasNative'], ['DiophantineConsistency.IPRAStandardTheory'],
            ['DiophantineConsistency.Sign25DirectNoAliasNative','DiophantineConsistency.IPRAStandardTheory']]
for row, name, imports in zip(rows,names,expected):
    src = packet / 'src/DiophantineConsistency' / (name + '.lean')
    assert digest(src) == digest(draft / (name + '.lean')) == row['source_sha256']
    assert re.findall(r'^import ([A-Za-z0-9_.]+)$', src.read_text(), re.M) == row['imports'] == imports
    assert not re.search(r'(?m)^(?:def|theorem|lemma|#check|#print)\b',src.read_text())
runner = (packet/'run.py').read_text()
assert digest(packet/'run.py') == '494fe3e9e62f725aea06438b5d12311b111c48721d2928e5fc1c098399167a82'
assert "elif local in ('Sign25ImportNativeOnly'):" in runner
# The expression above is string membership, but these exact manifest imports
# always reach the preceding native case or the framework case instead.
assert set(m.split('.')[-1] for row in rows for m in row['imports']) == {'Sign25DirectNoAliasNative','IPRAStandardTheory'}
assert not any(m.split('.')[-1] in 'Sign25ImportNativeOnly' for row in rows for m in row['imports'])
assert "if local=='Sign25DirectNoAliasNative':expected_hash=base['rows'][0]['object_sha256']" in runner
assert "base['status']=='FAILED'" in runner and "for row in base['rows'][:1]:" in runner
audit = root / 'reviews/nine-sharing-sign25-endpoint-no-alias-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(audit)],check=True,capture_output=True,timeout=120)
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(packet/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':digest(packet/'run.py'),
                  'scope':'import-only modules, fail-stop; producer is successful child of failed outer run',
                  'single_element_membership':'string, unreachable for pinned actual imports'},sort_keys=True,indent=2))
