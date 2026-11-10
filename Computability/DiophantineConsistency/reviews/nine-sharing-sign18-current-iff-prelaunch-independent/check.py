#!/usr/bin/env python3
"""Review current-port specialization and its partial historical provider."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root / 'research'
packet = research / 'nine-sharing-sign18-current-iff-check'
draft = research / 'nine-sharing-sign18-seed-iff-draft'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
src = packet / 'src/DiophantineConsistency/Sign18CurrentSeedIff.lean'
entry, = json.loads((packet / 'source-manifest.json').read_text())['rows']
assert entry['module'] == 'DiophantineConsistency.Sign18CurrentSeedIff'
assert digest(src) == digest(draft / 'Sign18CurrentSeedIff.lean') == entry['source_sha256']
assert re.findall(r'^import ([A-Za-z0-9_.]+)$', src.read_text(), re.M) == entry['imports'] == ['DiophantineConsistency.Sign18SeedExistential','DiophantineConsistency.CurrentKernelData2011']
s = src.read_text()
assert 'CurrentWindowCarry2011.ports 0 = (CurrentMasks2011.beta : ℤ) from rfl' in s
assert 'Int.cast_natCast, map_natCast' in s
assert 'Sign18SeedIff.exists_same_input CurrentWindowCarry2011.ports (CurrentMasks2011.beta : V) x port0' in s
assert '∃ v : Fin 19 → V, v 0 = x' in s and '∃ v : Fin 20 → V, v 0 = x' in s
historical = research / 'nine-sharing-norm38-current-ports-split-draft/attempt01/state.json'
state = json.loads(historical.read_text())
assert state['status'] == 'FAILED' and len(state['rows']) >= 2
assert all(state['rows'][i]['compile']['exit'] == 0 for i in (0,1))
survey = subprocess.run([sys.executable,'-I','-S','-B',str(packet/'port-survey.py')],capture_output=True,text=True,timeout=120)
assert survey.returncode == 0 and json.loads(survey.stdout)['status'] == 'PASS' and 'failed producer' in json.loads(survey.stdout)['scope']
audit = root / 'reviews/nine-sharing-sign18-seed-iff-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(audit)],check=True,capture_output=True,timeout=120)
runner=packet/'run.py';assert digest(runner)=='73d7cad17b7318466dde83021668d83aea282d92d4e0f830c45da4c3d41805f4'
r=runner.read_text();assert "if local=='Sign18SeedExistential':" in r and "elif local=='CurrentKernelData2011':" in r and "'-M2800'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
preflight = subprocess.run([sys.executable,'-I','-S','-B',str(packet/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180)
assert preflight.returncode == 0 and not preflight.stderr and json.loads(preflight.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','source_sha256':digest(src),'runner_sha256':digest(packet/'run.py'),
                  'historical_provider_status':'FAILED with two successful child stages',
                  'scope':'current-port specialization source and point providers only; no Lean result or endpoint'},sort_keys=True,indent=2))
