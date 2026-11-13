#!/usr/bin/env python3
"""Audit three checked Fin22 iPRA endpoints and their guarded providers."""
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
research = root/'research'
packet = research/'nine-sharing-sign22-endpoint-check'
prior = research/'nine-sharing-sign23-endpoint-check'
attempt = packet/'attempt01'
output = Path('/tmp/nine-sharing-sign22-endpoint-check-20261109')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt/'outer-result.json').read_text())
assert outer['author_observed_outer_session'] == 5243 and outer['author_observed_numeric_outer_exit'] == 0
state_path = attempt/'state.json'
assert digest(state_path) == digest(output/'state.json') == outer['state_sha256']
state = json.loads(state_path.read_text())
runner = packet/'run.py'
assert state['status'] == 'PASS' and len(state['rows']) == 3
assert state['runner_sha256'] == digest(runner) == '1e346805c189363cde3eccf70f0c5ec00cb97551ca1f68eecabc9a78d50ba1ba'
assert "'-M3600'" in runner.read_text() and "rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1" in runner.read_text()
manifest = json.loads((packet/'source-manifest.json').read_text())['rows']
names = ['Sign22DirectNoAliasNative','Sign22DirectNoAliasStandard','Sign22DirectNoAliasTranslated']
objects = ['46885d9abcf4d4c78f3fd85ae0aa61f2f360045c108e7fc928cc6474c877a20d', '68d8f7515a498cb6c0713b1183f1856dbde3b080d5e612f406da5d4aec7bc047', '8e49833b6ce3cc3ea41b28da088dd87d8a28d6ed97404a8a3bc2740c18966d6e']
pins = {'Sign22DirectPolynomialBridge':'53e98c8448caeebd9564037973e0ecd88be1793abd03f321d4d161f0651c7934',
        'IPRAExpressionNative':'9c2c741dd39fceb7a12eec69b4a038e33d7b9396d0df9ba4207a97ef7254e684',
        'IPRAStandardTheory':'b2417583564a1d6b0bbfb4952587db79339fab8c2b4d24442145e39578173e19', **dict(zip(names,objects))}
assert [r['module'] for r in state['rows']] == names
guards = 0
for row,entry,name,obj in zip(state['rows'],manifest,names,objects):
    src = packet/'src/DiophantineConsistency'/(name+'.lean')
    assert row['source_sha256'] == entry['source_sha256'] == digest(src) == digest(output/'src/DiophantineConsistency'/(name+'.lean'))
    assert src.read_text() == (prior/'src/DiophantineConsistency'/(name.replace('Sign22','Sign23')+'.lean')).read_text().replace('Sign23','Sign22').replace('SharingSeed23Octic','SharingSeed22Dodecic')
    assert row['object_sha256'] == obj == digest(output/'lib/DiophantineConsistency'/(name+'.olean'))
    for phase in ('deps','compile'):
        stage = row[phase]
        assert stage['exit'] == 0 and stage['stop_reason'] is None and not stage['monitor_errors'] and not stage['observed_descendant_pids']
        assert stage['rss_limit_bytes'] == 4*1024**3 and stage['host_floor_bytes'] == 10*1024**3 and stage['timeout_seconds'] == 120
        log = name+'-'+phase+'.txt'
        assert digest(attempt/log) == digest(output/log) == stage['log_sha256'] == outer['logs'][log]
    for path,observation in row['direct_guard'].items():
        candidate = Path(path)
        if observation is None: assert not os.path.lexists(candidate)
        else: assert candidate.is_file() and str(candidate.resolve()) == observation['realpath'] and digest(candidate) == observation['sha256']
        guards += 1
    for mod in entry['imports']:
        dep = row['dependencies'][mod]
        assert dep['sha256'] == pins[mod.split('.')[-1]] and row['direct_guard'][dep['path']] == {'sha256':dep['sha256'],'realpath':dep['realpath']}
    log = ' '.join((attempt/(name+'-compile.txt')).read_text().split())
    assert not re.search(r'warning:|error:|sorryAx',log)
    theorem = {'Sign22DirectNoAliasNative':'native_equivalence','Sign22DirectNoAliasStandard':'standard_equivalence','Sign22DirectNoAliasTranslated':'standard_translated_equivalence'}[name]
    assert "'DiophantineConsistency.Sign22DirectNoAlias."+theorem+"' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in state['overlay_links'].items(): assert Path(path).is_symlink() and str(Path(path).resolve()) == target
upstream = root/'reviews/nine-sharing-sign22-concrete-polynomial-bridge-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':5243,'outer_exit':0,'stages':3,'guards':guards,
                  'overlay_links':len(state['overlay_links']),'state_sha256':digest(state_path),
                  'scope':'native, standard and GG-translated Fin22 iPRA derivability; no exact degree, Jones or JSON/PDF binding'},sort_keys=True,indent=2))
