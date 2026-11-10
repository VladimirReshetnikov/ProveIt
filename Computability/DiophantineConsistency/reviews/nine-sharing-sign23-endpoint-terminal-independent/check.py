#!/usr/bin/env python3
"""Audit three checked Fin23 iPRA endpoints and their guarded providers."""
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
packet = research/'nine-sharing-sign23-endpoint-check'
prior = research/'nine-sharing-sign24-endpoint-memory-check'
attempt = packet/'attempt01'
output = Path('/tmp/nine-sharing-sign23-endpoint-check-20261109')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt/'outer-result.json').read_text())
assert outer['author_observed_outer_session'] == 26160 and outer['author_observed_numeric_outer_exit'] == 0
state_path = attempt/'state.json'
assert digest(state_path) == digest(output/'state.json') == outer['state_sha256']
state = json.loads(state_path.read_text())
runner = packet/'run.py'
assert state['status'] == 'PASS' and len(state['rows']) == 3
assert state['runner_sha256'] == digest(runner) == '84c52e445558adf15c87cec8582aafd2433032885c1af9d0d2553535c693f226'
assert "'-M3600'" in runner.read_text() and "rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1" in runner.read_text()
manifest = json.loads((packet/'source-manifest.json').read_text())['rows']
names = ['Sign23DirectNoAliasNative','Sign23DirectNoAliasStandard','Sign23DirectNoAliasTranslated']
objects = ['8adc0db4e8d2d257b2a25d855af84b1010f577d2b9c20880192a2f5a86566a5f', '47b1c4c9cd5523b79112fdad88d900178b1c7724eeabc622863b5aa6ef36fdc2', '10c4a1bb278c2845ba025e5dc6d1eacedbe3c9f5e2edf0eb43975af40f87b7ce']
pins = {'Sign23DirectPolynomialBridge':'2cb1f6c016b2d608ecc59ff59c9d88be2ab5a19d76a65d4c98c9f1ed76360c71',
        'IPRAExpressionNative':'9c2c741dd39fceb7a12eec69b4a038e33d7b9396d0df9ba4207a97ef7254e684',
        'IPRAStandardTheory':'b2417583564a1d6b0bbfb4952587db79339fab8c2b4d24442145e39578173e19', **dict(zip(names,objects))}
assert [r['module'] for r in state['rows']] == names
guards = 0
for row,entry,name,obj in zip(state['rows'],manifest,names,objects):
    src = packet/'src/DiophantineConsistency'/(name+'.lean')
    assert row['source_sha256'] == entry['source_sha256'] == digest(src) == digest(output/'src/DiophantineConsistency'/(name+'.lean'))
    assert src.read_text() == (prior/'src/DiophantineConsistency'/(name.replace('Sign23','Sign24')+'.lean')).read_text().replace('Sign24','Sign23').replace('SharingSeed24Octic','SharingSeed23Octic')
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
    theorem = {'Sign23DirectNoAliasNative':'native_equivalence','Sign23DirectNoAliasStandard':'standard_equivalence','Sign23DirectNoAliasTranslated':'standard_translated_equivalence'}[name]
    assert "'DiophantineConsistency.Sign23DirectNoAlias."+theorem+"' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in state['overlay_links'].items(): assert Path(path).is_symlink() and str(Path(path).resolve()) == target
upstream = root/'reviews/nine-sharing-sign23-concrete-polynomial-bridge-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':26160,'outer_exit':0,'stages':3,'guards':guards,
                  'overlay_links':len(state['overlay_links']),'state_sha256':digest(state_path),
                  'scope':'native, standard and GG-translated Fin23 iPRA derivability; no exact degree, Jones or JSON/PDF binding'},sort_keys=True,indent=2))
