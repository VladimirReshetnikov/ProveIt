#!/usr/bin/env python3
"""Audit sign20 transfer artifacts and retained warning/axiom reports."""
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
packet = root / 'research/nine-sharing-sign19-transfers-check'
attempt = packet / 'attempt01'
output = Path('/tmp/nine-sharing-sign19-transfers-check-20261109')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt / 'outer-result.json').read_text())
assert outer['author_observed_outer_session'] == 72629 and outer['author_observed_numeric_outer_exit'] == 0
state_path = attempt / 'state.json'
assert digest(state_path) == digest(output / 'state.json') == outer['state_sha256']
state = json.loads(state_path.read_text())
assert state['status'] == 'PASS' and len(state['rows']) == 2 and state['runner_sha256'] == digest(packet / 'run.py')
manifest = json.loads((packet / 'source-manifest.json').read_text())['rows']
objs = ['6262222a3179056b8181067a80c4466796e2e7360888f6ad6837ea31d844e9ae', '88cd823119fd71790f447d0523b9a43cd649153545800cc45c0dcb284726cd39']
gates = ['main_root','Dc2','tau','N0','Nt','cTminusR','V','V2minusY2','Na','scaled_Ns']
guards = warnings = 0
for i, (row, entry, obj) in enumerate(zip(state['rows'], manifest, objs)):
    name = f'Sign19Transfers0{i}'
    assert row['module'] == name and entry['module'] == 'DiophantineConsistency.' + name
    source = packet / 'src/DiophantineConsistency' / (name + '.lean')
    assert digest(source) == row['source_sha256'] == entry['source_sha256'] == digest(output / 'src/DiophantineConsistency' / (name + '.lean'))
    assert digest(output / 'lib/DiophantineConsistency' / (name + '.olean')) == row['object_sha256'] == obj
    for phase in ('deps', 'compile'):
        stage = row[phase]
        assert stage['exit'] == 0 and stage['stop_reason'] is None and not stage['monitor_errors'] and not stage['observed_descendant_pids']
        log = name + '-' + phase + '.txt'
        assert digest(attempt / log) == digest(output / log) == stage['log_sha256'] == outer['logs'][log]
    for path, observation in row['direct_guard'].items():
        candidate = Path(path)
        if observation is None: assert not os.path.lexists(candidate)
        else: assert candidate.is_file() and str(candidate.resolve()) == observation['realpath'] and digest(candidate) == observation['sha256']
        guards += 1
    dep = row['dependencies']['DiophantineConsistency.Sign19Coordinate']
    assert dep['sha256'] == '152766d2d71f8154b20dd8472afe13915c38b9e02c22824742a2e5d43e2fcab5'
    assert row['direct_guard'][dep['path']] == {'sha256':dep['sha256'], 'realpath':dep['realpath']}
    log = (attempt / (name + '-compile.txt')).read_text()
    warnings += len(re.findall(r': warning:', log))
    assert 'error:' not in log and 'sorryAx' not in log
    normalized = ' '.join(log.split())
    for gate in gates[i*5:i*5+5]:
        assert ("'DiophantineConsistency.Sign19Transfers." + gate + "_eval' depends on axioms: [propext, Classical.choice, Quot.sound]") in normalized
assert warnings == 15
for path, target in state['overlay_links'].items(): assert Path(path).is_symlink() and str(Path(path).resolve()) == target
upstream = root / 'reviews/nine-sharing-sign19-coordinate-terminal-independent/check.py'
subprocess.run([sys.executable, '-I', '-S', '-B', str(upstream)], check=True, capture_output=True, timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':72629,'stages':2,'guards':guards,
                  'overlay_links':len(state['overlay_links']),'warnings':warnings,'axiom_reports':10,
                  'state_sha256':digest(state_path),'scope':'10 residual evaluations under Y lift with explicit hp0; no assembled zero bridge'}, sort_keys=True, indent=2))
