#!/usr/bin/env python3
"""Audit sign20/21 direct zero equivalence and observed providers."""
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
packet = root/'research/nine-sharing-sign19-expression-equivalence-check'
attempt = packet/'attempt01'
output = Path('/tmp/nine-sharing-sign19-expression-equivalence-check-20261109')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt/'outer-result.json').read_text())
assert outer['author_observed_outer_session'] == 62699 and outer['author_observed_numeric_outer_exit'] == 0
state_path = attempt/'state.json'
assert digest(state_path) == digest(output/'state.json') == outer['state_sha256']
state = json.loads(state_path.read_text())
assert state['status'] == 'PASS' and len(state['rows']) == 1 and state['runner_sha256'] == digest(packet/'run.py')
row, = state['rows']
name = 'Sign19ExpressionEquivalence'
source = packet/'src/DiophantineConsistency'/(name+'.lean')
entry, = json.loads((packet/'source-manifest.json').read_text())['rows']
assert row['module'] == name and row['source_sha256'] == entry['source_sha256'] == digest(source) == digest(output/'src/DiophantineConsistency'/(name+'.lean'))
assert row['object_sha256'] == digest(output/'lib/DiophantineConsistency'/(name+'.olean')) == '8aaef1965c323908270875a59a7e35ad7d3b850dce7c71ea7287e987b546fb2a'
for phase in ('deps','compile'):
    stage = row[phase]
    assert stage['exit'] == 0 and stage['stop_reason'] is None and not stage['monitor_errors'] and not stage['observed_descendant_pids']
    log = name+'-'+phase+'.txt'
    assert digest(attempt/log) == digest(output/log) == stage['log_sha256'] == outer['logs'][log]
for path, observation in row['direct_guard'].items():
    candidate = Path(path)
    if observation is None: assert not os.path.lexists(candidate)
    else: assert candidate.is_file() and str(candidate.resolve()) == observation['realpath'] and digest(candidate) == observation['sha256']
pins = {'Sign19CurrentExpressionEval':'739961b9ea47a288a2b8e0aa2f8290eac430079d03481d0d738515eef940fea0',
        'Sign20CurrentExpressionEval':'aac81160cfe2f4d449f26b5c2c8ffeff411582ca95eb764d4055e0f7ea57ec78',
        'Sign19CurrentSeedIff':'c08944762b4d6b4381b0029f85526367bd76418409e4bc8b88789ad3bbf2aeee'}
for mod in entry['imports']:
    dep = row['dependencies'][mod]
    assert dep['sha256'] == pins[mod.split('.')[-1]] and row['direct_guard'][dep['path']] == {'sha256':dep['sha256'],'realpath':dep['realpath']}
log = ' '.join((attempt/(name+'-compile.txt')).read_text().split())
assert log.count('warning:') == 1 and 'unusedSectionVars' in log and 'error:' not in log and 'sorryAx' not in log
for th in ('exists_cons_iff','zero_exists_iff'):
    assert "'DiophantineConsistency.Sign19ExpressionEquivalence."+th+"' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in state['overlay_links'].items(): assert Path(path).is_symlink() and str(Path(path).resolve()) == target
for review in ('nine-sharing-sign19-current-iff-terminal-independent','nine-sharing-sign19-expression-eval-terminal-independent','nine-sharing-sign20-expression-eval-terminal-independent'):
    subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/review/'check.py')],check=True,capture_output=True,timeout=120)
subprocess.run([sys.executable,'-I','-S','-B',str(packet/'evaluator-union-survey.py')],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':62699,'guards':len(row['direct_guard']),
                  'overlay_links':len(state['overlay_links']),'state_sha256':digest(state_path),'warnings':1,
                  'scope':'current-port direct Fin19/Fin20 zero existence equivalence; no iPRA endpoint'},sort_keys=True,indent=2))
