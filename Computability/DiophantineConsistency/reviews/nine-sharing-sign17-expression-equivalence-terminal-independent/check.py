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
packet = root/'research/nine-sharing-sign17-expression-equivalence-check'
attempt = packet/'attempt01'
output = Path('/tmp/nine-sharing-sign17-expression-equivalence-check-20261109')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt/'outer-result.json').read_text())
assert outer['author_observed_outer_session'] == 67784 and outer['author_observed_numeric_outer_exit'] == 0
state_path = attempt/'state.json'
assert digest(state_path) == digest(output/'state.json') == outer['state_sha256']
state = json.loads(state_path.read_text())
assert state['status'] == 'PASS' and len(state['rows']) == 1 and state['runner_sha256'] == digest(packet/'run.py')
row, = state['rows']
name = 'Sign17ExpressionEquivalence'
source = packet/'src/DiophantineConsistency'/(name+'.lean')
entry, = json.loads((packet/'source-manifest.json').read_text())['rows']
assert row['module'] == name and row['source_sha256'] == entry['source_sha256'] == digest(source) == digest(output/'src/DiophantineConsistency'/(name+'.lean'))
assert row['object_sha256'] == digest(output/'lib/DiophantineConsistency'/(name+'.olean')) == '65c69fe64befa82c8ba23fe934e903b5985fd47f361a036bccb180fc6faa5bb5'
for phase in ('deps','compile'):
    stage = row[phase]
    assert stage['exit'] == 0 and stage['stop_reason'] is None and not stage['monitor_errors'] and not stage['observed_descendant_pids']
    log = name+'-'+phase+'.txt'
    assert digest(attempt/log) == digest(output/log) == stage['log_sha256'] == outer['logs'][log]
for path, observation in row['direct_guard'].items():
    candidate = Path(path)
    if observation is None: assert not os.path.lexists(candidate)
    else: assert candidate.is_file() and str(candidate.resolve()) == observation['realpath'] and digest(candidate) == observation['sha256']
pins = {'Sign17CurrentExpressionEval':'4ccb0e17b7f57d9516d4383dd53960f82a7c4d92c1d8f518484dfed8f9d13abc',
        'Sign18CurrentExpressionEval':'3ee861055296d6d6f8ffd9fad06cfbe4e6ac8be24b7b1c054cf85cce73b645d5',
        'Sign17CurrentSeedIff':'02e99186726eeaabd9eb89183714fd8329cb1f136821e8c62ae7c23a715a839d'}
for mod in entry['imports']:
    dep = row['dependencies'][mod]
    assert dep['sha256'] == pins[mod.split('.')[-1]] and row['direct_guard'][dep['path']] == {'sha256':dep['sha256'],'realpath':dep['realpath']}
log = ' '.join((attempt/(name+'-compile.txt')).read_text().split())
assert log.count('warning:') == 1 and 'unusedSectionVars' in log and 'error:' not in log and 'sorryAx' not in log
for th in ('exists_cons_iff','zero_exists_iff'):
    assert "'DiophantineConsistency.Sign17ExpressionEquivalence."+th+"' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in state['overlay_links'].items(): assert Path(path).is_symlink() and str(Path(path).resolve()) == target
for review in ('nine-sharing-sign17-current-iff-retry01-terminal-independent','nine-sharing-sign17-expression-eval-terminal-independent','nine-sharing-sign18-expression-eval-terminal-independent'):
    subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/review/'check.py')],check=True,capture_output=True,timeout=120)
subprocess.run([sys.executable,'-I','-S','-B',str(packet/'evaluator-union-survey.py')],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':67784,'guards':len(row['direct_guard']),
                  'overlay_links':len(state['overlay_links']),'state_sha256':digest(state_path),'warnings':1,
                  'scope':'current-port direct Fin17/Fin18 zero existence equivalence; no iPRA endpoint'},sort_keys=True,indent=2))
