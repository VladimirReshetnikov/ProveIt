#!/usr/bin/env python3
"""Audit two successful typed-sentence children and failed third stage."""
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
packet = root/'research/nine-sharing-sign25-specialization-diagnostic-check'
attempt = packet/'attempt01'
output = Path('/tmp/nine-sharing-sign25-specialization-diagnostic-20261109')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt/'outer-result.json').read_text())
assert outer['outer_session_id'] == 13751 and outer['outer_exit_code'] == 1
state_path = attempt/'state.json'
assert digest(state_path) == digest(output/'state.json')
state = json.loads(state_path.read_text())
assert state['status'] == 'FAILED' and state['failure'] == "RuntimeError('compile failed Sign25TypedCheckFormula')"
assert state['runner_sha256'] == digest(packet/'run.py') == 'aed65d2aa512dcea9c415c0bed978d97a037074c9b9c57f1c7fefb0cb60a4609'
manifest = json.loads((packet/'source-manifest.json').read_text())['rows']
names = ['Sign25GenericStandard','Sign25TypedSentence','Sign25TypedImports','Sign25TypedCheckFormula']
objects = ['72ea694f8bcb2d8c4267dc6f38d79b274ddffde9a7de2c17d7c78a31009de3f4','ff6b8634fca29d81c12311313b06a2611c35831b8f289745cb0867f0c13dd4d4','e9e0d11607be8f674b95e6b15a3224eb60e26cf790660aa8a172bdff6e901d51']
assert [r['module'] for r in state['rows']] == names
pins = {'IPRAExpressionNative':'9c2c741dd39fceb7a12eec69b4a038e33d7b9396d0df9ba4207a97ef7254e684',
        'IPRAStandardTheory':'b2417583564a1d6b0bbfb4952587db79339fab8c2b4d24442145e39578173e19',
        'Sign25CurrentExpressionDef':'759739a7d02784404feef8375cf95ffaf3231f08af5a39172fc52b72e77d12cc',
        'Sign25DirectPolynomialBridge':'b662728032c262f52f1bda8a52d9b29401129c6279a3f9d4e6f8e2924980f1ea',**dict(zip(names,objects))}
guards = 0
for i,(row,entry,name) in enumerate(zip(state['rows'],manifest,names)):
    src = packet/'src/DiophantineConsistency'/(name+'.lean')
    assert row['source_sha256'] == entry['source_sha256'] == digest(src) == digest(output/'src/DiophantineConsistency'/(name+'.lean'))
    assert row['deps']['exit'] == 0 and row['compile']['exit'] == (0 if i < 3 else -6)
    for phase in ('deps','compile'):
        stage = row[phase]
        assert stage['stop_reason'] is None and not stage['monitor_errors'] and not stage['observed_descendant_pids']
        log = name+'-'+phase+'.txt'
        assert digest(attempt/log) == digest(output/log) == stage['log_sha256']
    for path,observation in row['direct_guard'].items():
        candidate = Path(path)
        if observation is None: assert not os.path.lexists(candidate)
        else: assert candidate.is_file() and str(candidate.resolve()) == observation['realpath'] and digest(candidate) == observation['sha256']
        guards += 1
    for mod in entry['imports']:
        dep = row['dependencies'][mod]
        assert dep['sha256'] == pins[mod.split('.')[-1]] and row['direct_guard'][dep['path']] == {'sha256':dep['sha256'],'realpath':dep['realpath']}
    if i < 3:
        assert digest(output/'lib/DiophantineConsistency'/(name+'.olean')) == row['object_sha256'] == objects[i]
        log = ' '.join((attempt/(name+'-compile.txt')).read_text().split())
        if i < 2:
            th = 'Sign25GenericStandard.standard_of_bridge' if i == 0 else 'Sign25TypedSentence.sentence_def'
            assert "'DiophantineConsistency."+th+"' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
        else: assert not log
        assert 'warning:' not in log and 'sorryAx' not in log
    else:
        log = (attempt/(name+'-compile.txt')).read_text()
        assert 'memory_exception' in log and "'interpreter'" in log
        assert not (output/'lib/DiophantineConsistency'/(name+'.olean')).exists()
assert not (output/'lib/DiophantineConsistency/Sign25TypedCheckProof.olean').exists()
for path,target in state['overlay_links'].items(): assert Path(path).is_symlink() and str(Path(path).resolve()) == target
upstream = root/'reviews/nine-sharing-sign25-concrete-polynomial-bridge-terminal-frontier-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
subprocess.run([sys.executable,'-I','-S','-B',str(packet/'expression-survey.py')],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_PARTIAL_FAILURE_AUDIT','author_session':13751,'outer_exit':1,'successful_children':3,
                  'fourth_compile_exit':-6,'guards':guards,'overlay_links':len(state['overlay_links']),
                  'state_sha256':digest(state_path),'scope':'generic, sentence and import children only; no concrete standard endpoint or postflight'},sort_keys=True,indent=2))
