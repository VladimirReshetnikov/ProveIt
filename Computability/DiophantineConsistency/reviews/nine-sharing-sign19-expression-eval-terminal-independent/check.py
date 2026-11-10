#!/usr/bin/env python3
"""Audit Fin20 expression/evaluation stages and partial provider surveys."""
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
packet = root/'research/nine-sharing-sign19-expression-eval-check'
attempt = packet/'attempt01'
output = Path('/tmp/nine-sharing-sign19-expression-eval-check-20261109')
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
outer = json.loads((attempt/'outer-result.json').read_text())
assert outer['author_observed_outer_session'] == 42785 and outer['author_observed_numeric_outer_exit'] == 0
state_path = attempt/'state.json'
assert digest(state_path) == digest(output/'state.json') == outer['state_sha256']
state = json.loads(state_path.read_text())
assert state['status'] == 'PASS' and len(state['rows']) == 4 and state['runner_sha256'] == digest(packet/'run.py')
manifest = json.loads((packet/'source-manifest.json').read_text())['rows']
names = ['Sign19AbstractExpressionDef','Sign19AbstractExpressionEval','Sign19CurrentExpressionDef','Sign19CurrentExpressionEval']
objects = ['b171d7a5a813c8b2f965e4770868323ab92f6f3cd6d805ff20ebcd8144429d00','176c6deaa855f5e30163138534272a92e0900e6d839032b4eb5573e22dfe3cb4','1a6336abe416678dd04c4ec0587a41d79e7ac01ea87ce729a9317525c6c43317','739961b9ea47a288a2b8e0aa2f8290eac430079d03481d0d738515eef940fea0']
pins = {'SharingSeed19Degree44':'8067529394f2cd59712b1c53234c8de518cb9387b3ee3b554b3e87b84e50e1c4',
        'Sign32GenericRemoveInput':'0ab66daaacfbfa8f1d32649124c8eb12ca03e5b7881ca0134041e90152532e3b',
        'CurrentKernelData2011':'95901a4dd31bf84f725829e3903c16dc57f7ad118aa9d201046293ca17047896',**dict(zip(names,objects))}
guards = 0
for row,entry,name,obj in zip(state['rows'],manifest,names,objects):
    assert row['module'] == name and entry['module'] == 'DiophantineConsistency.'+name
    source = packet/'src/DiophantineConsistency'/(name+'.lean')
    assert digest(source) == row['source_sha256'] == entry['source_sha256'] == digest(output/'src/DiophantineConsistency'/(name+'.lean'))
    assert digest(output/'lib/DiophantineConsistency'/(name+'.olean')) == row['object_sha256'] == obj
    for phase in ('deps','compile'):
        stage = row[phase]
        assert stage['exit'] == 0 and stage['stop_reason'] is None and not stage['monitor_errors'] and not stage['observed_descendant_pids']
        log = name+'-'+phase+'.txt'
        assert digest(attempt/log) == digest(output/log) == stage['log_sha256'] == outer['logs'][log]
    for path, observation in row['direct_guard'].items():
        candidate = Path(path)
        if observation is None: assert not os.path.lexists(candidate)
        else: assert candidate.is_file() and str(candidate.resolve()) == observation['realpath'] and digest(candidate) == observation['sha256']
        guards += 1
    for mod in entry['imports']:
        dep = row['dependencies'][mod]
        assert dep['sha256'] == pins[mod.split('.')[-1]] and row['direct_guard'][dep['path']] == {'sha256':dep['sha256'],'realpath':dep['realpath']}
    log = ' '.join((attempt/(name+'-compile.txt')).read_text().split())
    assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
    if name.endswith('Eval'):
        ns = 'Sign19AbstractExpression' if name == names[1] else 'Sign19CurrentExpression'
        assert "'DiophantineConsistency."+ns+".eval_expression' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
    else: assert not log
for path,target in state['overlay_links'].items(): assert Path(path).is_symlink() and str(Path(path).resolve()) == target
upstream = root/'reviews/nine-sharing-sign19-staged-syntax-terminal-independent/check.py'
subprocess.run([sys.executable,'-I','-S','-B',str(upstream)],check=True,capture_output=True,timeout=120)
for survey in ('partial-survey.py','seed-data-survey.py'):
    subprocess.run([sys.executable,'-I','-S','-B',str(packet/survey)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':42785,'stages':4,'guards':guards,
                  'overlay_links':len(state['overlay_links']),'state_sha256':digest(state_path),
                  'scope':'Fin19 input-one evaluation; partial upstream producer observations retained'},sort_keys=True,indent=2))
