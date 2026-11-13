#!/usr/bin/env python3
"""Read-only snapshot checks and synthetic regressions; never starts Lean."""
import copy
import hashlib
import importlib.util
import inspect
import json
from pathlib import Path
import sys
from unittest import mock

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('run with python3 -I -S -B')
ROOT = Path(__file__).resolve().parents[2]
WORK = Path(__file__).resolve().parent/'snapshot'
pins={
 'launch.py':'3d8439244cb947e870211925d32184977d8cd2facb37098d84a5897a89439954',
 'worker.py':'81a1b0c6e01af561b8968c53d7a91907c871c1313d39503259db9907acc88103',
 'supervision.py':'f36f3893256106258a4b9ddcef89ba5334741f758e997f946d4cb183ff45daf1',
 'traversal_core.py':'27983ebed1529f21bb982ee7af1535c77383fee5ea76f86115004272e3df53a2',
 'test_core.py':'85c24d451d5afbce43ed6230127b192aa8e55f0e7297f1b1e3bfd45bf42ee961',
 'test_preflight.py':'851239376d5b9f14ba3aaf966d774d5768150d01059289976270e7ca67d96b83',
 'test_supervision.py':'edde533b86a51c558a13b07297973de824d9fe50e6dc9f4183cba00af45fe448',
 'core-controls.json':'e15983e6127f1cac13ddb76d4bc6d5ff5b97a375e84b2c0214ebfe4c4e48e750',
 'preflight-controls.json':'7d66412e043512e36ac44396d7eb9240a2cd27f69271dd5542b1e26979f63605',
 'supervision-controls.json':'c44fbcde3487831e0fa5f005fd496b5dfa93220898d10ea79f2cbb02997b22b5',
 'README.md':'4e5708172921598b14ec47b88e8d5231de54b6a940e12d04866b3c7f1422fed0',
}
for name,expected in pins.items():
    if hashlib.sha256((WORK/name).read_bytes()).hexdigest()!=expected:
        raise RuntimeError('reviewed packet drift: '+name)
def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module
core=load('audit_core',WORK/'traversal_core.py')
supervision=load('audit_supervision',WORK/'supervision.py')
worker=load('audit_worker',WORK/'worker.py')

# This hashes the six declared pins and every pinned project source.  It does
# not invoke the worker's main(), instantiate BoundedReader, or launch Lean.
survey=worker.check_inputs()
prior=json.loads(worker.baseline.read_text())
seeds=sorted(survey['declared_external'])
state=core.restore(prior,seeds)
assert len(survey['project_sources'])==1212 and len(seeds)==len(set(seeds))==128
assert len(prior['modules'])==64 and len(prior['frontier'])==199
assert len(state['queue'])==287
assert all(seed in state['seen'] or seed in state['queued'] for seed in seeds)

def rec(*deps):
    return {'imports':sorted(set(deps)),'headers':{'.olean':{'imports':list(deps)}}}
baseline={'status':'PARTIAL_COMPILED_HEADERS','seeds':['A','B'],
          'modules':{'A':rec('C'),'B':rec('D')},'frontier':['C','D']}
declared=['A','X']
s=core.restore(baseline,declared);core.append(s,'C',rec('E'))
parent={'declared_seeds':declared,'modules':copy.deepcopy(s['modules']),
        'processed':list(s['processed']),'frontier':list(s['queue'])}
assert core.restore(baseline,declared,parent)['processed']==['C']
# A separately self-consistent child can rewrite a nonbaseline processed row
# and still pass restore. This is a synthetic integrity test, not a claim
# that the trusted worker normally creates such a checkpoint.
changed=core.restore(baseline,declared);core.append(changed,'C',rec('F'))
core.append(changed,'D',rec())
child={'declared_seeds':declared,'modules':copy.deepcopy(changed['modules']),
       'processed':list(changed['processed']),'frontier':list(changed['queue'])}
assert parent['modules']['C']!=child['modules']['C']
assert core.restore(baseline,declared,child)['processed']==['C','D']

# No real processes or signals: demonstrate that an unexpected kill error
# propagates from drain before it attempts the other synthetic session member.
members=[{'pid':900001,'state':'S','rss':1},{'pid':900002,'state':'S','rss':1}]
leader=type('Leader',(),{'pid':900000,'poll':lambda self:None})()
with mock.patch.object(supervision,'group_members',return_value=members), \
     mock.patch.object(supervision.os,'kill',side_effect=PermissionError('injected')) as kill:
    try: supervision.drain(900000,leader)
    except PermissionError: escaped=True
    else: escaped=False
assert escaped and kill.call_count==1

# Static control: the worker is independently executable and its main body
# neither reads nor validates the launcher's review gate before constructing
# BoundedReader. No standalone worker is launched by this check.
source=inspect.getsource(worker.main)
assert "if __name__=='__main__':main()" in (WORK/'worker.py').read_text()
assert 'BoundedReader(env)' in source and 'review_gate' not in source and 'review-gate.json' not in source
print(json.dumps({'status':'REVIEW_FINDINGS_REPRODUCED',
  'pinned_project_sources':len(survey['project_sources']),'declared_seeds':len(seeds),
  'baseline_modules':len(prior['modules']),'baseline_frontier':len(prior['frontier']),
  'initial_frontier':len(state['queue']),'self_consistent_rewritten_prefix_accepted':True,
  'injected_kill_error_escapes_drain':escaped,'direct_worker_gate_check_absent':True,
  'scope':'Read-only input hashes, queue replay, mocked and in-memory regressions; no Lean, traversal or approval receipt.'},sort_keys=True))
