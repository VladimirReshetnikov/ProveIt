#!/usr/bin/env python3
"""Pure synthetic queue/reachability mutation controls; no Lean processes."""
import copy
import importlib.util
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B without optimization')
here=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('resume_core',here/'traversal_core.py')
core=importlib.util.module_from_spec(spec);spec.loader.exec_module(core)
def record(*deps):return {'imports':sorted(set(deps)),'headers':{'.olean':{'imports':list(deps)}}}
def require(ok,msg):
    if not ok:raise RuntimeError(msg)
def rejected(f):
    try:f()
    except (ValueError,KeyError):return True
    return False
prior={'status':'PARTIAL_COMPILED_HEADERS','seeds':['A','B'],
       'modules':{'A':record('C'),'B':record('D')},'frontier':['C','D']}
state=core.restore(prior,['A','X'])
require(list(state['queue'])==['C','D','X'],'seed append')
core.append(state,'C',record('E'))
checkpoint={'declared_seeds':['A','X'],'modules':state['modules'],'processed':state['processed'],
            'frontier':list(state['queue'])}
resumed=core.restore(prior,['A','X'],checkpoint)
require(list(resumed['queue'])==['D','X','E'] and resumed['seen']=={'A','B','C'},'resume')
bad=copy.deepcopy(checkpoint);bad['frontier'].reverse()
require(rejected(lambda:core.restore(prior,['A','X'],bad)),'changed queue accepted')
bad=copy.deepcopy(checkpoint);bad['processed']=['D']
require(rejected(lambda:core.restore(prior,['A','X'],bad)),'changed order accepted')
bad=copy.deepcopy(checkpoint);bad['modules']['A']=record('Z')
require(rejected(lambda:core.restore(prior,['A','X'],bad)),'changed baseline accepted')
bad=copy.deepcopy(checkpoint);bad['modules']['C']['imports']=['Q']
require(rejected(lambda:core.restore(prior,['A','X'],bad)),'header/import mismatch accepted')
bad=copy.deepcopy(prior);bad['frontier']=['D','C']
require(rejected(lambda:core.restore(bad,['A','X'])),'changed original frontier accepted')
require(rejected(lambda:core.append(resumed,'X',record())),'non-head append accepted')
target=core.TARGETS[0]
reach=core.reachability({'A':record(target),target:record()},['A','B'])
require(reach['A']['known_paths'][target]==['A',target] and reach['A']['complete'],
        'positive target path')
require(not reach['B']['complete'] and reach['B']['unexpanded']==['B'],'unknown marked complete')
prior.update({'artifacts':{'base':'h0'},'namespace_observations':{'Base':'p0'},'root_observations':['root']})
p=core.restore(prior,['A','B']);core.append(p,'C',record('E'))
parent={'declared_seeds':['A','B'],'modules':copy.deepcopy(p['modules']),'processed':list(p['processed']),
        'new_processed':['C'],'frontier':list(p['queue']),'artifacts':{'base':'h0','C':'h1'},
        'namespace_observations':{'Base':'p0','C':'p1'},'root_observations':['root']}
q=core.restore(prior,['A','B'],parent);core.append(q,'D',record())
child={'declared_seeds':['A','B'],'modules':copy.deepcopy(q['modules']),'processed':list(q['processed']),
       'new_processed':['D'],'frontier':list(q['queue']),'artifacts':{'base':'h0','C':'h1','D':'h2'},
       'namespace_observations':{'Base':'p0','C':'p1','D':'p2'},'root_observations':['root']}
core.validate_chain(prior,['A','B'],[parent,child])
# Both replay individually, but the child rewrites its parent's nonbaseline C.
changed=copy.deepcopy(child);changed['modules']['C']=record('F');changed['frontier']=['F']
core.restore(prior,['A','B'],changed)
require(rejected(lambda:core.validate_chain(prior,['A','B'],[parent,changed])),'rewritten ancestor accepted')
for key in ('artifacts','namespace_observations'):
    changed=copy.deepcopy(child);changed[key]['C']='changed'
    require(rejected(lambda:core.validate_chain(prior,['A','B'],[parent,changed])),key+' rewrite accepted')
print(json.dumps({'status':'PASS_SYNTHETIC_CORE_CONTROLS','mutations_rejected':9,
 'scope':'Pure synthetic queue, seed and reachability controls; no Lean or provider traversal.'},sort_keys=True))
