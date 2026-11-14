#!/usr/bin/env python3
from pathlib import Path
import json, hashlib, sys
import compiler as c
import support as s
HERE=Path(__file__).resolve().parent
def tup(x): return tuple(map(tup,x)) if isinstance(x,list) else x
raw=s.read_table(HERE/'raw202.native.tm')
raw.update({(38,0):(0,True,11),(38,1):(1,True,122),(164,1):(1,True,114),
 (214,0):(0,True,312),(214,1):(1,True,30),(312,0):(0,True,188),
 (310,1):(1,True,331),(331,0):(0,True,63),(331,1):(1,False,73)})
ns={k:tup(v) for k,v in json.loads((HERE/'parent6.nodes.json').read_text()).items()}
ns['node163']=('node6','node54')
ns['node170']=(('node36',('node167','node145')),'node56')
ns['node171']=('node170',(('leaf','inc',5),('leaf','continueTo',3)))
c.raw_nodes=lambda: ns
grammar=c.read_grammar(HERE/'grammar.json')
sites,ins,contracts=c.source(grammar)
folds=json.loads((HERE/'parent6.folds.json').read_text())
child,aliases=s.apply_folds(raw,folds)
print('raw,child,sites,contracts',len(raw)//2,len(child)//2,len(sites),len(contracts),flush=True)
print('folds',s.check_local_folds(raw,child,aliases,folds)['cases'].__len__(),flush=True)
incoming={}
for (q,b),(w,d,t) in raw.items(): incoming.setdefault(t,set()).add((w,d))
shape={q for q,b in raw if incoming.get(q) in ({(0,True)},{(1,True)})}
ops=c.opportunities_fast(raw,shape)
ops=[x for x in ops if incoming[x[0]]=={(0,True)} and incoming[x[1]]=={(1,True)}]
print('opportunities',len(ops),flush=True)
print(ops,flush=True)
print('matching',c.max_matching(ops),flush=True)
if '--verify' in sys.argv:
 print('validation',c.validate(child,contracts),flush=True)
 print('startup',s.startup(child,sites[25][0])['steps'],flush=True)
out=HERE/'combined'
out.mkdir(exist_ok=True)
(out/'machine195.native.tm').write_text(s.table_text(child))
(out/'nodes.json').write_text(json.dumps(ns))
(out/'instructions.json').write_text(json.dumps(ins))
(out/'opportunities.json').write_text(json.dumps(ops))
