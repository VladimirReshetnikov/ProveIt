#!/usr/bin/env python3
from pathlib import Path
import json,sys,os
HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'source/Computability/BusyBeaver/Research/ZFC'
sys.path.insert(0,str(BASE))
import recover_wade_dag as recover
import theory_backend_experiment as theory
nodes,names=recover.parse_dag(recover.git_bytes(None,'ZF/m254/coq/prog/Dag254.v').decode())
entry=json.load(open(HERE.parent/'source/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/27-variant-experiments-machine_search-grammar_search-decoder_entries.json'))
native={int(k):tuple(map(tuple,v)) for k,v in entry['nodes'].items()}
alignment=json.load(open(HERE/'protocol_alignment.json'))
def subtree(path):
    q=entry['root']
    for bit in path:
        e=native[q][int(bit)]
        if e[0]!='N':return None
        q=e[1]
    return q
selected=set(theory.MACROS)|{167,169,122,216,214,198,205,200,207,193,201}
mapping={}
def locate(q,path=''):
    if q in selected:
        aa=[x for x in alignment if x['source'].startswith(path)]
        prefix=os.path.commonprefix([x['target'] for x in aa])
        if subtree(prefix) is None:prefix=prefix[:-1]
        bb=[x for x in alignment if x['target'].startswith(prefix)]
        if len(aa)==len(bb):
            nq=subtree(prefix)
            if nq not in mapping:mapping[nq]=q
            assert mapping[nq]==q,(nq,mapping[nq],q)
    for bit,e in enumerate(nodes[q]):
        if e.startswith('ENode '):locate(int(e.split()[1]),path+str(bit))
locate(0)
def word(q):
    if q in mapping:return [theory.MACROS.get(mapping[q],names[mapping[q]])]
    out=[]
    for e in native[q]:
        out+=word(e[1]) if e[0]=='N' else [e]
    return out
print('MAP',mapping)
for q in [94,92,93,52,71,57,58,126,106,95,105,147]:print(q,word(q))
(HERE/'native_macro_map.json').write_text(json.dumps(mapping,indent=2)+'\n')
