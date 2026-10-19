#!/usr/bin/env python3
"""Apply the preserved source67 dictionary optimizer to a new exact-schema word.
This is a bounded re-association experiment, not a new binary simulation proof.
"""
from pathlib import Path
import sys,json,os,importlib,hashlib
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
BASE=ROOT/'context_folds/recovered/67/research'
LAYOUT=BASE/'agent_audit/layout_search'
os.environ['BEYOND252_EXPLORATORY']=str(BASE/'sources/beyond252/beyond252/exploratory')
sys.path[:0]=[str(LAYOUT),str(ROOT/'machine_encoding')]
import grammar_layout as g
best=json.loads((HERE/'permuted_rows/best.json').read_text())
def convert(e):
    xs=e.split();op=xs[0]
    return ('H',) if op=='EHalt' else ({'ENode':'N','EInc':'I','EDecnz':'D','EBreak':'B','EContinue':'C'}[op],int(xs[1]))
g.original={int(q):tuple(map(convert,edges)) for q,edges in best['nodes'].items()};g.original_root=0
import dictionary_milp as d
out=HERE/'permuted_rows_global';out.mkdir(exist_ok=True);d.HERE=out
result=d.run(maxlen=20,minfreq=2,seconds=90,maxzeros=7,maxdepth=0,prefer_old=True)
if 'nodes' not in result:raise RuntimeError('No integer solution was returned.')
new=result['nodes'];nr=result['root']
def canonical(tree):
    if tree[0]!='N':return tree
    a,b=tree[1:]
    if g.dt.closed(a) and g.dt.closed(b):
        def flat(e):
            if e[0]=='N' and g.dt.closed(e[1]) and g.dt.closed(e[2]):return flat(e[1])+flat(e[2])
            return (canonical(e),)
        return ('S',flat(tree))
    return ('A',canonical(a),canonical(b))
assert canonical(g.dt.unfold(new,nr))==canonical(g.dt.unfold(g.original,0))
import specialized_axiom_compiler as s
bd=out/'backend';bd.mkdir(exist_ok=True)
for name in ('TMBuilder.py','tm.py','tmdb.py','LICENSE.wade'):(bd/name).write_bytes(s.recover.git_bytes(None,'ZF/generator/'+name))
sys.path.insert(0,str(bd));backend=importlib.import_module('TMBuilder')
order=[nr]+sorted(set(new)-{nr});ids={q:i for i,q in enumerate(order)}
def edge(e):
    op=e[0]
    return 'EHalt' if op=='H' else f"{dict(N='ENode',I='EInc',D='EDecnz',B='EBreak',C='EContinue')[op]} {ids[e[1]] if op=='N' else e[1]}"
nn={ids[q]:tuple(map(edge,new[q])) for q in order};names={ids[q]:f'global_rowperm_{q}' for q in order};names[0]='main().0'
m=s.H.compile_dag(backend,nn,names);s.H.reextract(m,nn,names);data,labels,missing=s.common.normalize(m);(out/'candidate.tm').write_bytes(data)
summary=dict(source='logical_routes/permuted_rows/best.json',source_nodes=len(new),working_states=len({q for q,b in m.states}),closed_association_canonical_comparison=True,all_edges_reextracted=True,metrics=result['metrics'],solver_status=result['status'],solver_message=result['message'],seconds=result['seconds'],missing_totalized=missing,sha256=hashlib.sha256(data).hexdigest(),transition_rows=len(data.decode().splitlines())-1,status='Source and emitted-edge checks only; no whole-program binary endpoint.')
(out/'results.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
