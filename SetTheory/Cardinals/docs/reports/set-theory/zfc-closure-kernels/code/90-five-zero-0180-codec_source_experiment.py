#!/usr/bin/env python3
"""Alternative total formula codecs priced as exact register DAGs.

No generated register DAG is a certified binary machine.  The uniform-four
control reproduces the original 219-node source as an exact rooted DAG.
"""
from __future__ import annotations
import argparse, json
from functools import lru_cache
from pathlib import Path

HERE=Path(__file__).resolve().parent
DEFAULT=HERE/'inputs/original219.json'

def construct(raw, variant):
    old={int(k):tuple(map(tuple,v)) for k,v in raw['nodes'].items()}
    nodes={}; intern={}
    def pair(a,b):
        p=a,b
        if p not in intern:
            i=len(nodes); nodes[i]=p; intern[p]=i
        return ('N',intern[p])
    def seq(xs):
        e=xs[-1]
        for x in reversed(xs[:-1]):e=pair(x,e)
        return e
    def run(r,k):
        assert k>=1
        e=('I',r)
        for _ in range(k-1):e=pair(e,('I',r))
        return e
    def loop(r,body):return pair(('D',r),pair(body,('C',2)))
    @lru_cache(None)
    def rawclone(e):
        if e[0]!='N':return e
        return pair(*(rawclone(x) for x in old[e[1]]))
    unstack=rawclone(('N',160)); cantor=rawclone(('N',162))
    double_left=seq([loop(6,run(7,2)),loop(7,run(6,1))])
    @lru_cache(None)
    def cons(scale,tag=0,left_double=False,left_offset=0):
        parts=[unstack]
        if left_double:parts.append(double_left)
        if left_offset:parts.append(run(6,left_offset))
        parts += [cantor,loop(7,run(1,scale))]
        e=seq(parts)
        return pair(e,run(1,tag)) if tag else e
    if variant=='uniform4':
        ops={119:cons(4),181:cons(4,1),180:cons(4,2),182:cons(4,3)}
    elif variant=='prefix_2488':
        # This prefix tree has lengths (1,2,3,3): multipliers (2,4,8,8).
        ops={119:cons(2),181:cons(4,1),180:cons(8,3),182:cons(8,7)}
    elif variant=='prefix_2848':
        ops={119:cons(2),181:cons(8,1),180:cons(4,3),182:cons(8,5)}
    elif variant=='uniform4_swap':
        ops={119:cons(4),181:cons(4,1),180:cons(4,3),182:cons(4,2)}
    elif variant=='atom_parity3':
        ops={119:cons(3),181:cons(3,1,True),180:cons(3,2),182:cons(3,1,True,1)}
    else:raise ValueError(variant)
    @lru_cache(None)
    def clone(e):
        if e[0]!='N':return e
        if e[1] in ops:return ops[e[1]]
        return pair(*(clone(x) for x in old[e[1]]))
    root=clone(('N',raw['root']))
    seen=set(); leaves=[]
    def walk(e,p):
        if e[0]!='N':leaves.append((p,e));return
        seen.add(e[1])
        walk(nodes[e[1]][0],p+'0');walk(nodes[e[1]][1],p+'1')
    walk(root,'')
    retained={i:nodes[i] for i in sorted(seen)}
    return {'variant':variant,'root':root[1],'nodes':retained,
            'constructors':{str(k):v[1] for k,v in ops.items()},
            'metrics':{'register_dag_nodes':len(seen),'instruction_occurrences':len(leaves),
                       'max_depth':max(map(lambda x:len(x[0]),leaves)),
                       'max_zero_run':max(max(map(len,p.split('1'))) for p,e in leaves)}}

def main():
    p=argparse.ArgumentParser();p.add_argument('--source',type=Path,default=DEFAULT)
    p.add_argument('--output-dir',type=Path,default=HERE/'codec-source-results');a=p.parse_args()
    raw=json.loads(a.source.read_text());a.output_dir.mkdir(parents=True,exist_ok=True)
    results=[]
    for name in ['uniform4','uniform4_swap','prefix_2488','prefix_2848','atom_parity3']:
        r=construct(raw,name);results.append({'variant':name,**r['metrics']})
        (a.output_dir/(name+'.json')).write_text(json.dumps(r,indent=2)+'\n')
    assert results[0]['register_dag_nodes']==219
    (a.output_dir/'summary.json').write_text(json.dumps({'status':'EXPERIMENT',
       'scope':'Exact constructor replacement and rooted DAG pricing; no binary machine or logical calibration proof.',
       'results':results},indent=2)+'\n')
    print(json.dumps(results,indent=2))

if __name__=='__main__':main()
