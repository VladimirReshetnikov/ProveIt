#!/usr/bin/env python3
"""Exhaustive seven-leaf structured scanners, with exact unary graph proof.

Four decrements of H, one halt, one backward continue, one forward break.
Controls do not cross the scanner boundary. No finite natural-number test
is used as the acceptance criterion: its 4-phase decrement graph is exact.
"""
from functools import cache
from itertools import permutations
from pathlib import Path
import importlib.util, json, argparse
ap=argparse.ArgumentParser();ap.add_argument('--decrements',type=int,default=4);args=ap.parse_args()
nd=args.decrements;nleaf=nd+3

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
sp=importlib.util.spec_from_file_location('source_language',ROOT/'code/source_language.py')
s=importlib.util.module_from_spec(sp);sp.loader.exec_module(s)
oldrows=json.loads((ROOT/'machine/sites215.json').read_text())
old=s.tree(oldrows)
tail=s.subtree(old,'11111')

def ns(t):
    r=set()
    def go(q):
        if q in r:return
        r.add(q)
        if not s.leaf(q):go(q[0]);go(q[1])
    go(t);return r

@cache
def shapes(n):
    if n==1:return (None,)
    return tuple((a,b) for k in range(1,n) for a in shapes(k) for b in shapes(n-k))

def paths(t,p=''):
    return [p] if t is None else paths(t[0],p+'0')+paths(t[1],p+'1')

def construct(t,ops,c):
    if t is None:
        i=c[0];c[0]+=1;return ops[i]
    return construct(t[0],ops,c),construct(t[1],ops,c)

count=0; closed=0; hits=[]; best=999
for shape in shapes(nleaf):
    pp=paths(shape)
    intervals={}
    for i,p in enumerate(pp):
        for k in range(len(p)+1):
            q=p[:k]
            if q not in intervals:intervals[q]=[i,i+1]
            else:intervals[q][1]=i+1
    zero=[]; cc=[]; cb=[]
    for p in pp:
        zz=[k for k,x in enumerate(p) if x=='0'];oo=[k for k,x in enumerate(p) if x=='1']
        zero.append(intervals[p[:zz[-1]]][1] if zz else None)
        cb.append([intervals[p[:k]][1] for k in reversed(zz)])
        cc.append([intervals[p[:k]][0] for k in reversed(oo)])
    for halt,back,forward in permutations(range(nleaf),3):
        dd=set(range(nleaf))-{halt,back,forward}
        if any(zero[d] is None for d in dd):continue
        for bi,bt in enumerate(cc[back],1):
          for fi,ft in enumerate(cb[forward],1):
            count+=1
            def resolve(i):
                seen=set()
                while i not in dd and i not in (nleaf,halt):
                    if i in seen:return -2
                    seen.add(i)
                    i=bt if i==back else ft
                return i
            enter=resolve(0)
            if enter not in dd:continue
            z={d:resolve(zero[d]) for d in dd}
            pos={d:resolve(d+1) for d in dd}
            order=[];d=enter
            while d in dd and d not in order:
                order.append(d);d=pos[d]
            if d not in order:continue
            prefix=order.index(d);period=len(order)-prefix
            if period%4:continue
            if any(z[q] != (halt if k%4==1 else nleaf) for k,q in enumerate(order)):continue
            closed+=1
            ops=[('CD',5)]*nleaf;ops[halt]=('CH',None);ops[back]=('CC',bi);ops[forward]=('CB',fi)
            scan=construct(shape,ops,[0]);source=s.replace(old,'111',(scan,tail))
            cost=len(ns(source))
            rec={'dag_nodes':cost,'scanner':scan,'control_graph':{'decrement_order':order,'prefix':prefix,'period':period,'zero_targets':z,'positive_targets':pos},'metrics':s.metrics(source)}
            hits.append(rec)
            if cost<best:
                best=cost; print('new best',cost,scan,flush=True)
                (HERE/f'sites-atomhalt-{nd}dec-best.json').write_text(json.dumps(s.sites(source),separators=(',',':'))+'\n')
hits.sort(key=lambda a:a['dag_nodes'])
report={'domain':f'all full binary {nleaf}-leaf trees with {nd} CD5, CH, CCk, CBj; closed controls; exact modulo4 graph','specifications':count,'passing_exact_graphs':closed,'best_dag_nodes':best,'best':hits[:20]}
(HERE/f'mod4_search_{nd}dec_result.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='best'}),flush=True)
